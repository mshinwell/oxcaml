(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(* Where static bindings may be: the well-formedness of a compilation unit.

   This file is to be reviewed: [statics_at_toplevel] against the
   definition of toplevel in Simplify
   (simplify/simplify_let_cont_expr.ml, at_unit_toplevel, and
   Downwards_env.at_unit_toplevel), [well_formed_unit], and the two
   statements.

   Flambda permits a [Let_static] at the toplevel of a compilation unit
   only, so that it is executed once, before anything that follows it.
   Toplevel is:
   - the unit itself;
   - the body of a [Let], of a [Let_static] or of a [Let_cont] that is at
     toplevel;
   - the handler of a non-recursive continuation bound at toplevel, which
     is not an exception handler, when all its body can do is to apply
     that continuation or raise to the exception continuation of the
     unit: the handler then postdominates its body.
   Nothing else is: not the handler of a recursive continuation, which may
   run many times, and never the body of code, which runs once for each
   call.

   [statics_at_toplevel] is this as a check, carrying down the term
   whether it is at toplevel, as Simplify does. [well_formed_unit] asks
   also that no code id or symbol is bound twice.

   The semantics cannot see where a [Let_static] is, only what it does. So
   what it rules out is the harm of a binding in the wrong place: binding
   a name that is bound already is undefined
   (FlambdaSemanticsSpec.eval_static_bindings). It follows, for any term,
   that what a code id or a symbol is bound to never changes during a run
   ([step_extends_statics_statement], [run_extends_statics_statement]):
   this is what a rewrite needs, to rely in a handler on a binding made
   before the handler was defined.

   CR mshinwell: nothing here says that a well-formed unit never binds a
   name twice as it runs, which is the reason for the condition. It needs
   that a toplevel handler runs once at most.

   The model does not mark exception handlers, so [raises_to] finds them:
   a continuation is one when a call names it as its exception
   continuation.

   The proofs are in FlambdaWellFormedProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec.
Import ListNotations.

(* ======================================================================== *)
(* Where control may go                                                     *)
(* ======================================================================== *)

Definition among (name : positive) (names : list positive) : bool :=
  existsb (Pos.eqb name) names.

Definition all_among (names allowed : list positive) : bool :=
  forallb (fun name => among name allowed) names.

Definition without (bound names : list positive) : list positive :=
  filter (fun name => negb (among name bound)) names.

(* The continuations an expression may apply, or give to a call, that it
   does not bind itself. Code is closed, so bindings of code have none. *)
Fixpoint free_continuations (e : expr) : list continuation :=
  match e with
  | Let _ _ body | Let_static _ body => free_continuations body
  | Let_cont_non_recursive k h body =>
    handler_free_continuations h ++ without [k] (free_continuations body)
  | Let_cont_recursive handlers body =>
    without (map fst handlers)
      (flat_map (fun '(_, h) => handler_free_continuations h) handlers
       ++ free_continuations body)
  | Apply ap => [ap_continuation ap; ap_exn_continuation ap]
  | Apply_cont ac => [ac_continuation ac]
  | Switch _ arms => map (fun arm => ac_continuation (snd arm)) arms
  | Invalid => []
  end
with handler_free_continuations (h : continuation_handler)
    : list continuation :=
  match h with
  | Handler _ handler => free_continuations handler
  end.

(* Whether some call in the expression has [k] as its exception
   continuation. *)
Fixpoint raises_to (k : continuation) (e : expr) : bool :=
  match e with
  | Let _ _ body | Let_static _ body => raises_to k body
  | Let_cont_non_recursive _ h body =>
    handler_raises_to k h || raises_to k body
  | Let_cont_recursive handlers body =>
    existsb (fun '(_, h) => handler_raises_to k h) handlers
    || raises_to k body
  | Apply ap => Pos.eqb k (ap_exn_continuation ap)
  | Apply_cont _ | Switch _ _ | Invalid => false
  end
with handler_raises_to (k : continuation) (h : continuation_handler) : bool :=
  match h with
  | Handler _ handler => raises_to k handler
  end.

(* ======================================================================== *)
(* Static bindings are at toplevel                                          *)
(* ======================================================================== *)

(* Whether the handler of the non-recursive continuation [k], bound at
   toplevel around [body], is at toplevel too. *)
Definition handler_at_toplevel (unit_exn k : continuation) (body : expr)
    : bool :=
  negb (raises_to k body)
  && all_among (free_continuations body) [k; unit_exn].

(* Every [Let_static] of the expression is at toplevel, given whether the
   expression itself is ([toplevel]) and the exception continuation of the
   unit. *)
Fixpoint statics_at_toplevel (unit_exn : continuation) (toplevel : bool)
    (e : expr) : bool :=
  match e with
  | Let _ _ body => statics_at_toplevel unit_exn toplevel body
  | Let_static bindings body =>
    toplevel
    && forallb (binding_statics_at_toplevel unit_exn) bindings
    && statics_at_toplevel unit_exn toplevel body
  | Let_cont_non_recursive k h body =>
    handler_statics_at_toplevel unit_exn
      (toplevel && handler_at_toplevel unit_exn k body) h
    && statics_at_toplevel unit_exn toplevel body
  | Let_cont_recursive handlers body =>
    forallb (fun '(_, h) => handler_statics_at_toplevel unit_exn false h)
      handlers
    && statics_at_toplevel unit_exn toplevel body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => true
  end
with handler_statics_at_toplevel (unit_exn : continuation) (toplevel : bool)
    (h : continuation_handler) : bool :=
  match h with
  | Handler _ handler => statics_at_toplevel unit_exn toplevel handler
  end
with binding_statics_at_toplevel (unit_exn : continuation)
    (binding : static_binding) : bool :=
  match binding with
  | Bind_code _ c => code_statics_at_toplevel unit_exn c
  | Bind_deleted_code _ | Bind_symbol _ _ => true
  end
with code_statics_at_toplevel (unit_exn : continuation) (c : code) : bool :=
  match c with
  | Code _ _ _ _ body => statics_at_toplevel unit_exn false body
  end.

(* ======================================================================== *)
(* Static names are bound once                                              *)
(* ======================================================================== *)

Definition code_ids_of_binding (binding : static_binding) : list code_id :=
  match binding with
  | Bind_code id _ => [id]
  | Bind_deleted_code _ | Bind_symbol _ _ => []
  end.

Definition symbols_of_binding (binding : static_binding) : list symbol :=
  match binding with
  | Bind_symbol s _ => [s]
  | Bind_code _ _ | Bind_deleted_code _ => []
  end.

(* The names the [Let_static]s of an expression bind, by [names_of] for
   one binding. Deleted code is not bound, as in the semantics. Code is
   not looked into: in a well-formed unit it binds nothing. *)
Fixpoint static_names (names_of : static_binding -> list positive)
    (e : expr) : list positive :=
  match e with
  | Let _ _ body => static_names names_of body
  | Let_static bindings body =>
    flat_map names_of bindings ++ static_names names_of body
  | Let_cont_non_recursive _ h body =>
    handler_static_names names_of h ++ static_names names_of body
  | Let_cont_recursive handlers body =>
    flat_map (fun '(_, h) => handler_static_names names_of h) handlers
    ++ static_names names_of body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => []
  end
with handler_static_names (names_of : static_binding -> list positive)
    (h : continuation_handler) : list positive :=
  match h with
  | Handler _ handler => static_names names_of handler
  end.

Fixpoint distinct (names : list positive) : bool :=
  match names with
  | [] => true
  | name :: names => negb (among name names) && distinct names
  end.

(* ======================================================================== *)
(* Well-formed units                                                        *)
(* ======================================================================== *)

(* A unit, with its exception continuation: its static bindings are at
   toplevel, and bind each code id and each symbol once. *)
Definition well_formed_unit (unit_exn : continuation) (e : expr) : bool :=
  statics_at_toplevel unit_exn true e
  && distinct (static_names code_ids_of_binding e)
  && distinct (static_names symbols_of_binding e).

(* ======================================================================== *)
(* What is bound stays bound                                                *)
(* ======================================================================== *)

(* Everything the first static environment binds, the second binds to the
   same thing. *)
Definition statics_extend (statics statics' : static_env) : Prop :=
  (∀ (id : code_id) (c : code),
    lookup id (static_code statics) = Some c ->
    lookup id (static_code statics') = Some c)
  ∧ (∀ (s : symbol) (allocated : statically_allocated_value),
      lookup s (static_values statics) = Some allocated ->
      lookup s (static_values statics') = Some allocated).

Definition statics_of (s : state) : static_env :=
  match s with
  | State _ _ _ statics => statics
  end.

Definition step_extends_statics_statement : Prop :=
  ∀ s s' : state,
    step s = Step s' -> statics_extend (statics_of s) (statics_of s').

Definition run_extends_statics_statement : Prop :=
  ∀ (n : nat) (s s' : state),
    run n s = Step s' -> statics_extend (statics_of s) (statics_of s').
