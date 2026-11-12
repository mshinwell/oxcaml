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

(* Lifting out of the code of a function: a [Let], in the body of code,
   of a closure, an immutable block or a boxed number whose parts are
   symbols and constants, made a static binding of a symbol beside the
   code.

   This file is to be reviewed: [closed_named], [lifted_out],
   [lift_from_code] and [lifted_out_bindings], against what Simplify
   does (below); [lift_from_code_unit], which is extracted and run by
   the validation of middle_end/flambda2/tests/semantics/; and the
   statements.

   What Simplify does. The conditions under which it lifts a [Let] do
   not ask that the [Let] is at the toplevel of the unit
   (FlambdaLiftSpec.v has them): a set of closures each of whose value
   slots is a constant or a symbol, and a block or a boxed number whose
   type can be rebuilt as a static constant with symbols and constants
   for its parts, are lifted out of the body of a function too. The
   binding of the symbol is then placed at toplevel, around the code:
   a function that needs nothing from around it, given inside another
   function to a third (the function given to a map over a list), is
   the common case. FlambdaLiftSpec.lift_expr makes a [Let] a static
   binding where it stands, which cannot be done in code: the machine
   has no step for a call of code that binds something static.

   What is here. In the body of the code that the guess names,
   [lift_from_code] makes the [Let]s at the paths given aliases of
   symbols, and binds the symbols in the group of static bindings that
   binds the code, before the code:

     Let_static [...; Bind_code id (Code ... (Let x = d in body)); ...]
       becomes
     Let_static
       [...; bindings; Bind_code id (Code ... (Let x = Symbol s in body));
        ...]

   where FlambdaLiftSpec.lift_named gives [bindings] and [s] for [d],
   as for a [Let] lifted where it stands, and [d] mentions no variable
   ([closed_named]), so that the bindings mean the same at toplevel. As
   there, the variable stays, bound to the symbol, for other passes to
   follow and remove; a [Let] is named by its path in the body of its
   code; the handlers of recursive continuations are not gone into; and
   which [Let]s, to which symbols, is a guess of the caller's, of which
   nothing is believed.

   A [Let] whose parts are variables bound to symbols by an earlier
   lifting is closed once those aliases are followed: the validator
   makes several liftings in turn, each followed by its normalisation
   (FlambdaValidateSpec.lifted_in_turn).

   Why it is right. The first run makes a closure, a block or a boxed
   number each time the [Let] is executed; the second has the symbol,
   bound once, when the group of the code is, to the same thing: the
   parts are symbols and constants, which are the same values whenever
   they are evaluated. The two values are related by
   FlambdaLiftSpec.value_lifted, as for the lifting at toplevel, and no
   primitive and no rule of the machine tells them apart. They differ
   at an exit of the unit, so [lift_from_code_unit] makes the same
   check as FlambdaLiftSpec.lift_unit (FlambdaLiftSpec.exits_plain: the
   unit gives only symbols and constants to the continuations that it
   may leave through). It also checks that the result is a well-formed
   unit: the symbols given are then new and distinct, and the group of
   the code is executed once. With both, the unit lifted refines the
   unit, run on its own ([lift_from_code_unit_program_refines_statement]).

   The second run binds the symbol when the group of the code is
   bound, whether or not the code is ever called. That binding cannot
   itself be undefined under the checks: its fields or value slots are
   constants and symbols, which have values without the symbols being
   resolved (and for a closure of a set, FlambdaLiftSpec.lift_named
   gives bindings only at function slots that the set has); and the
   result being a well-formed unit, the symbol is not bound already and
   the group is not executed again. So code that is never called
   brings no undefinedness to the unit lifted. Where the code is called
   and its [Let] is undefined in the first run (a block one of whose
   fields is a symbol bound to nothing: decision D8), the refinement
   asks nothing more of the second run.

   What is not here: lifting out of the handler of a recursive
   continuation, in code or at toplevel; out of the arm of a test at
   toplevel; and the sharing of equal constants.

   The proofs are in FlambdaLiftFromCodeProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaNominalSpec FlambdaWellFormedSpec
  FlambdaUnusedStaticsSpec FlambdaLiftSpec.
Import ListNotations.

(* ======================================================================== *)
(* What is lifted out                                                       *)
(* ======================================================================== *)

(* A defining expression that makes something and mentions no variable:
   its arguments, or its value slots, are symbols and constants. *)
Definition closed_named (d : named) : bool :=
  match d with
  | Prim _ args => forallb plain_simple args
  | Set_of_closures _ value_slots
  | Closure_of_set _ _ value_slots =>
    forallb (fun slot => plain_simple (snd slot)) value_slots
  | Simple _ | Project_value_slot _ _ | Project_value_slot_from _ _ _
  | Project_function_slot _ _ _ =>
    false
  end.

(* What stands for the [Let] of [d] at [at_path], if it is lifted out:
   the static bindings, and the symbol. None if the guess has nothing
   for the path, if [d] mentions a variable, or if it is not something
   that is lifted to what the guess says. *)
Definition lifted_out (lets : list (path * lift_to)) (at_path : path)
    (d : named) : option (list static_binding * symbol) :=
  match lookup at_path lets with
  | Some target => if closed_named d then lift_named target d else None
  | None => None
  end.

(* The guess: for a code id, the [Let]s of the body of its code to lift
   out, by their paths in the body. *)
Definition lets_in_code : Type :=
  list (code_id * list (path * lift_to)).

Definition lets_of (K : lets_in_code) (id : code_id)
    : list (path * lift_to) :=
  match lookup id K with
  | Some lets => lets
  | None => []
  end.

(* The static bindings that stand for the [Let]s of an expression that
   are lifted out, in the order of FlambdaLiftSpec.lift_expr: the body
   of a [Let_cont] before its handler. *)
Fixpoint lifted_out_bindings (lets : list (path * lift_to)) (at_path : path)
    (e : expr) : list static_binding :=
  match e with
  | Let _ _ d body =>
    match lifted_out lets at_path d with
    | Some (bindings, _) => bindings
    | None => []
    end
    ++ lifted_out_bindings lets (xO at_path) body
  | Let_static _ body => lifted_out_bindings lets (xO at_path) body
  | Let_cont_non_recursive _ h body =>
    lifted_out_bindings lets (xO at_path) body
    ++ handler_lifted_out_bindings lets (xI at_path) h
  | Let_cont_recursive _ body => lifted_out_bindings lets (xO at_path) body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => []
  end
with handler_lifted_out_bindings (lets : list (path * lift_to))
    (at_path : path) (h : continuation_handler) : list static_binding :=
  match h with
  | Handler _ _ handler => lifted_out_bindings lets at_path handler
  end.

(* ======================================================================== *)
(* The rewrite                                                              *)
(* ======================================================================== *)

(* The expression with the [Let]s at the paths [lets] made aliases of
   the symbols that stand for them, and with every group of static
   bindings rewritten: the code that [K] names has the [Let]s that [K]
   gives for it made aliases, and the bindings that stand for them are
   put before it. [at_path] is the path of the expression. For a unit,
   [lets] is empty: only its code is rewritten. *)
Fixpoint lift_from_code (K : lets_in_code) (lets : list (path * lift_to))
    (at_path : path) (e : expr) : expr :=
  match e with
  | Let x kind d body =>
    let body := lift_from_code K lets (xO at_path) body in
    match lifted_out lets at_path d with
    | Some (_, s) => Let x kind (Simple (Symbol s)) body
    | None => Let x kind d body
    end
  | Let_static bindings body =>
    Let_static (flat_map (binding_lift_from_code K) bindings)
      (lift_from_code K lets (xO at_path) body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k (handler_lift_from_code K lets (xI at_path) h)
      (lift_from_code K lets (xO at_path) body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (lift_from_code K lets (xO at_path) body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end
with handler_lift_from_code (K : lets_in_code)
    (lets : list (path * lift_to)) (at_path : path)
    (h : continuation_handler) : continuation_handler :=
  match h with
  | Handler params metadata handler =>
    Handler params metadata (lift_from_code K lets at_path handler)
  end
with binding_lift_from_code (K : lets_in_code)
    (binding : static_binding) : list static_binding :=
  match binding with
  | Bind_code id (Code params my_closure ret exn metadata body) =>
    lifted_out_bindings (lets_of K id) root body
    ++ [Bind_code id
          (Code params my_closure ret exn metadata
             (lift_from_code K (lets_of K id) root body))]
  | Bind_deleted_code _ | Bind_symbol _ _ => [binding]
  end.

(* ======================================================================== *)
(* The check                                                                *)
(* ======================================================================== *)

(* The unit with the [Let]s of the guess lifted out of its code: if the
   unit exits with symbols and constants only, and the result is a
   well-formed unit. *)
Definition lift_from_code_unit (u : unit_interface) (K : lets_in_code)
    (e : expr) : option expr :=
  let lifted := lift_from_code K [] root e in
  if exits_plain [] e && well_formed_unit u lifted then Some lifted else None.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

(* What [lift_from_code_unit] gives refines the unit, run on its own. *)
Definition lift_from_code_unit_program_refines_statement : Prop :=
  ∀ (u : unit_interface) (K : lets_in_code) (e e' : expr),
    lift_from_code_unit u K e = Some e' -> program_refines e e'.

(* The rewrite commutes with renaming: a [Let] is named by where it is,
   and one that is lifted out mentions no variable. The renaming is of
   variables and continuations, in code too. *)
Definition lifted_out_bindings_equivariant_statement : Prop :=
  ∀ (r : renaming) (lets : list (path * lift_to)) (at_path : path)
    (e : expr),
    lifted_out_bindings lets at_path (rename_expr r e)
    = lifted_out_bindings lets at_path e.

Definition lift_from_code_equivariant_statement : Prop :=
  ∀ (r : renaming) (K : lets_in_code) (lets : list (path * lift_to))
    (at_path : path) (e : expr),
    rename_expr r (lift_from_code K lets at_path e)
    = lift_from_code K lets at_path (rename_expr r e).
