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

(* An application of a continuation whose handler only applies another
   applies that other: a normalisation that refines.

   This file is to be reviewed: [forward_applications] and what it is
   made of, which are extracted and run by the validation of
   middle_end/flambda2/tests/semantics/, and the statement.

   Simplify does not go through a non-recursive continuation whose
   handler, once rebuilt, is a single [Apply_cont]:

   - it records the continuation as a shortcut to the one its handler
     applies (simplify/simplify_let_cont_expr.ml, where the handler of a
     non-recursive continuation is rebuilt: [Shortcut_to], unless the
     continuation is an exception handler, is inlined, or the
     [Apply_cont] has a trap action; then
     [Upwards_env.add_continuation_shortcut]), and every application of
     it is rebuilt as an application of that one, with the arguments of
     the application put for the parameters in the arguments of the
     handler (simplify/continuation_shortcut.ml, [apply]);
   - an arm of a [Switch] that is a goto, with no argument and no trap
     action, to a continuation of no parameters whose handler is known
     becomes the [Apply_cont] of the handler as it is, with its
     arguments and its trap action if it has one
     (simplify/simplify_switch_expr.ml, [rebuild_arm]).

   FlambdaShortcutSpec.shortcut_switches does this where the [Switch] is
   directly under the [Let_cont] and the continuation has no parameter.
   The front end leaves many more: the raise of a failed test, in every
   division and every checked access, is an arm to a continuation of no
   parameters bound some way above; the way out of a [try] is a
   continuation that passes its parameter on.

   [forward_applications] does it wherever the continuation is applied.
   Going down the term it keeps, for the non-recursive continuations in
   scope whose handler, once done itself, is one [Apply_cont], the
   parameters and that [Apply_cont] ([forwards]). An application of such
   a continuation becomes the [Apply_cont] of its handler with the
   arguments put for the parameters ([forwarded]): an [Apply_cont], if
   neither it nor that of the handler has a trap action
   ([forward_apply_cont]); an arm of a [Switch] in the same way, and a
   goto to a continuation of no parameters whatever the trap action of
   the handler ([forward_arm]). The [Let_cont] stays;
   FlambdaUnusedContsSpec.remove_unused_conts removes it if nothing
   names its continuation any more.

   What stops it ([forwarding]):
   - a continuation that the [Apply_cont] of the handler names, the one
     it applies or the one of its trap action, or a variable of its
     arguments that is not a parameter, is bound again somewhere in the
     body of the [Let_cont]: there it would not mean what it means in the
     handler. Names that the binders of a term do not reuse pass;
   - the [Apply_cont] of the handler names the continuation being bound,
     by applying it or in its trap action: in the handler that name is
     another continuation;
   - an exception handler, which a raise applies;
   - parameters that are not distinct;
   - an application that has not as many arguments as the continuation
     has parameters stays as it is;
   - recursive continuations are not forwarded, and an [Apply] that
     returns to a continuation still does: the call passes it as it is.
     Simplify renames such a continuation too where its handler passes
     its parameters on unchanged ([Continuation_shortcut.to_alias]);
     this pass does not;
   - the bodies of code are not gone into
     (FlambdaNormaliseSpec.rewrite_code takes the pass there).

   The result refines the term ([forward_applications_refines_statement]),
   under all environments. It is not an equivalence as it is stated: an
   application of the first term binds the parameters, so one with a
   parameter that the handler does not pass on is undefined where its
   argument has no value, and the second term does not look at that
   argument. So the pass is for the term before Simplify. The machine
   does not execute trap actions, so that a goto takes that of the
   handler is nothing to it.

   Nothing is asked of the names of the term beyond what the pass checks
   itself. [binds_cont] and FlambdaParamAliasesSpec.binds_var may say yes
   when the answer is no, never the reverse.

   Renaming: the functions here compare names by equality only and bind
   none, so the pass commutes with a renaming. That statement is owed to
   the nominal work and is not made here.

   The proofs are in FlambdaForwardProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaNormaliseSpec FlambdaParamAliasesSpec.
Import ListNotations.

(* ======================================================================== *)
(* Where an application goes                                                *)
(* ======================================================================== *)

(* Whether an expression may bind the continuation, by a [Let_cont]. *)
Fixpoint binds_cont (k : continuation) (e : expr) : bool :=
  match e with
  | Let _ _ _ body | Let_static _ body => binds_cont k body
  | Let_cont_non_recursive k' h body =>
    Pos.eqb k k' || binds_cont_in_handler k h || binds_cont k body
  | Let_cont_recursive handlers body =>
    existsb (fun '(k', h) => Pos.eqb k k' || binds_cont_in_handler k h)
      handlers
    || binds_cont k body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => false
  end
with binds_cont_in_handler (k : continuation) (h : continuation_handler)
    : bool :=
  match h with
  | Handler _ _ handler => binds_cont k handler
  end.

(* A [Simple] with the arguments put for the parameters. *)
Definition subst_simple (params : list variable) (args : list simple)
    (s : simple) : simple :=
  match s with
  | Var x =>
    match lookup x (combine params args) with
    | Some arg => arg
    | None => s
    end
  | Symbol _ | Const _ => s
  end.

(* The [Apply_cont] of a handler, for an application of its continuation
   to the arguments given. *)
Definition forwarded (params : list variable) (args : list simple)
    (target : apply_cont) : apply_cont :=
  Apply_cont_expr (ac_continuation target)
    (map (subst_simple params args) (ac_args target))
    (ac_trap_action target).

(* For the continuations in scope, the most recently bound first: the
   parameters and the [Apply_cont] of the handler, for one whose
   applications may go where its handler goes; [None] for another. *)
Definition forwards : Type :=
  list (continuation * option (list variable * apply_cont)).

Definition forward_of (F : forwards) (k : continuation)
    : option (list variable * apply_cont) :=
  match lookup k F with
  | Some entry => entry
  | None => None
  end.

(* An [Apply_cont] made to go where the handler of its continuation
   goes, if neither has a trap action. *)
Definition forward_apply_cont (F : forwards) (ac : apply_cont) : apply_cont :=
  match forward_of F (ac_continuation ac) with
  | Some (params, target) =>
    if
      Nat.eqb (length (ac_args ac)) (length params)
      && no_trap_action ac && no_trap_action target
    then forwarded params (ac_args ac) target
    else ac
  | None => ac
  end.

(* The same for an arm of a [Switch]; and a goto to a continuation of no
   parameters goes where the handler goes whatever the trap action of
   the handler. *)
Definition forward_arm (F : forwards) (ac : apply_cont) : apply_cont :=
  match forward_of F (ac_continuation ac), ac_args ac with
  | Some ([], target), [] =>
    if no_trap_action ac then forwarded [] [] target else ac
  | _, _ => forward_apply_cont F ac
  end.

(* Whether the applications of [k], whose handler has become [handler],
   may go where it goes: the parameters and the [Apply_cont] if so.
   [body] is the body of the [Let_cont] of [k]. *)
Definition forwarding (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler body : expr)
    : option (list variable * apply_cont) :=
  match handler with
  | Apply_cont target =>
    if
      hm_is_exn_handler metadata
      || among k (apply_cont_continuations target)
      || negb (distinct params)
      || existsb (fun j => binds_cont j body) (apply_cont_continuations target)
      || existsb
           (fun s =>
              match s with
              | Var x => negb (among x params) && binds_var x body
              | Symbol _ | Const _ => false
              end)
           (ac_args target)
    then None
    else Some (params, target)
  | Let _ _ _ _ | Let_static _ _ | Let_cont_non_recursive _ _ _
  | Let_cont_recursive _ _ | Apply _ | Switch _ _ | Invalid =>
    None
  end.

(* ======================================================================== *)
(* The pass                                                                 *)
(* ======================================================================== *)

Fixpoint forward_applications_under (F : forwards) (e : expr) : expr :=
  match e with
  | Let x kind d body => Let x kind d (forward_applications_under F body)
  | Let_static bindings body =>
    Let_static bindings (forward_applications_under F body)
  | Let_cont_non_recursive k (Handler params metadata handler) body =>
    let handler := forward_applications_under F handler in
    Let_cont_non_recursive k (Handler params metadata handler)
      (forward_applications_under
         ((k, forwarding k params metadata handler body) :: F) body)
  | Let_cont_recursive handlers body =>
    let F := map (fun '(k, _) => (k, None)) handlers ++ F in
    Let_cont_recursive
      (map (fun '(k, h) => (k, forward_applications_in_handler F h)) handlers)
      (forward_applications_under F body)
  | Apply _ | Invalid => e
  | Apply_cont ac => Apply_cont (forward_apply_cont F ac)
  | Switch scrutinee arms =>
    Switch scrutinee (map (fun arm => (fst arm, forward_arm F (snd arm))) arms)
  end
with forward_applications_in_handler (F : forwards)
    (h : continuation_handler) : continuation_handler :=
  match h with
  | Handler params metadata handler =>
    Handler params metadata (forward_applications_under F handler)
  end.

Definition forward_applications (e : expr) : expr :=
  forward_applications_under [] e.

Definition forward_applications_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (forward_applications e).
