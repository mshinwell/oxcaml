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



(* In an arm of a [Switch] on a variable, an argument that is that
   variable is the number of the arm: a normalisation that is an
   equivalence.

   This file is to be reviewed: [numbers_in_arms] and what it is made
   of, which are extracted and run by the validation of
   middle_end/flambda2/tests/semantics/, and the two statements. The
   validation applies the pass to each of the two terms that it
   compares, once it has placed their continuations, just after
   FlambdaUnaliasParamsSpec.unalias_params
   (FlambdaValidateSpec.tidied_before, [tidied_after]).

   Simplify simplifies the arguments of an arm of a [Switch] in an
   environment in which the scrutinee is the number of the arm
   (simplify/simplify_switch_expr.ml: [simplify_switch] meets the type
   of the scrutinee with [T.this_naked_immediate arm] for each arm,
   and [simplify_arm] simplifies the arguments of the arm, and
   records the use of its continuation, under what the meet gives).
   An argument that is the scrutinee is then the constant; and the
   handler of a continuation that has that one use is simplified
   under the same knowledge. So for a flag that a loop tests before
   it sets it,

     for i = 0 to n do
       if not !seen then if p i then (seen := true; first := i)
     done

   the term after Simplify passes the constant [0] or [1] on where
   the term before passes the flag as it was read.

   [number_in_arms x] puts, for the variable [x] in the arguments of
   an application of a continuation, the naked immediate that [x] is
   known to be there. What is known ([known], a number or nothing)
   is found on the way down as FlambdaGiveScrutineeSpec.give_scrutinee
   finds it, by the functions of that file:
   - in an arm of a [Switch] on [x], [x] is the number of the arm
     ([arm_known]);
   - in the handler of a non-recursive continuation whose [Let_cont]
     has for its body a [Switch] on [x], or comes to one through
     non-recursive [Let_cont]s that do not bind the continuation
     again and whose handlers do not mention it, and that only arms
     of one number apply, [x] is that number ([arm_fact]);
   - what is known where a continuation is defined is known in its
     handler, which runs under the variables of its definition and
     its parameters;
   - nothing is known of [x] under a [Let] of [x] or in a handler
     that has [x] among its parameters ([known_under]).
   Only the arguments of applications of continuations are changed,
   those of the arms of a [Switch] among them: a primitive, a call
   and the scrutinee of a [Switch] keep the variable. The bindings of
   a [Let_static], and so the bodies of code, are left as they are.

   The rewrite is an equivalence whatever [x] is
   ([number_in_arms_equivalent_statement]): an argument is changed
   only where the variable holds the constant. The pass
   ([numbers_in_arms]) makes it for each variable that is the
   scrutinee of a [Switch] of the term, in the order in which the
   term has them ([scrutinees]; a variable that several have is
   taken once for each, and the rewrite changes nothing the second
   time). It goes into the handlers of recursive continuations; the
   bodies of code are not gone into: FlambdaNormaliseSpec.rewrite_code
   takes a pass there.

   It is the rewrite of FlambdaGiveScrutineeSpec.give_scrutinee the
   other way; the pass of that file keeps its rewrite only where
   FlambdaUnaliasParamsSpec.unalias_param would then take the
   parameter away. Applied to the result of that pass as it is, this
   one puts the numbers back. The validation applies that pass, then
   [unalias_params], which takes the parameter away and with it the
   arguments that were made the variable, and then this one: there
   it undoes nothing.

   The result is equivalent to the term
   ([numbers_in_arms_equivalent_statement]), under all environments.

   Renaming: the functions here compare names by equality only and
   make none.

   The proofs are in FlambdaArmNumbersProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaMapSpec FlambdaSemanticsSpec FlambdaUnaliasParamsSpec
  FlambdaGiveScrutineeSpec.
Import ListNotations.

(* ======================================================================== *)
(* The rewrite                                                              *)
(* ======================================================================== *)

(* The number [c] for the variable [x]. *)
Definition number_simple (x : variable) (c : Z) (s : simple) : simple :=
  match s with
  | Var y => if Pos.eqb y x then Const (Naked_immediate c) else s
  | _ => s
  end.

Definition number_in_apply_cont (x : variable) (known : option Z)
    (ac : apply_cont) : apply_cont :=
  match known with
  | Some c =>
    {| ac_continuation := ac_continuation ac;
       ac_args := map (number_simple x c) (ac_args ac);
       ac_trap_action := ac_trap_action ac |}
  | None => ac
  end.

Fixpoint number_in_arms (x : variable) (known : option Z) (e : expr)
    {struct e} : expr :=
  match e with
  | Let y kind d body =>
    Let y kind d
      (number_in_arms x (if Pos.eqb y x then None else known) body)
  | Let_static bindings body =>
    Let_static bindings (number_in_arms x known body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k
      (number_in_handler x
         match arm_fact x k body with
         | Some c => Some c
         | None => known
         end
         h)
      (number_in_arms x known body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive
      (map (fun '(k, h) => (k, number_in_handler x known h)) handlers)
      (number_in_arms x known body)
  | Apply_cont ac => Apply_cont (number_in_apply_cont x known ac)
  | Switch scrutinee arms =>
    Switch scrutinee
      (map
         (fun '(d, ac) =>
            (d, number_in_apply_cont x (arm_known x scrutinee d known) ac))
         arms)
  | Apply _ | Invalid => e
  end
with number_in_handler (x : variable) (known : option Z)
    (h : continuation_handler) {struct h} : continuation_handler :=
  match h with
  | Handler params metadata handler =>
    Handler params metadata
      (number_in_arms x (known_under x params known) handler)
  end.

(* The result behaves as the term does, under all environments,
   whatever the variable is. *)
Definition number_in_arms_equivalent_statement : Prop :=
  ∀ (x : variable) (e : expr), expr_equivalent e (number_in_arms x None e).

(* ======================================================================== *)
(* The pass                                                                 *)
(* ======================================================================== *)

(* The variables that are the scrutinee of a [Switch] of a term,
   outside code. *)
Fixpoint scrutinees (e : expr) {struct e} : list variable :=
  match e with
  | Let _ _ _ body => scrutinees body
  | Let_static _ body => scrutinees body
  | Let_cont_non_recursive _ h body =>
    handler_scrutinees h ++ scrutinees body
  | Let_cont_recursive handlers body =>
    flat_map (fun '(_, h) => handler_scrutinees h) handlers
    ++ scrutinees body
  | Switch (Var x) _ => [x]
  | Switch _ _ | Apply _ | Apply_cont _ | Invalid => []
  end
with handler_scrutinees (h : continuation_handler) {struct h}
    : list variable :=
  match h with
  | Handler _ _ handler => scrutinees handler
  end.

(* The pass: the rewrite for each of them in turn. *)
Definition numbers_in_arms (e : expr) : expr :=
  fold_left (fun e x => number_in_arms x None e) e (scrutinees e).

Definition numbers_in_arms_equivalent_statement : Prop :=
  ∀ e : expr, expr_equivalent e (numbers_in_arms e).
