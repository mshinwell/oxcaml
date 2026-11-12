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

(* A [Switch] whose arms all apply one continuation, to arguments that
   are computed from the number of the arm: a normalisation that
   refines.

   This file is to be reviewed: [merge_switches] and what it is made
   of, and the statements. The rewrite is one of the normalisations
   of the term before Simplify that the validation of
   middle_end/flambda2/tests/semantics/ applies: in a round of each of
   its two phases it follows [collapse_switches]
   (FlambdaValidateSpec.normalise_expr_before and
   [normalise_expr_params]). It is extracted and run with them.

   What Simplify does. Where the arms of a [Switch] all apply the same
   continuation with no trap action, and each argument is either the
   same in every arm or a constant that is computed from the number of
   the arm, Simplify makes of the [Switch] one application of the
   continuation, under the [Let]s of the primitives that compute those
   arguments from the scrutinee ([rebuild_switch] of
   middle_end/flambda2/simplify/simplify_switch_expr.ml). So
   [switch i with 0 -> k x 0t | 1 -> k x 1t], where [0t] is the tagged
   immediate, becomes [let tagged = Tag_immediate i in k x tagged].
   The model of that function, with what it is given and what is
   stated of it, is ../types/rocq/FlambdaSimplifySwitchMergeSpec.v.

   [merge_switches] does as much to the term before, for two of the
   ways in which Simplify computes an argument:
   - the argument is, in every arm, the number of the arm as a tagged
     immediate: the scrutinee is tagged ([By_tagging]);
   - the argument is the tagged immediate 1 in the arm of 0 and the
     tagged immediate 0 in the arm of 1, and there is no other arm:
     the scrutinee is tagged and the result negated
     ([By_tagging_and_negating]).
   The arguments that differ from arm to arm are all computed in the
   same one of these two ways. An argument that is a multiple of the
   number of the arm plus an offset, and the scrutinee passed as it
   is, which Simplify also merges, are not here.

   How it decides ([merge_switch]). The scrutinee must be a variable
   and there must be two arms or more. The application that the
   [Switch] may become applies the continuation of the first arm, with
   no trap action; its arguments are those of the first arm where the
   second arm has the same, and the variable of the scrutinee where it
   has not ([merged_arguments]), and the variable must be among them.
   Every arm must then be that application with a constant in place of
   the variable ([arm_is_merged]): the constant that is computed from
   the number of the arm ([constant_of_arm]). Where that is so of all
   the arms the [Switch] becomes the application, under a [Let] of the
   variable as itself tagged, and for the second way under a second
   [Let] of the variable as that negated ([bind_tagged],
   [bind_negated]).
   Otherwise the [Switch] is left as it is.

   The variable of the scrutinee is bound again, where Simplify binds
   a new variable. So the rewrite makes no name, and needs none to be
   given; the comparison of the validation is up to bound names
   (FlambdaCompareSpec.v). The arguments that are the same in every
   arm are not captured by the new [Let]s: in the merged arguments the
   variable of the scrutinee marks the arguments that are computed, so
   an argument that is that variable in the arms is read as one of
   them, and then no arm is the application with a constant in its
   place: nothing is merged. Nothing is assumed of the numbers of the
   arms: for the first way they are tested to be immediates
   ([in_range]), as [Tag_immediate] has no value on a number that is
   not one and the machine does not ask it of the scrutinee of a
   [Switch]; for the second they are 0 or 1.

   [merge_switches] goes where
   FlambdaNormaliseSpec.collapse_switches goes: into the bodies of
   [Let]s, of static bindings and of the bindings of continuations,
   and into the handlers of non-recursive continuations. It leaves
   the handlers of recursive continuations and the bodies of code as
   they are: a round of the validation takes it there as it takes
   the other rewrites of the round, with
   FlambdaRecHandlersSpec.rewrite_rec_handlers and
   FlambdaNormaliseSpec.rewrite_code. A [Switch] whose arms are all the
   same is left to [collapse_switches].

   The result refines the term ([merge_switches_refines_statement]).
   Where the scrutinee is the number of an arm, the [Switch] goes to
   that arm, and the merged term binds the variable to the constant
   of that arm and applies the continuation to the same values. It is
   not an equivalence: the [Switch] is undefined where the scrutinee
   is not the number of an arm, and the merged term is not.

   The rewrite commutes with renaming
   ([merge_switches_equivariant_statement]): it makes no name, and it
   looks at names only to compare them, which a renaming, being
   injective, keeps true or false. That it keeps scope, which is that
   a variable or a continuation that is free in the result is free in
   the term, is stated with the same of the other rewrites of a round
   (FlambdaKeepsScopeSpec.merge_switches_keeps_scope_statement).

   Two terms as checks of the definitions
   ([merge_switches_tagging_example_statement],
   [merge_switches_negating_example_statement]).

   The proofs are in FlambdaMergeSwitchesProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaPrimitiveModel FlambdaPrimitiveSpec FlambdaSemanticsSpec
  FlambdaNominalSpec FlambdaNormaliseSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The arguments that are computed from the number of the arm               *)
(* ======================================================================== *)

(* How the arguments that differ from arm to arm are computed from the
   scrutinee. *)
Inductive merge_by : Type :=
  | By_tagging
  | By_tagging_and_negating.

(* The constant that such an argument is in the arm of number [i], if
   the number is one that the primitives have a value on. *)
Definition constant_of_arm (how : merge_by) (i : Z) : option const :=
  match how with
  | By_tagging =>
    if in_range (int_width Standard_naked_immediate) i
    then Some (Tagged_immediate i)
    else None
  | By_tagging_and_negating =>
    if i =? 0 then Some (Tagged_immediate 1)
    else if i =? 1 then Some (Tagged_immediate 0)
    else None
  end.

(* ======================================================================== *)
(* The application that the arms are merged into                            *)
(* ======================================================================== *)

(* The arguments of two arms, merged: an argument that is the same in
   the two stays, and one that is not becomes the variable. Where one
   arm has more arguments than the other, those are left out, and no
   arm will be found to be the application ([arm_is_merged]). *)
Fixpoint merged_arguments (v : variable) (args args' : list simple)
    : list simple :=
  match args, args' with
  | s :: args, s' :: args' =>
    (if simple_eq_dec s s' then s else Var v)
    :: merged_arguments v args args'
  | _, _ => []
  end.

(* A constant in place of a variable. *)
Definition constant_for (v : variable) (c : const) (s : simple) : simple :=
  match s with
  | Var x => if Pos.eqb x v then Const c else s
  | Symbol _ | Const _ => s
  end.

(* An arm is the merged application with the constant of its number in
   place of the variable. *)
Definition arm_is_merged (how : merge_by) (v : variable) (merged : apply_cont)
    (arm : Z * apply_cont) : bool :=
  match constant_of_arm how (fst arm) with
  | Some c =>
    if apply_cont_eq_dec (snd arm)
         (Apply_cont_expr (ac_continuation merged)
            (map (constant_for v c) (ac_args merged))
            (ac_trap_action merged))
    then true
    else false
  | None => false
  end.

(* The variable bound again: to itself tagged, where it holds a naked
   immediate, and to itself negated, where it holds a tagged boolean. *)
Definition bind_tagged (v : variable) (body : expr) : expr :=
  Let v Value (Prim (Unary Tag_immediate) [Var v]) body.

Definition bind_negated (v : variable) (body : expr) : expr :=
  Let v Value (Prim (Unary Boolean_not) [Var v]) body.

(* ======================================================================== *)
(* The rewrite                                                              *)
(* ======================================================================== *)

Definition merge_switch (scrutinee : simple) (arms : list (Z * apply_cont))
    : expr :=
  match scrutinee, arms with
  | Var v, (_, ac) :: (_, ac') :: _ =>
    let merged :=
      Apply_cont_expr (ac_continuation ac)
        (merged_arguments v (ac_args ac) (ac_args ac')) None
    in
    if var_in_simples v (ac_args merged)
    then
      if forallb (arm_is_merged By_tagging v merged) arms
      then bind_tagged v (Apply_cont merged)
      else if forallb (arm_is_merged By_tagging_and_negating v merged) arms
      then bind_tagged v (bind_negated v (Apply_cont merged))
      else Switch scrutinee arms
    else Switch scrutinee arms
  | _, _ => Switch scrutinee arms
  end.

Fixpoint merge_switches (e : expr) : expr :=
  match e with
  | Let x kind d body => Let x kind d (merge_switches body)
  | Let_static bindings body => Let_static bindings (merge_switches body)
  | Let_cont_non_recursive k (Handler params metadata handler) body =>
    Let_cont_non_recursive k
      (Handler params metadata (merge_switches handler))
      (merge_switches body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (merge_switches body)
  | Switch scrutinee arms => merge_switch scrutinee arms
  | Apply _ | Apply_cont _ | Invalid => e
  end.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

Definition merge_switches_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (merge_switches e).

Definition merge_switches_equivariant_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    merge_switches (rename_expr r e) = rename_expr r (merge_switches e).

(* ======================================================================== *)
(* Two terms                                                                *)
(* ======================================================================== *)

Module Merge_examples.

Definition i : variable := 1%positive.
Definition x : variable := 2%positive.
Definition k : continuation := 1%positive.

Definition apply_k (s : simple) : apply_cont :=
  Apply_cont_expr k [Var x; s] None.

Definition constant (n : Z) : simple := Const (Tagged_immediate n).

(* [switch i with 0 -> k x 0t | 1 -> k x 1t | 2 -> k x 2t] and
   [let i = Tag_immediate i in k x i]. *)
Definition switch_tagging : expr :=
  Switch (Var i)
    [(0, apply_k (constant 0)); (1, apply_k (constant 1));
     (2, apply_k (constant 2))].

Definition merged_tagging : expr :=
  bind_tagged i (Apply_cont (apply_k (Var i))).

(* [switch i with 0 -> k x 1t | 1 -> k x 0t] and
   [let i = Tag_immediate i in let i = Boolean_not i in k x i]. *)
Definition switch_negating : expr :=
  Switch (Var i) [(0, apply_k (constant 1)); (1, apply_k (constant 0))].

Definition merged_negating : expr :=
  bind_tagged i (bind_negated i (Apply_cont (apply_k (Var i)))).

End Merge_examples.

Definition merge_switches_tagging_example_statement : Prop :=
  merge_switches Merge_examples.switch_tagging
  = Merge_examples.merged_tagging.

Definition merge_switches_negating_example_statement : Prop :=
  merge_switches Merge_examples.switch_negating
  = Merge_examples.merged_negating.
