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

(* Proofs of the statements of FlambdaPortIntArithInvalidSpec.v. Nothing
   here needs review but that each theorem has the statement of its name.
   This file follows no file of the compiler.

   No [Axiom], no [Parameter], no [Admitted]. The contracts are
   hypotheses of a section. After the section they are premises of the
   theorem, as its statement has them: they are not theorems, and [Print
   Assumptions] does not list them. *)

From Stdlib Require Import ZArith Bool List Permutation.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaPrimitiveModel
  FlambdaPrimitiveSpec.
From OxCamlFlambda2Types Require Import FlambdaSimplifyArithSpec.
From SimplifyPort Require Import Port_monad Kit_laws.
Require SimplifyPort.Simplify_binary_primitive
  SimplifyPort.Simplify_primitive_result.
From SimplifyPort.decl Require Bound_var Debuginfo Downwards_acc
  Downwards_env Flambda Flambda2_types Flambda_kind Flambda_primitive
  Number_adjuncts Or_invalid Simple Simplified_named
  Simplify_primitive_result Target_system.
From SimplifyPortAgainstModel Require Import FlambdaPortIntArithTableSpec
  FlambdaPortIntArithTableProofs FlambdaPortIntArithInvalidSpec.
From SimplifyPortAgainstModel Require Simplify_binary_primitive_named_locals.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The tie                                                                  *)
(* ======================================================================== *)

(* Rocq computes: both sides unfold to one term. *)
Theorem simplify_is_its_named_locals : simplify_is_its_named_locals_statement.
Proof.
  intros op dacc original_term dbg arg1 arg1_ty arg2 arg2_ty result_var.
  reflexivity.
Qed.

(* ======================================================================== *)
(* A computation that, if it returns, returns a value with a property       *)
(* ======================================================================== *)

Lemma if_returns_ret {A : Type} (a : A) (Q : A -> Prop) :
  Q a -> if_returns (ret a) Q.
Proof. intros H n s. apply wp_ret. exact H. Qed.

(* A call of which nothing is known. *)
Lemma if_returns_any {A : Type} (m : M A) (Q : A -> Prop) :
  (forall a : A, Q a) -> if_returns m Q.
Proof.
  intros H n s. apply wp_any; [intros a s'; apply H | intros e s'; exact I].
Qed.

Lemma if_returns_bind {A B : Type} (m : M A) (k : A -> M B)
    (R : A -> Prop) (Q : B -> Prop) :
  if_returns m R ->
  (forall a : A, R a -> if_returns (k a) Q) ->
  if_returns (bind m k) Q.
Proof.
  intros Hm Hk n s. apply wp_bind.
  eapply wp_weaken; [exact (Hm n s) | | intros e s' H; exact H].
  intros a s' HR. exact (Hk a HR n s').
Qed.

(* After a call of which nothing is known. *)
Lemma if_returns_bind_any {A B : Type} (m : M A) (k : A -> M B)
    (Q : B -> Prop) :
  (forall a : A, if_returns (k a) Q) -> if_returns (bind m k) Q.
Proof.
  intro Hk. apply (if_returns_bind m k (fun _ => True)).
  - apply if_returns_any. intro a. exact I.
  - intros a _. exact (Hk a).
Qed.

Lemma if_returns_weaken {A : Type} (m : M A) (Q R : A -> Prop) :
  if_returns m Q -> (forall a : A, Q a -> R a) -> if_returns m R.
Proof.
  intros Hm HQR n s.
  eapply wp_weaken; [exact (Hm n s) | | intros e s' H; exact H].
  intros a s' HQ. exact (HQR a HQ).
Qed.

(* The form of the table's theorem gives this weaker form. *)
Lemma pure_if_returns_if_returns {A : Type} (m : M A) (Q : A -> Prop) :
  pure_if_returns m Q -> if_returns m Q.
Proof.
  intros Hm n s.
  eapply wp_weaken; [exact (Hm n s) | | intros e s' H; destruct H].
  intros a s' [HQ _]. exact HQ.
Qed.

(* ======================================================================== *)
(* The two facts about the form of the new contracts                        *)
(* ======================================================================== *)

Theorem fold_names_its_elements : fold_names_its_elements_statement.
Proof.
  intros elt set fold nums known Hfold.
  eapply if_returns_weaken.
  - apply (Hfold (list elt) (fun c visited => ret (c :: visited)) []
             (fun seen visited => visited = seen)).
    + reflexivity.
    + intros c seen visited _ ->. apply if_returns_ret. reflexivity.
  - intros visited (seen & Hperm & ->). exact Hperm.
Qed.

Theorem ported_create_is_not_invalid : ported_create_is_not_invalid_statement.
Proof.
  intros named try_reify dacc.
  unfold SimplifyPort.Simplify_primitive_result.create.
  apply if_returns_bind_any. intro machine_width.
  apply if_returns_bind_any. intro simplified_named.
  apply if_returns_ret. cbn. exists simplified_named. reflexivity.
Qed.

(* ======================================================================== *)
(* The step                                                                 *)
(* ======================================================================== *)

(* The port's set of possible results is a list in increasing order.
   What [add] returns is not the empty set. *)
Lemma cons_is_not_empty (e : Possible_result.t)
    (s : Possible_result.Set_.t) :
  (e :: s : Possible_result.Set_.t) <> Possible_result.Set_.empty.
Proof. unfold Possible_result.Set_.empty. discriminate. Qed.

Lemma add_is_not_empty (e : Possible_result.t) (s : Possible_result.Set_.t) :
  if_returns (Possible_result.Set_.add e s)
    (fun s' => s' <> Possible_result.Set_.empty).
Proof.
  destruct s as [ | e' rest]; cbn [Possible_result.Set_.add].
  - apply if_returns_ret. apply cons_is_not_empty.
  - apply if_returns_bind_any. intro c.
    destruct (c <? 0).
    + apply if_returns_ret. apply cons_is_not_empty.
    + destruct (c =? 0).
      * apply if_returns_ret. apply cons_is_not_empty.
      * apply if_returns_bind_any. intro rest'.
        apply if_returns_ret. apply cons_is_not_empty.
Qed.

Section Under_the_contracts.

  Variable machine_width : Target_system.Machine_width.t.
  Variable value : Num.t -> Z.
  Variable compatible : Num.t -> Prop.
  Hypothesis zero : zero_is_0 machine_width value compatible.
  Hypothesis one : one_is_1 machine_width value compatible.
  Hypothesis minus_one : minus_one_is_m1 machine_width value compatible.
  Hypothesis equal : equal_is_equality value compatible.
  Hypothesis create : create_is_not_invalid.
  Variable nums : Num.Set_.t.
  Variable known : list Num.t.
  Hypothesis fold : fold_visits Num.t Num.Set_.t (@Num.Set_.fold) nums known.
  Hypothesis known_compatible : forall c : Num.t, In c known -> compatible c.
  Variable denv : DE.t.
  Variable dacc : DA.t.
  Variable original_term : Named.t.
  Variable dbg : Debuginfo.t.
  Variable op : P.binary_int_arith_op.
  Variable result_var : Bound_var.t.
  Variable kind : K.t.
  Variable other_side : Simple.t.

  (* The model's operation has no result on a number in range and the
     reading of [c]. *)
  Let no_result (c : Num.t) : Prop :=
    forall j : Z,
      in_range tagged_width j = true ->
      eval_int_arith tagged_width (int_arith_op_of_port op) j (value c)
      = None.

  (* THE INVARIANT OF THE FOLD: if the set of possible results is there
     and is empty, the operation has no result on any number visited. *)
  Let inv (seen : list Num.t)
      (possible_results : option Possible_result.Set_.t) : Prop :=
    match possible_results with
    | None => True
    | Some s =>
      s = Possible_result.Set_.empty ->
      forall c : Num.t, In c seen -> no_result c
    end.

  (* A possible result is added: the set is then not empty. *)
  Ltac after_add :=
    eapply if_returns_bind;
    [ apply add_is_not_empty
    | let s' := fresh "s'" in
      let Hs' := fresh "Hs'" in
      let He := fresh "He" in
      intros s' Hs'; apply if_returns_ret; intro He; contradiction ].

  (* The calls of which nothing is known, up to the one that adds. *)
  Ltac to_the_add :=
    repeat first
      [ progress cbv zeta
      | after_add
      | apply if_returns_bind_any; intro ].

  (* The end of a path that makes its result with [SPR.create]. *)
  Ltac by_create :=
    eapply if_returns_weaken;
    [ apply create
    | let r := fresh "r" in
      let Hr := fresh "Hr" in
      let Hi := fresh "Hi" in
      intros r Hr Hi; destruct (Hr Hi) ].

  Lemma invalid_only_where_no_result_under_the_contracts :
    if_returns
      (Locals.only_one_side_known denv
         (Locals.check_possible_results
            (Locals.result_invalid kind dacc result_var) original_term dbg
            kind denv op dacc result_var)
         (Locals.result_unknown denv op dacc result_var original_term)
         Num.t Num.Set_.t
         (fun i => Tagged.op_lhs_unknown machine_width op i)
         nums
         (@Num.Set_.fold (option Possible_result.Set_.t))
         other_side)
      (fun r =>
         is_invalid_result r -> forall c : Num.t, In c known -> no_result c).
  Proof.
    unfold Locals.only_one_side_known.
    apply (if_returns_bind _ _
             (fun possible_results =>
                exists seen : list Num.t,
                  Permutation seen known /\ inv seen possible_results)).
    - (* The fold. *)
      refine (fold _ _ _ inv _ _).
      + intros _ c Hc. destruct Hc.
      + intros c seen possible_results Hc Hinv.
        destruct possible_results as [s | ]; cbv beta iota.
        2: { apply if_returns_ret. exact I. }
        eapply if_returns_bind.
        { apply pure_if_returns_if_returns.
          exact (op_lhs_unknown_sound machine_width value compatible zero one
                   minus_one equal op c (known_compatible c Hc)). }
        intros a Ha. unfold answer_is_sound in Ha.
        destruct a as [r | | | k | w | | ]; cbv beta iota.
        * (* Exactly *) to_the_add.
        * (* The_other_side *) to_the_add.
        * (* Negation_of_the_other_side *) to_the_add.
        * (* Bitwise_not_of_the_other_side *) to_the_add.
        * (* Float_negation_of_the_other_side *) to_the_add.
        * (* Cannot_simplify *) apply if_returns_ret. exact I.
        * (* Invalid *)
          apply if_returns_ret. intros He c' [<- | Hc'].
          -- exact Ha.
          -- exact (Hinv He c' Hc').
    - (* After the fold. *)
      intros possible_results (seen & Hperm & Hinv).
      destruct possible_results as [results | ]; cbv beta iota.
      + (* [check_possible_results] *)
        unfold Locals.check_possible_results.
        destruct results as [ | e rest]; cbn [Possible_result.Set_.is_empty].
        * (* The set is empty: whatever [result_invalid] returns. *)
          apply (if_returns_bind _ _ (fun b => b = true)).
          { apply if_returns_ret. reflexivity. }
          intros b ->. apply if_returns_any. intros r _ c Hc.
          apply (Hinv eq_refl).
          exact (Permutation_in c (Permutation_sym Hperm) Hc).
        * (* The set is not empty: the result is made by [SPR.create]. *)
          apply (if_returns_bind _ _ (fun b => b = false)).
          { apply if_returns_ret. reflexivity. }
          intros b ->. cbv beta iota.
          apply if_returns_bind_any. intro named.
          apply if_returns_bind_any. intros [ty simple_opt]. cbv beta iota.
          apply if_returns_bind_any. intro dacc'.
          destruct simple_opt as [simple | ]; cbv beta iota.
          -- apply if_returns_bind_any. intro named'. by_create.
          -- by_create.
      + (* [result_unknown] *)
        unfold Locals.result_unknown.
        apply if_returns_bind_any. intro machine_width'.
        apply if_returns_bind_any. intro dacc'.
        by_create.
  Qed.

End Under_the_contracts.

Theorem invalid_only_where_no_result : invalid_only_where_no_result_statement.
Proof.
  intros machine_width value compatible Hzero Hone Hminus_one Hequal Hcreate
    nums known Hfold Hknown denv dacc original_term dbg op result_var kind
    other_side.
  exact (invalid_only_where_no_result_under_the_contracts machine_width value
           compatible Hzero Hone Hminus_one Hequal Hcreate nums known Hfold
           Hknown denv dacc original_term dbg op result_var kind other_side).
Qed.

(* ======================================================================== *)
(* The port's [simplify], where it takes the step                           *)
(* ======================================================================== *)

(* After a call that, if it returns, returns one value. *)
Lemma if_returns_bind_value {A B : Type} (m : M A) (k : A -> M B) (v : A)
    (Q : B -> Prop) :
  if_returns m (fun a => a = v) ->
  if_returns (k v) Q ->
  if_returns (bind m k) Q.
Proof.
  intros Hm Hk. apply (if_returns_bind m k (fun a => a = v)).
  - exact Hm.
  - intros a Ha. rewrite Ha. exact Hk.
Qed.

Theorem simplify_invalid_is_sound : simplify_invalid_is_sound_statement.
Proof.
  intros machine_width value compatible Hzero Hone Hminus_one Hequal Hcreate
    nums known Hfold Hknown op dacc original_term dbg arg1 arg1_ty arg2
    arg2_ty result_var denv tenv Hdenv Htenv Hlhs Hrhs Hwidth.
  (* The tie. *)
  rewrite (simplify_is_its_named_locals op dacc original_term dbg arg1
             arg1_ty arg2 arg2_ty result_var).
  unfold Locals.simplify_with_named_locals.
  (* The four calls that choose the case. *)
  apply (if_returns_bind_value _ _ denv); [exact Hdenv | ].
  apply (if_returns_bind_value _ _ tenv); [exact Htenv | ].
  apply (if_returns_bind_value _ _ T.Need_meet); [exact Hlhs | ].
  apply (if_returns_bind_value _ _ (T.Known_result nums)); [exact Hrhs | ].
  cbv zeta beta iota.
  (* [N.ok_to_evaluate] is ported, and answers yes. *)
  apply (if_returns_bind_value _ _ true);
    [apply if_returns_ret; reflexivity | ].
  cbv beta iota. unfold seq.
  (* The assertion that the set is not empty: whatever it does. *)
  apply if_returns_bind_any. intros _.
  apply (if_returns_bind_value _ _ machine_width); [exact Hwidth | ].
  (* The step. *)
  exact (invalid_only_where_no_result machine_width value compatible Hzero
           Hone Hminus_one Hequal Hcreate nums known Hfold Hknown denv dacc
           original_term dbg op result_var Tagged.result_kind arg1).
Qed.
