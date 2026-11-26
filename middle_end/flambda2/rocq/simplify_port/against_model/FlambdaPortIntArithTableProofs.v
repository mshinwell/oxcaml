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

(* Proofs of the statements of FlambdaPortIntArithTableSpec.v. Nothing
   here needs review but that each theorem has the statement of its name.
   This file follows no file of the compiler.

   No [Axiom], no [Parameter], no [Admitted]. The four contracts are
   hypotheses of a section. After the section they are premises of each
   theorem, as its statement has them: they are not theorems, and [Print
   Assumptions] does not list them. *)

From Stdlib Require Import ZArith Bool.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaPrimitiveModel
  FlambdaPrimitiveSpec.
From OxCamlFlambda2Types Require Import FlambdaSimplifyArithSpec
  FlambdaSimplifyArithProofs.
From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort Require Simplify_binary_primitive.
From SimplifyPort.decl Require Flambda_primitive Scalar Target_system.
From SimplifyPortAgainstModel Require Import FlambdaPortIntArithTableSpec.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* A computation that is pure if it returns                                 *)
(* ======================================================================== *)

Lemma pure_if_returns_ret {A : Type} (a : A) (Q : A -> Prop) :
  Q a -> pure_if_returns (ret a) Q.
Proof. intros H n s. apply wp_ret. split; [exact H | reflexivity]. Qed.

Lemma pure_if_returns_bind {A B : Type} (m : M A) (k : A -> M B)
    (Q : A -> Prop) (R : B -> Prop) :
  pure_if_returns m Q ->
  (forall a : A, Q a -> pure_if_returns (k a) R) ->
  pure_if_returns (bind m k) R.
Proof.
  intros Hm Hk n s. apply wp_bind.
  eapply wp_weaken; [apply Hm | | auto].
  intros a s' [HQ ->]. apply Hk. exact HQ.
Qed.

Lemma pure_if_returns_weaken {A : Type} (m : M A) (Q R : A -> Prop) :
  pure_if_returns m Q -> (forall a : A, Q a -> R a) -> pure_if_returns m R.
Proof.
  intros Hm HQR n s. eapply wp_weaken; [apply Hm | | auto].
  intros a s' [HQ ->]. split; [exact (HQR a HQ) | reflexivity].
Qed.

(* ======================================================================== *)
(* The contracts have a model                                               *)
(* ======================================================================== *)

Theorem contracts_have_a_model : contracts_have_a_model_statement.
Proof.
  cbv zeta. repeat split;
    try (intros n s; apply wp_ret; repeat split; reflexivity).
  intros [fa a] [fb b] Ha Hb. simpl in Ha, Hb. subst fa fb.
  unfold model_equal. simpl. apply pure_if_returns_ret. reflexivity.
Qed.

(* ======================================================================== *)
(* The tagged immediates                                                    *)
(* ======================================================================== *)

Section Tagged_immediates.

  Variable machine_width : Target_system.Machine_width.t.
  Variable value : Num.t -> Z.
  Variable compatible : Num.t -> Prop.

  (* THE FOUR CONTRACTS, as hypotheses. *)
  Hypothesis zero : zero_is_0 machine_width value compatible.
  Hypothesis one : one_is_1 machine_width value compatible.
  Hypothesis minus_one : minus_one_is_m1 machine_width value compatible.
  Hypothesis equal : equal_is_equality value compatible.

  (* A test of a compatible number against one of the three constants: the
     rest of the computation is run on whether the number reads as that
     constant. *)
  Lemma test_of_a_constant {B : Type} (constant : M Num.t) (c : Z)
      (this_side : Num.t) (k : bool -> M B) (R : B -> Prop) :
    constant_reads_as value compatible constant c ->
    compatible this_side ->
    pure_if_returns (k (value this_side =? c)) R ->
    pure_if_returns
      (bind constant (fun tmp => bind (Num.equal this_side tmp) k)) R.
  Proof.
    intros Hconstant Hthis Hk.
    eapply pure_if_returns_bind; [exact Hconstant | ].
    intros z [Hz <-].
    eapply pure_if_returns_bind; [exact (equal this_side z Hthis Hz) | ].
    intros r ->. exact Hk.
  Qed.

  (* An answer [Exactly] of one of the three constants. *)
  Lemma exactly_a_constant (constant : M Num.t) (c : Z)
      (R : answer Num.t -> Prop) :
    constant_reads_as value compatible constant c ->
    (forall z : Num.t,
       value z = c ->
       R (SimplifyPort.Simplify_binary_primitive.Exactly z)) ->
    pure_if_returns
      (bind constant
         (fun tmp => ret (SimplifyPort.Simplify_binary_primitive.Exactly tmp)))
      R.
  Proof.
    intros Hconstant HR.
    eapply pure_if_returns_bind; [exact Hconstant | ].
    intros z [_ Hz]. apply pure_if_returns_ret. exact (HR z Hz).
  Qed.

  (* One step of a proof about the table: the next test, an answer
     [Exactly], the cases of a test, or another answer. *)
  Ltac table_step :=
    match goal with
    | |- pure_if_returns
           (bind (Num.zero _) (fun _ => bind (Num.equal _ _) _)) _ =>
      apply (test_of_a_constant _ 0); [exact zero | assumption | ]
    | |- pure_if_returns
           (bind (Num.one _) (fun _ => bind (Num.equal _ _) _)) _ =>
      apply (test_of_a_constant _ 1); [exact one | assumption | ]
    | |- pure_if_returns
           (bind (Num.minus_one _) (fun _ => bind (Num.equal _ _) _)) _ =>
      apply (test_of_a_constant _ (-1)); [exact minus_one | assumption | ]
    | |- pure_if_returns (bind (Num.zero _) (fun _ => ret _)) _ =>
      apply (exactly_a_constant _ 0); [exact zero | intros ? ?]
    | |- pure_if_returns (bind (Num.minus_one _) (fun _ => ret _)) _ =>
      apply (exactly_a_constant _ (-1)); [exact minus_one | intros ? ?]
    | |- pure_if_returns (if (?a =? ?b) && _ then _ else _) _ =>
      destruct (Z.eqb_spec a b); cbn [andb]
    | |- pure_if_returns (if ?a =? ?b then _ else _) _ =>
      destruct (Z.eqb_spec a b)
    | |- pure_if_returns (ret _) _ => apply pure_if_returns_ret
    end.

  (* The facts of the model's [int_arith_identities] for the number [j],
     and the end of a case: the answer is one of the four that say
     nothing, or the model's operation is one of those facts. *)
  Ltac by_the_identities :=
    try split;
    intros j Hj; cbn [answer_is_sound int_arith_op_of_port];
    try exact I;
    let H := fresh "H" in
    pose proof (int_arith_identities Standard_tagged_immediate j Hj) as H;
    cbv zeta in H; fold tagged_width in H;
    destruct H as
      (Hadd_l & Hadd_r & Hsub_r & Hmul_0_l & Hmul_0_r & Hmul_1_l & Hmul_1_r
       & Hand_m1_l & Hand_m1_r & Hand_0_l & Hand_0_r
       & Hor_m1_l & Hor_m1_r & Hor_0_l & Hor_0_r
       & Hxor_l & Hxor_r & Hdiv_mod & Hmod_m1);
    repeat match goal with
           | E : value _ = _ |- _ => rewrite E
           end;
    first
      [ assumption
      | match goal with
        | |- context [signedness_of_port ?s] =>
          destruct (Hdiv_mod (signedness_of_port s))
            as (Hdiv_0 & Hmod_0 & Hdiv_1 & Hmod_1);
          assumption
        end ].

  (* The table of the operations that are the same on both sides: its
     answer is sound with the known number on either side. *)
  Lemma symmetric_sound (op : Tagged.symmetric_op) (this_side : Num.t) :
    compatible this_side ->
    let model_op :=
      match op with
      | Tagged.Add => FlambdaPrimitiveModel.Add
      | Tagged.Mul => FlambdaPrimitiveModel.Mul
      | Tagged.And => FlambdaPrimitiveModel.And
      | Tagged.Or => FlambdaPrimitiveModel.Or
      | Tagged.Xor => FlambdaPrimitiveModel.Xor
      end
    in
    pure_if_returns
      (Tagged.symmetric_op_one_side_unknown machine_width op this_side)
      (fun a =>
         answer_is_sound tagged_width value a
           (fun j => eval_int_arith tagged_width model_op j (value this_side))
         /\ answer_is_sound tagged_width value a
              (fun j =>
                 eval_int_arith tagged_width model_op (value this_side) j)).
  Proof.
    intros Hthis model_op. subst model_op.
    destruct op; cbn [Tagged.symmetric_op_one_side_unknown];
      repeat table_step; by_the_identities.
  Qed.

  (* [op_lhs_unknown], under the four contracts. *)
  Lemma op_lhs_unknown_sound_under_the_contracts :
    op_lhs_unknown_answers_soundly machine_width value compatible.
  Proof.
    intros op rhs Hrhs.
    destruct op as [ | | | s | s | | | ]; cbn [Tagged.op_lhs_unknown];
      try (eapply pure_if_returns_weaken;
           [exact (symmetric_sound _ rhs Hrhs) | intros a [Hl _]; exact Hl]);
      try destruct s; repeat table_step; by_the_identities.
  Qed.

  (* [op_rhs_unknown], under the four contracts. *)
  Lemma op_rhs_unknown_sound_under_the_contracts :
    op_rhs_unknown_answers_soundly machine_width value compatible.
  Proof.
    intros op lhs Hlhs.
    destruct op as [ | | | s | s | | | ]; cbn [Tagged.op_rhs_unknown];
      try (eapply pure_if_returns_weaken;
           [exact (symmetric_sound _ lhs Hlhs) | intros a [_ Hr]; exact Hr]);
      try destruct s; repeat table_step; by_the_identities.
  Qed.

End Tagged_immediates.

(* THE TWO THEOREMS. The four contracts are premises of each. *)

Theorem op_lhs_unknown_sound : op_lhs_unknown_statement.
Proof.
  intros machine_width value compatible Hzero Hone Hminus_one Hequal.
  eapply op_lhs_unknown_sound_under_the_contracts; eassumption.
Qed.

Theorem op_rhs_unknown_sound : op_rhs_unknown_statement.
Proof.
  intros machine_width value compatible Hzero Hone Hminus_one Hequal.
  eapply op_rhs_unknown_sound_under_the_contracts; eassumption.
Qed.
