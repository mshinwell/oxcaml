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

(* Proofs of the statements of FlambdaPortIntArithTableKindsSpec.v.
   Nothing here needs review but that each theorem has the statement of
   its name. This file follows no file of the compiler.

   THE PROOF IS WRITTEN ONCE, in the functor [Sound] over the argument
   of the port's functor [Int_ops_for_binary_arith], a module [Numbers]
   of numbers: it is the proof of FlambdaPortIntArithTableProofs.v, for
   the table at [Numbers] and the width of any kind of the model. Each
   of the seven modules of the port is the port's functor at a module of
   decl/. Rocq takes the table of [Sound] at that module for the port's
   own: each of the fourteen theorems is one application of [Sound].

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
From SimplifyPort.decl Require Flambda_primitive Number_adjuncts Scalar
  Target_system.
From SimplifyPortAgainstModel Require Import FlambdaPortIntArithTableSpec
  FlambdaPortIntArithTableProofs FlambdaPortIntArithTableKindsSpec.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The table at any argument of the port's functor                          *)
(* ======================================================================== *)

Module Sound
    (Numbers : SimplifyPort.decl.Number_adjuncts.Int_number_kind).

  Module Ops :=
    SimplifyPort.Simplify_binary_primitive.Int_ops_for_binary_arith
      Numbers.
  Module Num := Numbers.Num.

  Section Under_the_contracts.

    Variable kind : standard_int.
    Variable machine_width : Target_system.Machine_width.t.
    Variable value : Num.t -> Z.
    Variable compatible : Num.t -> Prop.
    Hypothesis zero :
      constant_reads_as value compatible (Num.zero machine_width) 0.
    Hypothesis one :
      constant_reads_as value compatible (Num.one machine_width) 1.
    Hypothesis minus_one :
      constant_reads_as value compatible (Num.minus_one machine_width) (-1).
    Hypothesis equal : tests_equality value compatible Num.equal.

    Let width := int_width kind.

    (* A test of a compatible number against one of the three constants:
       the rest of the computation is run on whether the number reads as
       that constant. *)
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
           (fun tmp =>
              ret (SimplifyPort.Simplify_binary_primitive.Exactly tmp)))
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

    (* The facts of the model's [int_arith_identities] for the number
       [j], and the end of a case: the answer is one of the four that say
       nothing, or the model's operation is one of those facts. *)
    Ltac by_the_identities :=
      try split;
      intros j Hj; cbn [answer_is_sound int_arith_op_of_port];
      try exact I;
      let H := fresh "H" in
      pose proof (int_arith_identities kind j Hj) as H;
      cbv zeta in H; change (int_width kind) with width in H;
      destruct H as
        (Hadd_l & Hadd_r & Hsub_r & Hmul_0_l & Hmul_0_r & Hmul_1_l
         & Hmul_1_r & Hand_m1_l & Hand_m1_r & Hand_0_l & Hand_0_r
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
    Lemma symmetric_sound (op : Ops.symmetric_op) (this_side : Num.t) :
      compatible this_side ->
      let model_op :=
        match op with
        | Ops.Add => FlambdaPrimitiveModel.Add
        | Ops.Mul => FlambdaPrimitiveModel.Mul
        | Ops.And => FlambdaPrimitiveModel.And
        | Ops.Or => FlambdaPrimitiveModel.Or
        | Ops.Xor => FlambdaPrimitiveModel.Xor
        end
      in
      pure_if_returns
        (Ops.symmetric_op_one_side_unknown machine_width op this_side)
        (fun a =>
           answer_is_sound width value a
             (fun j => eval_int_arith width model_op j (value this_side))
           /\ answer_is_sound width value a
                (fun j => eval_int_arith width model_op (value this_side) j)).
    Proof.
      intros Hthis model_op. subst model_op.
      destruct op; cbn [Ops.symmetric_op_one_side_unknown];
        repeat table_step; by_the_identities.
    Qed.

    (* [op_lhs_unknown], under the four contracts. *)
    Lemma op_lhs_unknown_sound_under_the_contracts :
      forall (op : P.binary_int_arith_op) (rhs : Num.t),
        compatible rhs ->
        pure_if_returns (Ops.op_lhs_unknown machine_width op rhs)
          (fun a =>
             answer_is_sound width value a
               (fun j =>
                  eval_int_arith width (int_arith_op_of_port op) j
                    (value rhs))).
    Proof.
      intros op rhs Hrhs.
      destruct op as [ | | | s | s | | | ]; cbn [Ops.op_lhs_unknown];
        try (eapply pure_if_returns_weaken;
             [exact (symmetric_sound _ rhs Hrhs) | intros a [Hl _]; exact Hl]);
        try destruct s; repeat table_step; by_the_identities.
    Qed.

    (* [op_rhs_unknown], under the four contracts. *)
    Lemma op_rhs_unknown_sound_under_the_contracts :
      forall (op : P.binary_int_arith_op) (lhs : Num.t),
        compatible lhs ->
        pure_if_returns (Ops.op_rhs_unknown machine_width op lhs)
          (fun a =>
             answer_is_sound width value a
               (fun j =>
                  eval_int_arith width (int_arith_op_of_port op)
                    (value lhs) j)).
    Proof.
      intros op lhs Hlhs.
      destruct op as [ | | | s | s | | | ]; cbn [Ops.op_rhs_unknown];
        try (eapply pure_if_returns_weaken;
             [exact (symmetric_sound _ lhs Hlhs) | intros a [_ Hr]; exact Hr]);
        try destruct s; repeat table_step; by_the_identities.
    Qed.

  End Under_the_contracts.

  (* The two general statements, for the table at [Numbers]. *)
  Lemma op_lhs_unknown_sound (kind : standard_int) :
    lhs_unknown_table_sound Num.t (int_width kind)
      Num.zero Num.one Num.minus_one Num.equal Ops.op_lhs_unknown.
  Proof.
    intros machine_width value compatible Hzero Hone Hminus_one Hequal.
    eapply op_lhs_unknown_sound_under_the_contracts; eassumption.
  Qed.

  Lemma op_rhs_unknown_sound (kind : standard_int) :
    rhs_unknown_table_sound Num.t (int_width kind)
      Num.zero Num.one Num.minus_one Num.equal Ops.op_rhs_unknown.
  Proof.
    intros machine_width value compatible Hzero Hone Hminus_one Hequal.
    eapply op_rhs_unknown_sound_under_the_contracts; eassumption.
  Qed.

End Sound.

(* ======================================================================== *)
(* The seven modules of the port                                            *)
(* ======================================================================== *)

Module Sound_tagged :=
  Sound SimplifyPort.decl.Number_adjuncts.For_tagged_immediates.

Theorem tagged_op_lhs_unknown_sound : tagged_op_lhs_unknown_statement.
Proof. exact Sound_tagged.op_lhs_unknown_sound. Qed.

Theorem tagged_op_rhs_unknown_sound : tagged_op_rhs_unknown_statement.
Proof. exact Sound_tagged.op_rhs_unknown_sound. Qed.

Module Sound_naked :=
  Sound SimplifyPort.decl.Number_adjuncts.For_naked_immediates.

Theorem naked_op_lhs_unknown_sound : naked_op_lhs_unknown_statement.
Proof. exact Sound_naked.op_lhs_unknown_sound. Qed.

Theorem naked_op_rhs_unknown_sound : naked_op_rhs_unknown_statement.
Proof. exact Sound_naked.op_rhs_unknown_sound. Qed.

Module Sound_int8 :=
  Sound SimplifyPort.decl.Number_adjuncts.For_int8s.

Theorem int8_op_lhs_unknown_sound : int8_op_lhs_unknown_statement.
Proof. exact Sound_int8.op_lhs_unknown_sound. Qed.

Theorem int8_op_rhs_unknown_sound : int8_op_rhs_unknown_statement.
Proof. exact Sound_int8.op_rhs_unknown_sound. Qed.

Module Sound_int16 :=
  Sound SimplifyPort.decl.Number_adjuncts.For_int16s.

Theorem int16_op_lhs_unknown_sound : int16_op_lhs_unknown_statement.
Proof. exact Sound_int16.op_lhs_unknown_sound. Qed.

Theorem int16_op_rhs_unknown_sound : int16_op_rhs_unknown_statement.
Proof. exact Sound_int16.op_rhs_unknown_sound. Qed.

Module Sound_int32 :=
  Sound SimplifyPort.decl.Number_adjuncts.For_int32s.

Theorem int32_op_lhs_unknown_sound : int32_op_lhs_unknown_statement.
Proof. exact Sound_int32.op_lhs_unknown_sound. Qed.

Theorem int32_op_rhs_unknown_sound : int32_op_rhs_unknown_statement.
Proof. exact Sound_int32.op_rhs_unknown_sound. Qed.

Module Sound_int64 :=
  Sound SimplifyPort.decl.Number_adjuncts.For_int64s.

Theorem int64_op_lhs_unknown_sound : int64_op_lhs_unknown_statement.
Proof. exact Sound_int64.op_lhs_unknown_sound. Qed.

Theorem int64_op_rhs_unknown_sound : int64_op_rhs_unknown_statement.
Proof. exact Sound_int64.op_rhs_unknown_sound. Qed.

Module Sound_nativeint :=
  Sound SimplifyPort.decl.Number_adjuncts.For_nativeints.

Theorem nativeint_op_lhs_unknown_sound : nativeint_op_lhs_unknown_statement.
Proof. exact Sound_nativeint.op_lhs_unknown_sound. Qed.

Theorem nativeint_op_rhs_unknown_sound : nativeint_op_rhs_unknown_statement.
Proof. exact Sound_nativeint.op_rhs_unknown_sound. Qed.

(* ======================================================================== *)
(* This file and FlambdaPortIntArithTableSpec.v                             *)
(* ======================================================================== *)

Theorem tagged_statements_agree : tagged_statements_agree_statement.
Proof.
  split; intro H; exact (H Standard_tagged_immediate).
Qed.
