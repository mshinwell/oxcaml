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

(* Proofs of the statements of FlambdaValidateSpec.v. Nothing here needs
   review: each step of the check is a theorem of the file it comes from,
   and these are put end to end. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaCompareSpec FlambdaCompareProofs
  FlambdaNormaliseSpec FlambdaNormaliseProofs FlambdaBlockLoadSpec
  FlambdaBlockLoadProofs FlambdaUnusedStaticsSpec FlambdaUnusedStaticsProofs
  FlambdaValidateSpec.
From OxCamlFlambda2Types Require Import FlambdaAliasesSpec
  FlambdaAliasesProofs.
Import ListNotations.

Lemma expr_equivalent_refl (e : expr) : expr_equivalent e e.
Proof. intros vars conts statics. apply equivalent_refl. Qed.

Lemma expr_equivalent_sym (e e' : expr) :
  expr_equivalent e e' -> expr_equivalent e' e.
Proof. intros H vars conts statics. apply equivalent_sym, H. Qed.

(* One rewrite that is an equivalence, at the head of the right-hand
   side. *)
Ltac equivalence_step :=
  first
    [ apply fold_constants_equivalent
    | apply follow_aliases_equivalent
    | apply remove_unused_defined_lets_equivalent
    | apply drop_deleted_code_equivalent
    | apply merge_statics_equivalent
    | apply inline_known_calls_equivalent
    | apply thread_switches_equivalent ].

Ltac refinement_step :=
  first
    [ apply inline_calls_refines
    | apply collapse_switches_refines
    | apply inline_tail_conts_refines
    | apply remove_unused_lets_refines
    | apply load_known_blocks_refines
    | apply expr_equivalent_refines; equivalence_step ].

Lemma normalise_code_before_refines (body : expr) :
  expr_refines body (normalise_code_before body).
Proof.
  unfold normalise_code_before.
  repeat (eapply expr_refines_trans; [ | solve [ refinement_step ] ]).
  apply expr_refines_refl.
Qed.

Lemma normalise_before_round_refines (e : expr) :
  expr_refines e (normalise_before_round e).
Proof.
  unfold normalise_before_round.
  eapply expr_refines_trans;
    [ | apply rewrite_code_refines, normalise_code_before_refines ].
  repeat (eapply expr_refines_trans; [ | solve [ refinement_step ] ]).
  apply expr_refines_refl.
Qed.

Lemma normalise_code_after_equivalent (body : expr) :
  expr_equivalent body (normalise_code_after body).
Proof.
  unfold normalise_code_after.
  repeat (eapply expr_equivalent_trans; [ | solve [ equivalence_step ] ]).
  apply expr_equivalent_refl.
Qed.

Lemma normalise_after_round_equivalent (e : expr) :
  expr_equivalent e (normalise_after_round e).
Proof.
  unfold normalise_after_round.
  eapply expr_equivalent_trans;
    [ | apply rewrite_code_equivalent, normalise_code_after_equivalent ].
  repeat (eapply expr_equivalent_trans; [ | solve [ equivalence_step ] ]).
  apply expr_equivalent_refl.
Qed.

Lemma normalise_before_refines (rounds : nat) :
  ∀ e : expr, expr_refines e (normalise_before rounds e).
Proof.
  unfold normalise_before.
  induction rounds as [ | rounds IH]; intros e; simpl;
    [ apply expr_refines_refl | ].
  exact (expr_refines_trans _ _ _ (normalise_before_round_refines e)
    (IH _)).
Qed.

Lemma normalise_after_equivalent (rounds : nat) :
  ∀ e : expr, expr_equivalent e (normalise_after rounds e).
Proof.
  unfold normalise_after.
  induction rounds as [ | rounds IH]; intros e; simpl;
    [ apply expr_equivalent_refl | ].
  exact (expr_equivalent_trans _ _ _ (normalise_after_round_equivalent e)
    (IH _)).
Qed.

(* The two normalised terms being the same up to bound names, the term
   after refines the term before. *)
Lemma normalised_refines (rounds : nat) (before after : expr) :
  expr_eqb [] [] (normalise_before rounds before)
    (normalise_after rounds after)
  = true ->
  expr_refines before after.
Proof.
  intros Heq.
  apply (expr_refines_trans _ _ _ (normalise_before_refines rounds before)).
  apply expr_equivalent_refines.
  apply (expr_equivalent_trans _ _ _ (expr_eqb_sound _ _ Heq)).
  apply expr_equivalent_sym, normalise_after_equivalent.
Qed.

Lemma expr_refines_program (source target : expr) :
  expr_refines source target -> program_refines source target.
Proof. intros H. apply H. Qed.

Lemma without_statics_program_refines (D : dropped) (e : expr) :
  program_refines e (without_statics D e).
Proof.
  unfold without_statics.
  destruct (drop_statics D e) as [e' | ] eqn:Hdrop; [ | apply refines_refl ].
  apply (refines_trans _ _ _ (drop_statics_program_refines D e e' Hdrop)).
  apply expr_refines_program, expr_equivalent_refines.
  exact (expr_equivalent_trans _ _ _ (drop_deleted_code_equivalent e')
    (merge_statics_equivalent _)).
Qed.

Theorem validate_unit_sound_everywhere :
  validate_unit_sound_everywhere_statement.
Proof.
  intros rounds unused before after. unfold validate_unit.
  destruct (expr_eqb [] [] before after) eqn:Hsame.
  - intros _. apply expr_equivalent_refines, expr_eqb_sound, Hsame.
  - destruct (expr_eqb [] [] (normalise_before rounds before)
                (normalise_after rounds after)) eqn:Hnormalised.
    + intros _. exact (normalised_refines rounds before after Hnormalised).
    + destruct (expr_eqb [] []
                  (without_statics unused (normalise_before rounds before))
                  (normalise_after rounds after));
        intros [H | H]; discriminate H.
Qed.

Theorem validate_unit_sound : validate_unit_sound_statement.
Proof.
  intros rounds unused before after. unfold validate_unit.
  destruct (expr_eqb [] [] before after) eqn:Hsame.
  - intros _.
    apply expr_refines_program, expr_equivalent_refines, expr_eqb_sound,
      Hsame.
  - destruct (expr_eqb [] [] (normalise_before rounds before)
                (normalise_after rounds after)) eqn:Hnormalised.
    + intros _. apply expr_refines_program.
      exact (normalised_refines rounds before after Hnormalised).
    + destruct (expr_eqb [] []
                  (without_statics unused (normalise_before rounds before))
                  (normalise_after rounds after)) eqn:Hremoved;
        [ intros _ | intros H; contradiction H; reflexivity ].
      apply (refines_trans _
        (State (normalise_before rounds before) [] [] empty_static_env));
        [ apply expr_refines_program, normalise_before_refines | ].
      apply (refines_trans _ _ _
        (without_statics_program_refines unused _)).
      apply expr_refines_program, expr_equivalent_refines.
      apply (expr_equivalent_trans _ _ _ (expr_eqb_sound _ _ Hremoved)).
      apply expr_equivalent_sym, normalise_after_equivalent.
Qed.
