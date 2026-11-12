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
  FlambdaBlockLoadProofs FlambdaForwardSpec FlambdaForwardProofs
  FlambdaLoopAliasesSpec FlambdaLoopAliasesProofs
  FlambdaLoopLetsSpec FlambdaLoopLetsProofs FlambdaParamAliasesSpec
  FlambdaParamAliasesProofs FlambdaRecHandlersSpec FlambdaRecHandlersProofs
  FlambdaShortcutSpec FlambdaShortcutProofs FlambdaSinkContsSpec
  FlambdaSinkContsProofs FlambdaUnboxSpec FlambdaUnboxProofs
  FlambdaUnusedContsSpec FlambdaUnusedContsProofs FlambdaUnusedParamsSpec
  FlambdaUnusedParamsProofs FlambdaUnusedStaticsSpec
  FlambdaUnusedStaticsProofs FlambdaLiftSpec FlambdaLiftProofs
  FlambdaUnusedSlotsSpec FlambdaUnusedSlotsProofs FlambdaKnownSymbolsSpec
  FlambdaKnownSymbolsProofs FlambdaKnownClosuresSpec FlambdaKnownClosuresProofs
  FlambdaFloatCodeSpec FlambdaFloatCodeProofs FlambdaValidateSpec.
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
    | apply thread_switches_equivalent
    | apply remove_unused_conts_equivalent
    | apply sink_let_conts_equivalent
    | apply follow_aliases_in_loops_equivalent
    | apply shortcut_switches_equivalent
    | apply remove_unused_defined_lets_in_loops_equivalent ].

Ltac refinement_step :=
  first
    [ apply inline_calls_refines
    | apply collapse_switches_refines
    | apply inline_tail_conts_refines
    | apply remove_unused_lets_refines
    | apply load_known_blocks_refines
    | apply unbox_known_numbers_refines
    | apply drop_unused_params_refines
    | apply bind_aliased_params_refines
    | apply forward_applications_refines
    | apply expr_equivalent_refines; equivalence_step ].

Lemma normalise_expr_before_refines (e : expr) :
  expr_refines e (normalise_expr_before e).
Proof.
  unfold normalise_expr_before. cbv zeta.
  repeat (eapply expr_refines_trans; [ | solve [ refinement_step ] ]).
  apply expr_refines_refl.
Qed.

Lemma normalise_code_before_refines (body : expr) :
  expr_refines body (normalise_code_before body).
Proof.
  unfold normalise_code_before.
  exact (expr_refines_trans _ _ _ (normalise_expr_before_refines body)
    (rewrite_rec_handlers_refines _ normalise_expr_before_refines _)).
Qed.

Lemma normalise_before_round_refines (e : expr) :
  expr_refines e (normalise_before_round e).
Proof.
  unfold normalise_before_round.
  eapply expr_refines_trans;
    [ | apply rewrite_code_refines, normalise_code_before_refines ].
  repeat (eapply expr_refines_trans; [ | solve [ refinement_step ] ]).
  eapply expr_refines_trans; [ | apply normalise_code_before_refines ].
  apply inline_calls_refines.
Qed.

(* The first phase of the term before. *)
Lemma normalise_expr_params_refines (e : expr) :
  expr_refines e (normalise_expr_params e).
Proof.
  unfold normalise_expr_params. cbv zeta.
  repeat (eapply expr_refines_trans; [ | solve [ refinement_step ] ]).
  apply expr_refines_refl.
Qed.

Lemma normalise_code_params_refines (body : expr) :
  expr_refines body (normalise_code_params body).
Proof.
  unfold normalise_code_params.
  exact (expr_refines_trans _ _ _
    (rewrite_rec_handlers_refines _ normalise_expr_params_refines body)
    (normalise_expr_params_refines _)).
Qed.

Lemma normalise_params_round_refines (e : expr) :
  expr_refines e (normalise_params_round e).
Proof.
  unfold normalise_params_round.
  eapply expr_refines_trans;
    [ | apply rewrite_code_refines, normalise_code_params_refines ].
  apply normalise_code_params_refines.
Qed.

Lemma iterate_refines (f : expr -> expr) :
  (∀ e : expr, expr_refines e (f e)) ->
  ∀ (rounds : nat) (e : expr), expr_refines e (iterate rounds f e).
Proof.
  intros Hf rounds.
  induction rounds as [ | rounds IH]; intros e; simpl;
    [ apply expr_refines_refl | ].
  exact (expr_refines_trans _ _ _ (Hf e) (IH _)).
Qed.

Lemma normalise_expr_after_equivalent (e : expr) :
  expr_equivalent e (normalise_expr_after e).
Proof.
  unfold normalise_expr_after.
  repeat (eapply expr_equivalent_trans; [ | solve [ equivalence_step ] ]).
  apply expr_equivalent_refl.
Qed.

Lemma normalise_code_after_equivalent (body : expr) :
  expr_equivalent body (normalise_code_after body).
Proof.
  unfold normalise_code_after.
  exact (expr_equivalent_trans _ _ _ (normalise_expr_after_equivalent body)
    (rewrite_rec_handlers_equivalent _ normalise_expr_after_equivalent _)).
Qed.

Lemma normalise_after_round_equivalent (e : expr) :
  expr_equivalent e (normalise_after_round e).
Proof.
  unfold normalise_after_round.
  eapply expr_equivalent_trans;
    [ | apply rewrite_code_equivalent, normalise_code_after_equivalent ].
  repeat (eapply expr_equivalent_trans; [ | solve [ equivalence_step ] ]).
  eapply expr_equivalent_trans;
    [ | apply rewrite_rec_handlers_equivalent,
          normalise_expr_after_equivalent ].
  repeat (eapply expr_equivalent_trans; [ | solve [ equivalence_step ] ]).
  apply expr_equivalent_refl.
Qed.

Lemma normalise_before_refines (rounds : nat) :
  ∀ e : expr, expr_refines e (normalise_before rounds e).
Proof.
  intros e. unfold normalise_before.
  exact (expr_refines_trans _ _ _
    (iterate_refines _ normalise_params_round_refines rounds e)
    (iterate_refines _ normalise_before_round_refines rounds _)).
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

Lemma with_lifting_program_refines (L : lifting) (e : expr) :
  program_refines e (with_lifting L e).
Proof.
  unfold with_lifting.
  destruct (lift_unit L e) as [e' | ] eqn:Hlift; [ | apply refines_refl ].
  exact (lift_unit_program_refines L e e' Hlift).
Qed.

Lemma with_known_program_refines (e : expr) :
  program_refines e (with_known e).
Proof.
  unfold with_known.
  destruct (fold_known_unit e) as [e' | ] eqn:Hfold; [ | apply refines_refl ].
  exact (fold_known_unit_program_refines e e' Hfold).
Qed.

Lemma iterate_lifted_program_refines (rounds : nat) :
  ∀ e : expr, program_refines e (iterate rounds normalise_lifted_round e).
Proof.
  induction rounds as [ | rounds IH]; intros e; simpl;
    [ apply refines_refl | ].
  apply (refines_trans _ _ _
    (expr_refines_program _ _ (normalise_before_round_refines e))).
  apply (refines_trans _ _ _
    (expr_refines_program _ _ (use_known_closures_refines _))).
  apply (refines_trans _ _ _ (with_known_program_refines _)).
  apply IH.
Qed.

Lemma normalise_lifted_program_refines (rounds : nat) :
  ∀ e : expr, program_refines e (normalise_lifted rounds e).
Proof.
  intros e. unfold normalise_lifted.
  exact (refines_trans _ _ _
    (expr_refines_program _ _
       (iterate_refines _ normalise_params_round_refines rounds e))
    (iterate_lifted_program_refines rounds _)).
Qed.

Lemma lifted_in_turn_program_refines (rounds : nat) (Ls : list lifting) :
  ∀ e : expr, program_refines e (lifted_in_turn rounds Ls e).
Proof.
  induction Ls as [ | L Ls IH]; intros e; simpl; [ apply refines_refl | ].
  apply (refines_trans _ _ _ (with_lifting_program_refines L _)).
  apply (refines_trans _ _ _ (normalise_lifted_program_refines rounds _)).
  apply IH.
Qed.

Lemma without_slots_program_refines (slots : list value_slot) (e : expr) :
  program_refines e (without_slots slots e).
Proof.
  unfold without_slots.
  destruct (drop_unused_slots slots e) as [e' | ] eqn:Hdrop;
    [ | apply refines_refl ].
  exact (drop_unused_slots_program_refines slots e e' Hdrop).
Qed.

Theorem validate_unit_sound_everywhere :
  validate_unit_sound_everywhere_statement.
Proof.
  intros rounds unused slots Ls before after. unfold validate_unit.
  destruct (expr_eqb [] [] before after) eqn:Hsame.
  - intros _. apply expr_equivalent_refines, expr_eqb_sound, Hsame.
  - destruct (expr_eqb [] [] (normalise_before rounds before)
                (normalise_after rounds after)) eqn:Hnormalised.
    + intros _. exact (normalised_refines rounds before after Hnormalised).
    + destruct (expr_eqb [] []
                  (without_statics unused (normalise_before rounds before))
                  (normalise_after rounds after));
        [ intros [H | H]; discriminate H | ].
      destruct
        (expr_eqb [] []
           (float_code
              (without_statics unused
                 (without_slots slots (lifted_in_turn rounds Ls before))))
           (float_code (normalise_after rounds after)));
        intros [H | H]; discriminate H.
Qed.

Theorem validate_unit_sound : validate_unit_sound_statement.
Proof.
  intros rounds unused slots Ls before after. unfold validate_unit.
  destruct (expr_eqb [] [] before after) eqn:Hsame.
  - intros _.
    apply expr_refines_program, expr_equivalent_refines, expr_eqb_sound,
      Hsame.
  - destruct (expr_eqb [] [] (normalise_before rounds before)
                (normalise_after rounds after)) eqn:Hnormalised.
    + intros _. apply expr_refines_program.
      exact (normalised_refines rounds before after Hnormalised).
    + assert (Hbefore :
        program_refines before (normalise_before rounds before))
        by apply expr_refines_program, normalise_before_refines.
      destruct (expr_eqb [] []
                  (without_statics unused (normalise_before rounds before))
                  (normalise_after rounds after)) eqn:Hremoved.
      * intros _. apply (refines_trans _ _ _ Hbefore).
        apply (refines_trans _ _ _
          (without_statics_program_refines unused _)).
        apply expr_refines_program, expr_equivalent_refines.
        apply (expr_equivalent_trans _ _ _ (expr_eqb_sound _ _ Hremoved)).
        apply expr_equivalent_sym, normalise_after_equivalent.
      * destruct
          (expr_eqb [] []
             (float_code
                (without_statics unused
                   (without_slots slots
                      (lifted_in_turn rounds Ls before))))
             (float_code (normalise_after rounds after))) eqn:Hlifted;
          [ intros _ | intros H; contradiction H; reflexivity ].
        apply (refines_trans _ _ _
          (lifted_in_turn_program_refines rounds Ls _)).
        apply (refines_trans _ _ _ (without_slots_program_refines slots _)).
        apply (refines_trans _ _ _
          (without_statics_program_refines unused _)).
        apply expr_refines_program, expr_equivalent_refines.
        apply (expr_equivalent_trans _ _ _ (float_code_equivalent _)).
        apply (expr_equivalent_trans _ _ _ (expr_eqb_sound _ _ Hlifted)).
        apply expr_equivalent_sym.
        exact (expr_equivalent_trans _ _ _
          (normalise_after_equivalent rounds after)
          (float_code_equivalent _)).
Qed.
