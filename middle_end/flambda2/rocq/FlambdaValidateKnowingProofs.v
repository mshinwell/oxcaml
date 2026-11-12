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

(* Proofs of the statements of FlambdaValidateKnowingSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaNormaliseSpec FlambdaNormaliseProofs
  FlambdaUnusedStaticsSpec FlambdaNominalSpec FlambdaValidateSpec
  FlambdaValidateProofs FlambdaValidatorEquivarianceSpec
  FlambdaValidatorEquivarianceProofs FlambdaValidateKnowingSpec.
From OxCamlFlambda2Types Require FlambdaEnvAliasesFollowSpec
  FlambdaEnvAliasesFollowProofs.
From OxCamlFlambda2Types Require Import FlambdaEnvAliasesFollowScopeSpec
  FlambdaEnvAliasesFollowScopeProofs.
Import ListNotations.

Theorem normalise_knowing_refines : normalise_knowing_refines_statement.
Proof.
  intros round rounds e Hround. revert e. unfold normalise_knowing.
  induction rounds as [ | rounds IH]; intros e; simpl;
    [ apply expr_refines_refl | ].
  refine (expr_refines_trans _ _ _ _ (IH _)). unfold knowing_round.
  eapply expr_refines_trans; [ | apply Hround ].
  apply expr_equivalent_refines.
  apply FlambdaEnvAliasesFollowProofs.follow_aliases_equivalent.
Qed.

Theorem normalise_knowing_equivalent : normalise_knowing_equivalent_statement.
Proof.
  intros round rounds e Hround. revert e. unfold normalise_knowing.
  induction rounds as [ | rounds IH]; intros e; simpl;
    [ apply expr_equivalent_refl | ].
  refine (expr_equivalent_trans _ _ _ _ (IH _)). unfold knowing_round.
  eapply expr_equivalent_trans; [ | apply Hround ].
  apply FlambdaEnvAliasesFollowProofs.follow_aliases_equivalent.
Qed.

Theorem validate_knowing_sound : validate_knowing_sound_statement.
Proof.
  intros round_before round_after rounds before after Hbefore Hafter
    Hnormalised.
  apply (refines_trans _ _ _
    (expr_refines_program _ _
       (normalise_knowing_refines round_before rounds before Hbefore))).
  apply (refines_trans _ _ _ Hnormalised).
  apply expr_refines_program, expr_equivalent_refines, expr_equivalent_sym.
  exact (normalise_knowing_equivalent round_after rounds after Hafter).
Qed.

Theorem validate_knowing_sound_everywhere
    : validate_knowing_sound_everywhere_statement.
Proof.
  intros round_before round_after rounds before after Hbefore Hafter
    Hnormalised.
  apply (expr_refines_trans _ _ _
    (normalise_knowing_refines round_before rounds before Hbefore)).
  apply (expr_refines_trans _ _ _ Hnormalised).
  apply expr_equivalent_refines, expr_equivalent_sym.
  exact (normalise_knowing_equivalent round_after rounds after Hafter).
Qed.

(* ======================================================================== *)
(* Renaming and scope                                                       *)
(* ======================================================================== *)

Lemma knowing_round_keeps_scope (round : expr -> expr) :
  keeps_scope round -> keeps_scope (knowing_round round).
Proof.
  intros Hround.
  exact (keeps_scope_compose _ round
    follow_aliases_knowing_nothing_keeps_scope
    Hround).
Qed.

Theorem normalise_knowing_keeps_scope
    : normalise_knowing_keeps_scope_statement.
Proof.
  intros round rounds Hround.
  exact (keeps_scope_iterate rounds (knowing_round round)
    (knowing_round_keeps_scope round Hround)).
Qed.

Theorem normalise_knowing_equivariant
    : normalise_knowing_equivariant_statement.
Proof.
  intros round rounds Hround r. unfold normalise_knowing.
  induction rounds as [ | rounds IH]; intros e; simpl; [ reflexivity | ].
  rewrite <- IH. f_equal. unfold knowing_round.
  rewrite (FlambdaEnvAliasesFollowProofs.rename_follow_aliases_empty r e).
  apply Hround.
Qed.

Theorem normalise_knowing_equivariant_up_to
    : normalise_knowing_equivariant_up_to_statement.
Proof.
  intros round rounds Hscope Hround.
  apply (equivariant_up_to_iterate rounds (knowing_round round));
    [ exact (knowing_round_keeps_scope round Hscope) | ].
  apply (equivariant_up_to_compose _ round
    follow_aliases_knowing_nothing_keeps_scope
    Hscope);
    [ | exact Hround ].
  apply rewrite_equivariant_up_to.
  exact FlambdaEnvAliasesFollowProofs.rename_follow_aliases_empty.
Qed.
