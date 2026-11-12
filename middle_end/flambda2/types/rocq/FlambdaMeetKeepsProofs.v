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


(* Proofs of the statements of FlambdaMeetKeepsSpec.v. Nothing here
   needs review. The proofs of the files of the contract are read at
   the predicate that no static environment has
   (FlambdaMeetValidity.v). *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaClosuresSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaTypingEnv
  FlambdaMeetGrammar FlambdaExpandHead FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec FlambdaMeetStepsSpec FlambdaMeetHeadsSpec
  FlambdaMeetRowLikeSpec FlambdaMeetClosuresSpec FlambdaMeetFuelSpec
  FlambdaMeetExamplesSpec FlambdaMeetValidity FlambdaMeetHeadsProofs
  FlambdaMeetRowLikeProofs FlambdaMeetFuelProofs FlambdaMeetClosuresProofs
  FlambdaMeetExamplesProofs FlambdaMeetKeepsSpec.
Import ListNotations.

(* With no valid static environment, a join that has the half of its
   contract that is not about values has its contract. *)
Lemma join_keeps_sound_at_none (join : join_scoped_envs) :
  join_scoped_envs_keeps join ->
  join_scoped_envs_sound_for (V := no_validity) join.
Proof.
  intros Hjoin meet_head initial_env result scoped_envs. cbv zeta.
  intros _ Hkeeps Hfits Hscoped Hagree Hcall.
  split.
  - intros scoped_env statics valuation _ Hvalid. destruct Hvalid.
  - exact (Hjoin meet_head initial_env result scoped_envs Hkeeps Hfits
             Hscoped Hagree Hcall).
Qed.

Theorem meet_expanded_head_fuel_keeps :
  meet_expanded_head_fuel_keeps_statement.
Proof.
  intros join choices fuel Hjoin Hchoice Hdefine Hlift.
  pose proof (join_keeps_sound_at_none join Hjoin) as Hjoin'.
  exact
    (proj1
       (@meet_expanded_head_fuel_ok_for no_validity join choices Hchoice
          (fun mh Hkeeps Hsound _ v =>
             @meet_value_heads_ok_for no_validity join choices mh v Hjoin'
               Hdefine Hkeeps Hsound
               (@meet_row_like_for_blocks_ok_for no_validity join choices mh
                  v Hjoin' Hdefine Hlift Hkeeps Hsound)
               (@meet_row_like_for_closures_ok_for no_validity join choices
                  mh v Hjoin' Hdefine Hlift Hkeeps Hsound))
          fuel)).
Qed.

Theorem meet_expanded_head_repaired_keeps :
  meet_expanded_head_repaired_keeps_statement.
Proof.
  intros join fuel Hjoin.
  exact (meet_expanded_head_fuel_keeps join repaired_choices fuel Hjoin
           eq_refl eq_refl eq_refl).
Qed.

(* The join that forgets does not look at the meet that it is given:
   its contract is read at a meet that never answers, which has both
   contracts of a meet. *)
Theorem forgetful_join_keeps : forgetful_join_keeps_statement.
Proof.
  intros meet_head initial_env result scoped_envs. cbv zeta.
  intros _ Hfits Hscoped Hagree Hcall.
  assert (Hsound : meet_expanded_head_sound (fun _ _ _ => None)).
  { intros statics valuation menv expanded1 expanded2 v result' tenv _ _ _ _
      _ Hmeet.
    discriminate Hmeet. }
  assert (Hkeeps : meet_expanded_head_keeps (fun _ _ _ => None)).
  { intros menv menv' expanded1 expanded2 r tenv answered _ Hmeet.
    discriminate Hmeet. }
  exact (proj2
           (forgetful_join_sound (fun _ _ _ => None) initial_env result
              scoped_envs Hsound Hkeeps Hfits Hscoped Hagree Hcall)).
Qed.

Theorem meet_with_forgetful_join_keeps :
  meet_with_forgetful_join_keeps_statement.
Proof.
  intros fuel.
  exact (meet_expanded_head_repaired_keeps forgetful_join fuel
           forgetful_join_keeps).
Qed.
