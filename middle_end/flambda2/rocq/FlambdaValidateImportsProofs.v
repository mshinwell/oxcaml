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

(* Proofs of the statements of FlambdaValidateImportsSpec.v. Nothing here
   needs review: the steps are those of FlambdaValidateProofs.v, each
   taken at a static environment in which the names removed do not
   occur; that of the imports is one. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaCompareSpec FlambdaCompareProofs
  FlambdaNormaliseSpec FlambdaNormaliseProofs FlambdaStaticsOrderSpec
  FlambdaStaticsOrderProofs FlambdaUnusedStaticsSpec
  FlambdaUnusedStaticsProofs FlambdaLoopifySpec FlambdaLoopifyProofs
  FlambdaLiftSpec FlambdaValidateSpec FlambdaValidateProofs
  FlambdaValidateKnowingSpec FlambdaValidateKnowingProofs
  FlambdaImportsSpec FlambdaImportsProofs FlambdaValidateImportsSpec.
From OxCamlFlambda2 Require Import FlambdaStubCallsSpec
  FlambdaStubCallsProofs.
Import ListNotations.

Lemma envs_free_of_statics (D : dropped) (statics : static_env) :
  statics_free_of D statics = true -> envs_free_of D [] [] statics = true.
Proof. intros Hfree. unfold envs_free_of. simpl. exact Hfree. Qed.

Lemma without_statics_refines_from (statics : static_env) (hp : heap)
    (D : dropped) (e : expr) :
  statics_free_of D statics = true ->
  refines (State e [] [] statics hp)
    (State (without_statics D e) [] [] statics hp).
Proof.
  intros Hfree. unfold without_statics.
  destruct (drop_statics D e) as [e' | ] eqn:Hdrop; [ | apply refines_refl ].
  apply (refines_trans _ _ _
    (drop_statics_refines D e e' Hdrop [] [] statics hp
       (envs_free_of_statics D statics Hfree))).
  apply (expr_equivalent_refines _ _
    (expr_equivalent_trans _ _ _ (drop_deleted_code_equivalent e')
       (merge_statics_equivalent _))).
Qed.

Theorem validate_unit_sound_from : validate_unit_sound_from_statement.
Proof.
  intros statics hp rounds unused slots G Ls kept before after.
  unfold validate_unit.
  destruct (expr_eqb [] [] before after) eqn:Hsame.
  - intros _ _.
    apply (expr_equivalent_refines _ _ (expr_eqb_sound _ _ Hsame)).
  - cbv zeta. intros Hvalidated Hfree.
    apply (refines_trans _ _ _
      (demote_stub_calls_refines before [] [] statics hp)).
    apply (refines_trans _ _ _
      (loopify_unit_refines G (demote_stub_calls before) [] [] statics hp)).
    revert Hvalidated. clear Hsame.
    generalize (loopify_unit G (demote_stub_calls before)). clear before.
    intros before.
    set (a := tidied_after rounds (normalise_after rounds kept after)).
    destruct (expr_eqb [] []
                (order_statics_as a
                   (tidied_before rounds
                      (normalise_before rounds kept before)))
                a)
      eqn:Hnormalised.
    + intros _.
      exact (normalised_refines rounds kept before after Hnormalised
               [] [] statics hp).
    + destruct (expr_eqb [] []
                  (order_statics_as a
                     (without_statics unused
                        (tidied_before rounds
                           (normalise_before rounds kept before))))
                  a) eqn:Hremoved.
      * intros _.
        apply (refines_trans _
          (State
             (tidied_before rounds (normalise_before rounds kept before))
             [] [] statics hp)).
        { apply (expr_refines_trans _ _ _
            (normalise_before_refines rounds kept before)
            (tidied_before_refines rounds _)). }
        apply (refines_trans _ _ _
          (without_statics_refines_from statics hp unused _ Hfree)).
        apply (expr_equivalent_refines _ _
          (ordered_same_equivalent rounds kept _ after Hremoved)).
      * (* What is left lifts, or is not validated. *)
        repeat
          match goal with
          | |- context [if ?c then _ else _] => destruct c
          end;
          discriminate.
Qed.

Theorem validate_unit_knowing_sound_from
    : validate_unit_knowing_sound_from_statement.
Proof.
  intros statics hp rounds unused slots G Ls kept before after Hvalidated
    Hfree.
  apply (refines_trans _ _ _
    (normalise_knowing_refines
       (normalise_before_round_avoiding
          (unit_continuations Ls ++ map snd G) kept)
       rounds before
       (normalise_before_round_avoiding_refines
          (unit_continuations Ls ++ map snd G) kept)
       [] [] statics hp)).
  apply (refines_trans _ _ _
    (validate_unit_sound_from statics hp rounds unused slots G Ls kept _ _
       Hvalidated Hfree)).
  apply (expr_equivalent_refines _ _
    (expr_equivalent_sym _ _
       (normalise_knowing_equivalent (normalise_after_round kept) rounds
          after (normalise_after_round_equivalent kept)))).
Qed.

(* The static environment of the imports is one in which no name
   occurs. *)
Lemma imports_statics_free (D : dropped)
    (imports : list (symbol * import_class)) :
  statics_free_of D (imports_statics imports) = true.
Proof.
  pose proof (imports_statics_free_of D imports) as Hfree.
  unfold envs_free_of in Hfree. simpl in Hfree. exact Hfree.
Qed.

Theorem validate_unit_sound_imports : validate_unit_sound_imports_statement.
Proof.
  intros imports rounds unused slots G Ls kept before after Hvalidated.
  exact (validate_unit_sound_from (imports_statics imports) empty_heap rounds
           unused slots G Ls kept before after Hvalidated
           (imports_statics_free unused imports)).
Qed.

Theorem validate_unit_knowing_sound_imports
    : validate_unit_knowing_sound_imports_statement.
Proof.
  intros imports rounds unused slots G Ls kept before after Hvalidated.
  exact (validate_unit_knowing_sound_from (imports_statics imports)
           empty_heap rounds unused slots G Ls kept before after Hvalidated
           (imports_statics_free unused imports)).
Qed.
