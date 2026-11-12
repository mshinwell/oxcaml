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
   taken at the static environment of the imports. *)

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
Import ListNotations.

(* No name occurs in the static environment of the imports. *)
Lemma imports_statics_free_of (D : dropped)
    (imports : list (symbol * import_class)) :
  envs_free_of D [] [] (imports_statics imports) = true.
Proof.
  unfold envs_free_of, statics_free_of, imports_statics. simpl.
  induction imports as [ | [s c] imports IH]; [ reflexivity | exact IH ].
Qed.

Lemma without_statics_unit_refines (imports : list (symbol * import_class))
    (D : dropped) (e : expr) :
  unit_refines imports e (without_statics D e).
Proof.
  unfold without_statics, unit_refines.
  destruct (drop_statics D e) as [e' | ] eqn:Hdrop; [ | apply refines_refl ].
  apply (refines_trans _ _ _
    (drop_statics_refines D e e' Hdrop [] [] (imports_statics imports)
       empty_heap (imports_statics_free_of D imports))).
  apply (expr_refines_unit_refines imports), expr_equivalent_refines.
  exact (expr_equivalent_trans _ _ _ (drop_deleted_code_equivalent e')
    (merge_statics_equivalent _)).
Qed.

Theorem validate_unit_sound_imports : validate_unit_sound_imports_statement.
Proof.
  intros imports rounds unused slots G Ls kept before after.
  unfold validate_unit.
  destruct (expr_eqb [] [] before after) eqn:Hsame.
  - intros _.
    apply expr_refines_unit_refines, expr_equivalent_refines, expr_eqb_sound,
      Hsame.
  - cbv zeta. intros Hvalidated.
    apply (refines_trans _ _ _
      (expr_refines_unit_refines imports _ _ (loopify_unit_refines G before))).
    revert Hvalidated. clear Hsame.
    generalize (loopify_unit G before). clear before. intros before.
    set (a := tidied_after rounds (normalise_after rounds kept after)).
    destruct (expr_eqb [] []
                (order_statics_as a
                   (tidied_before rounds
                      (normalise_before rounds kept before)))
                a)
      eqn:Hnormalised.
    + intros _. apply expr_refines_unit_refines.
      exact (normalised_refines rounds kept before after Hnormalised).
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
             [] [] (imports_statics imports) empty_heap)).
        { apply (expr_refines_unit_refines imports).
          apply (expr_refines_trans _ _ _
            (normalise_before_refines rounds kept before)).
          apply tidied_before_refines. }
        apply (refines_trans _ _ _
          (without_statics_unit_refines imports unused _)).
        apply (expr_refines_unit_refines imports), expr_equivalent_refines.
        exact (ordered_same_equivalent rounds kept _ after Hremoved).
      * (* What is left lifts, or is not validated. *)
        repeat
          match goal with
          | |- context [if ?c then _ else _] => destruct c
          end;
          discriminate.
Qed.

Theorem validate_unit_knowing_sound_imports
    : validate_unit_knowing_sound_imports_statement.
Proof.
  intros imports rounds unused slots G Ls kept before after Hvalidated.
  unfold unit_refines.
  apply (refines_trans _ _ _
    (expr_refines_unit_refines imports _ _
       (normalise_knowing_refines
          (normalise_before_round_avoiding
             (unit_continuations Ls ++ map snd G) kept)
          rounds before
          (normalise_before_round_avoiding_refines
             (unit_continuations Ls ++ map snd G) kept)))).
  apply (refines_trans _ _ _
    (validate_unit_sound_imports imports rounds unused slots G Ls kept _ _
       Hvalidated)).
  apply (expr_refines_unit_refines imports), expr_equivalent_refines,
    expr_equivalent_sym.
  exact (normalise_knowing_equivalent (normalise_after_round kept) rounds
           after (normalise_after_round_equivalent kept)).
Qed.
