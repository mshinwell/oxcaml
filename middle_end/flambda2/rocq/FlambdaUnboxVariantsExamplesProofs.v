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


(* Proofs of the statements of FlambdaUnboxVariantsExamplesSpec.v.
   Nothing here needs review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaCompareSpec FlambdaCompareProofs
  FlambdaNormaliseSpec FlambdaNormaliseProofs FlambdaBlockLoadSpec
  FlambdaBlockLoadProofs FlambdaLoopAliasesSpec FlambdaLoopAliasesProofs
  FlambdaShortcutSpec FlambdaShortcutProofs FlambdaSinkContsSpec
  FlambdaSinkContsProofs FlambdaUnboxSpec FlambdaUnboxProofs
  FlambdaUnusedContsSpec FlambdaUnusedContsProofs FlambdaUnusedParamsSpec
  FlambdaUnusedParamsProofs FlambdaValidateSpec FlambdaValidateProofs
  FlambdaUnboxParamsSpec FlambdaUnboxParamsExamplesSpec
  FlambdaUnboxVariantsSpec FlambdaUnboxVariantsProofs
  FlambdaUnboxVariantsExamplesSpec.
From OxCamlFlambda2Types Require Import FlambdaAliasesSpec FlambdaAliasesProofs.
Import ListNotations.

(* The round refines, as each of its rewrites does. *)
Lemma round_with_variants_refines (e : expr) :
  expr_refines e (round_with_variants e).
Proof.
  unfold round_with_variants. cbv zeta.
  repeat
    (eapply expr_refines_trans;
     [ | solve
           [ first [ apply unbox_variant_params_refines | refinement_step ] ]
     ]).
  apply expr_refines_refl.
Qed.

Lemma rounds_with_variants_refine (rounds : nat) :
  ∀ e : expr, expr_refines e (iterate rounds round_with_variants e).
Proof.
  induction rounds as [ | rounds IH]; intros e; simpl.
  - apply expr_refines_refl.
  - exact (expr_refines_trans _ _ _ (round_with_variants_refines e)
      (IH (round_with_variants e))).
Qed.

(* What is the same as the body after, once the rounds are done, is
   refined by it. *)
Lemma validated_refines (rounds : nat) (before after : expr) :
  expr_eqb [] [] (iterate rounds round_with_variants before) after = true ->
  expr_refines before after.
Proof.
  intros Hsame.
  exact (expr_refines_trans _ _ _ (rounds_with_variants_refine rounds before)
    (expr_equivalent_refines _ _ (expr_eqb_sound _ _ Hsame))).
Qed.

Theorem option_heap_validated : option_heap_validated_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem option_heap_not_validated_today :
  option_heap_not_validated_today_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem option_heap_refines : option_heap_refines_statement.
Proof. exact (validated_refines 5 _ _ option_heap_validated). Qed.

Theorem list_heap_validated : list_heap_validated_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem list_heap_not_validated_today :
  list_heap_not_validated_today_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem list_heap_refines : list_heap_refines_statement.
Proof. exact (validated_refines 5 _ _ list_heap_validated). Qed.

Theorem shape_heap_validated : shape_heap_validated_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem shape_heap_not_validated_today :
  shape_heap_not_validated_today_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem shape_heap_refines : shape_heap_refines_statement.
Proof. exact (validated_refines 5 _ _ shape_heap_validated). Qed.

Theorem shape2_heap_validated : shape2_heap_validated_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem shape2_heap_not_validated_today :
  shape2_heap_not_validated_today_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem shape2_heap_refines : shape2_heap_refines_statement.
Proof. exact (validated_refines 5 _ _ shape2_heap_validated). Qed.

Theorem nested_heap_validated : nested_heap_validated_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem nested_heap_not_validated_today :
  nested_heap_not_validated_today_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem nested_heap_refines : nested_heap_refines_statement.
Proof. exact (validated_refines 5 _ _ nested_heap_validated). Qed.

Theorem either_heap_validated : either_heap_validated_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem either_heap_not_validated_today :
  either_heap_not_validated_today_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem either_heap_refines : either_heap_refines_statement.
Proof. exact (validated_refines 5 _ _ either_heap_validated). Qed.

Theorem int64_option_heap_validated : int64_option_heap_validated_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem int64_option_heap_not_validated_today :
  int64_option_heap_not_validated_today_statement.
Proof. vm_compute. reflexivity. Qed.

Theorem int64_option_heap_refines : int64_option_heap_refines_statement.
Proof. exact (validated_refines 5 _ _ int64_option_heap_validated). Qed.

Theorem earlier_examples_validated : earlier_examples_validated_statement.
Proof. split; vm_compute; reflexivity. Qed.
