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


(* Proofs of the statements of FlambdaTypeAliasKindsSpec.v. Nothing here
   needs review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeAliasKindsSpec.
Import ListNotations.

Theorem aliases_with_kinds_unknown : aliases_with_kinds_unknown_statement.
Proof. intros [ | [] | | ]; reflexivity. Qed.

Theorem aliases_with_kinds_bottom : aliases_with_kinds_bottom_statement.
Proof. intros [ | [] | | ]; reflexivity. Qed.

Theorem aliases_with_kinds_alias : aliases_with_kinds_alias_statement.
Proof. intros [ | [] | | ] s; reflexivity. Qed.

Theorem aliases_with_kinds_get_alias
  : aliases_with_kinds_get_alias_statement.
Proof.
  intros [ty | ty | k ty | ty | ty] s; simpl;
    destruct ty as [ | [head | s'] | ]; try discriminate;
    intros [= ->]; reflexivity.
Qed.

Theorem aliases_with_kinds_type_for_const
  : aliases_with_kinds_type_for_const_statement.
Proof.
  intros c s k. destruct c; simpl;
    try (intros [[= <- <-] | []]; split; reflexivity);
    try (intros []).
  rewrite aliases_with_kinds_unknown. intros [].
Qed.

Theorem aliases_with_kinds_these_naked_immediates
  : aliases_with_kinds_these_naked_immediates_statement.
Proof.
  intros [ | i [ | i' imms]] s k; simpl.
  - intros [].
  - intros [[= <- <-] | []]. exists i. repeat split.
  - intros [].
Qed.

Theorem aliases_with_kinds_these_tagged_immediates
  : aliases_with_kinds_these_tagged_immediates_statement.
Proof.
  intros [ | i [ | i' imms]] s k; simpl.
  - intros [].
  - intros [[= <- <-] | []]. exists i. repeat split.
  - intros [].
Qed.

Lemma aliases_of_unknown_cases (tags : list Z) :
  flat_map
    (fun case : Z * Or_unknown.t row_like_block_case =>
       match snd case with
       | Or_unknown.Known case =>
         aliases_of_block_case aliases_with_kinds aliases_of_env_extension
           case
       | Or_unknown.Unknown => []
       end)
    (map (fun tag => (tag, Or_unknown.Unknown)) tags)
  = [].
Proof.
  induction tags as [ | tag tags IH]; simpl; [ reflexivity | exact IH ].
Qed.

Theorem aliases_with_kinds_none : aliases_with_kinds_none_statement.
Proof.
  repeat split; try reflexivity.
  intros tags alloc_mode. unfold blocks_with_these_tags. simpl.
  rewrite aliases_of_unknown_cases. reflexivity.
Qed.

Theorem aliases_with_kinds_create_variant
  : aliases_with_kinds_create_variant_statement.
Proof.
  intros is_unique immediates blocks extensions. simpl.
  rewrite app_nil_r. reflexivity.
Qed.

Theorem aliases_with_kinds_tag_immediate
  : aliases_with_kinds_tag_immediate_statement.
Proof. intros t. simpl. rewrite !app_nil_r. reflexivity. Qed.

Theorem aliases_with_kinds_box_number
  : aliases_with_kinds_box_number_statement.
Proof. intros k contents alloc_mode. simpl. apply app_nil_r. Qed.

Theorem aliases_with_kinds_immutable_block
  : aliases_with_kinds_immutable_block_statement.
Proof.
  intros is_unique tag shape alloc_mode fields. simpl.
  unfold aliases_of_block_case. simpl. rewrite !app_nil_r. reflexivity.
Qed.

Theorem aliases_with_kinds_create_closures
  : aliases_with_kinds_create_closures_statement.
Proof. intros alloc_mode by_function_slot. simpl. apply app_nil_r. Qed.

Theorem aliases_with_kinds_this_closure
  : aliases_with_kinds_this_closure_statement.
Proof.
  intros slot function_types closure_types value_slot_types alloc_mode.
  split; simpl; rewrite !app_nil_r; reflexivity.
Qed.

(* ======================================================================== *)
(* The names of equations, with their kinds                                 *)
(* ======================================================================== *)

Theorem equation_names_none : equation_names_none_statement.
Proof.
  split; [ intros [ | [] | | ]; reflexivity | ].
  split; [ intros [ | [] | | ]; reflexivity | ].
  split; [ intros [ | [] | | ] s; reflexivity | ].
  intros c. destruct c as [ | | | | | | | | | | | | | | k];
    try reflexivity.
  destruct k as [ | [] | | ]; reflexivity.
Qed.

Theorem equation_names_of_equations
  : equation_names_of_equations_statement.
Proof.
  intros equations n ty Hin. simpl. split.
  - apply in_flat_map. exists (n, ty). split; [ exact Hin | ].
    left. reflexivity.
  - intros equation Hequation. apply in_flat_map. exists (n, ty).
    split; [ exact Hin | ]. right. exact Hequation.
Qed.

Theorem equation_names_create_variant
  : equation_names_create_variant_statement.
Proof. intros is_unique immediates blocks extensions. reflexivity. Qed.
