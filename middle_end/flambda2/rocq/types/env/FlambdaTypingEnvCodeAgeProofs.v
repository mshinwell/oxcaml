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


(* Proofs of the statements of FlambdaTypingEnvCodeAgeSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaCodeAgeRelation FlambdaCodeAgeRelationSpec
  FlambdaCodeAgeRelationProofs FlambdaTypingEnv
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs
  FlambdaTypingEnvKindedSpec FlambdaTypingEnvCodeAgeSpec.
Import ListNotations.

(* ======================================================================== *)
(* Which functions change the relation                                      *)
(* ======================================================================== *)

Theorem create_code_age_relation : create_code_age_relation_statement.
Proof. reflexivity. Qed.

Theorem with_code_age_relation : with_code_age_relation_statement.
Proof. intros tenv rel. split; [ reflexivity | ]. repeat split. Qed.

Theorem with_code_age_relation_same : with_code_age_relation_same_statement.
Proof. intros [ ]. reflexivity. Qed.

Theorem add_to_code_age_relation_same_but :
  add_to_code_age_relation_same_but_statement.
Proof. intros tenv new_code_id old_code_id. repeat split. Qed.

Theorem add_to_code_age_relation_none :
  add_to_code_age_relation_none_statement.
Proof. intros [ ] new_code_id. reflexivity. Qed.

Theorem add_to_code_age_relation_older_version :
  add_to_code_age_relation_older_version_statement.
Proof.
  intros tenv new_code_id old_code_id id.
  exact (get_older_version_of_add (Typing_env.code_age_relation tenv)
           new_code_id old_code_id id).
Qed.

Lemma add_definitions_of_params_code_age_relation
    (params : list (variable * flambda_kind)) :
  ∀ tenv : Typing_env.t,
    Typing_env.code_age_relation
      (Typing_env.add_definitions_of_params tenv params)
    = Typing_env.code_age_relation tenv.
Proof.
  unfold Typing_env.add_definitions_of_params.
  induction params as [ | param params IH]; intros tenv; [ reflexivity | ].
  simpl. rewrite IH. reflexivity.
Qed.

Theorem code_age_relation_kept : code_age_relation_kept_statement.
Proof.
  intros tenv. cbv zeta.
  repeat match goal with |- _ ∧ _ => split end.
  - reflexivity.
  - intros current_level just_after_level. reflexivity.
  - intros current_level just_after_level next_binding_time. reflexivity.
  - intros aliases. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros var kind name_mode. reflexivity.
  - intros sym. reflexivity.
  - intros syms. reflexivity.
  - intros [var | sym] name_mode kind tenv'; simpl.
    + intros [= <-]. reflexivity.
    + destruct (Name_mode.equal name_mode Name_mode.normal);
        [ | discriminate ].
      intros [= <-]. reflexivity.
  - intros params. apply add_definitions_of_params_code_age_relation.
  - intros n ty. reflexivity.
  - intros canonical_element1 canonical_element2 result.
    unfold Typing_env.add_alias.
    destruct
      (Typing_env.aliases_add tenv canonical_element1 canonical_element2)
      as [[added | ] | ]; try discriminate.
    intros [= <-]. reflexivity.
  - reflexivity.
Qed.

(* ======================================================================== *)
(* The lookups, the aliases and [cut] do not read the relation              *)
(* ======================================================================== *)

(* Two environments that differ in their relations only are one
   environment with two relations. *)
Lemma same_but_code_age_relation_eq (tenv tenv' : Typing_env.t) :
  same_but_code_age_relation tenv tenv' ->
  tenv'
  = Typing_env.with_code_age_relation tenv
      (Typing_env.code_age_relation tenv').
Proof.
  destruct tenv, tenv'. unfold same_but_code_age_relation. simpl.
  intros (-> & -> & -> & -> & -> & -> & ->). reflexivity.
Qed.

Theorem same_but_code_age_relation_reads :
  same_but_code_age_relation_reads_statement.
Proof.
  intros tenv tenv' Hsame.
  rewrite (same_but_code_age_relation_eq tenv tenv' Hsame).
  repeat match goal with |- _ ∧ _ => split end; intros; reflexivity.
Qed.

Theorem same_but_code_age_relation_invariant :
  same_but_code_age_relation_invariant_statement.
Proof.
  intros tenv tenv' Hsame.
  rewrite (same_but_code_age_relation_eq tenv tenv' Hsame).
  repeat match goal with |- _ ∧ _ => split end;
    split; intros H; exact H.
Qed.

(* ======================================================================== *)
(* The order                                                                *)
(* ======================================================================== *)

Theorem add_to_code_age_relation_newer :
  add_to_code_age_relation_newer_statement.
Proof.
  intros tenv new_code_id old_code_id.
  apply (Newer_version _ new_code_id old_code_id old_code_id);
    [ | constructor ].
  rewrite
    (add_to_code_age_relation_older_version tenv new_code_id old_code_id
       new_code_id),
    Pos.eqb_refl.
  reflexivity.
Qed.

Theorem add_to_code_age_relation_order_grows :
  add_to_code_age_relation_order_grows_statement.
Proof.
  intros tenv new_code_id [old_code_id | ] id id' Hfresh H;
    [ | rewrite (add_to_code_age_relation_none tenv new_code_id); exact H ].
  induction H as [id | id older id' Holder H IH]; [ constructor | ].
  apply (Newer_version _ id older id'); [ | exact IH ].
  rewrite
    (add_to_code_age_relation_older_version tenv new_code_id old_code_id id).
  destruct (Pos.eqb_spec id new_code_id) as [-> | _]; [ | exact Holder ].
  rewrite Hfresh in Holder. discriminate Holder.
Qed.

Theorem add_to_code_age_relation_forgets :
  add_to_code_age_relation_forgets_statement.
Proof.
  cbv zeta. split.
  - apply same_or_newer_b_decides. reflexivity.
  - intros H. apply same_or_newer_b_decides in H. compute in H.
    discriminate H.
Qed.

(* ======================================================================== *)
(* A well-formed relation                                                   *)
(* ======================================================================== *)

Theorem create_code_ages_well_formed :
  create_code_ages_well_formed_statement.
Proof. exact empty_well_formed. Qed.

Theorem with_code_age_relation_well_formed :
  with_code_age_relation_well_formed_statement.
Proof. intros tenv rel. split; intros H; exact H. Qed.

Theorem add_to_code_age_relation_well_formed :
  add_to_code_age_relation_well_formed_statement.
Proof.
  intros tenv new_code_id old_code_id Hwf.
  exact (add_well_formed (Typing_env.code_age_relation tenv) new_code_id
           old_code_id Hwf).
Qed.

Theorem add_to_code_age_relation_not_well_formed :
  add_to_code_age_relation_not_well_formed_statement.
Proof.
  cbv zeta. split.
  - destruct
      (same_but_code_age_relation_invariant Typing_env.create _
         (add_to_code_age_relation_same_but Typing_env.create 1%positive
            (Some 1%positive)))
      as [[_ Hinvariant] _].
    exact (Hinvariant create_invariant).
  - intros Hwf. apply (Hwf 1%positive 1%positive); [ reflexivity | ].
    constructor.
Qed.
