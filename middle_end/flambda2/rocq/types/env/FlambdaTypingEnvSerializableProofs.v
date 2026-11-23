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


(* Proofs of the statements of FlambdaTypingEnvSerializableSpec.v.
   Nothing here needs review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaBindingTime FlambdaCodeAgeRelation
  FlambdaCodeAgeRelationSpec FlambdaCodeAgeRelationProofs FlambdaTypingEnv
  FlambdaTypingEnvExtensionProofs FlambdaTypingEnvSerializableSpec.
Import ListNotations.

(* ======================================================================== *)
(* [Code_age_relation.union]                                                *)
(* ======================================================================== *)

(* [union] answers exactly when the two relations agree, and answers
   the first followed by the second. *)
Lemma union_some (rel1 rel2 rel : Code_age_relation.t) :
  Code_age_relation.union rel1 rel2 = Some rel ->
  rel = rel1 ++ rel2 ∧ relations_agree rel1 rel2.
Proof.
  unfold Code_age_relation.union.
  match goal with
  | |- context [forallb ?test ?ids] => destruct (forallb test ids) eqn:Hall
  end; [ | discriminate ].
  intros [= <-]. split; [ reflexivity | ].
  intros id older1 older2 H1 H2.
  unfold Code_age_relation.get_older_version_of in H1, H2.
  rewrite forallb_forall in Hall.
  assert (Hin : In id (map fst rel1)).
  { apply lookup_in in H1. exact (in_map fst rel1 (id, older1) H1). }
  specialize (Hall id Hin). cbv beta in Hall. rewrite H1, H2 in Hall.
  cbn in Hall. apply Pos.eqb_eq in Hall. exact Hall.
Qed.

Lemma union_agree (rel1 rel2 : Code_age_relation.t) :
  relations_agree rel1 rel2 ->
  Code_age_relation.union rel1 rel2 = Some (rel1 ++ rel2).
Proof.
  intros Hagree. unfold Code_age_relation.union.
  match goal with
  | |- context [forallb ?test ?ids] => destruct (forallb test ids) eqn:Hall
  end; [ reflexivity | ].
  apply Bool.not_true_iff_false in Hall. exfalso. apply Hall.
  apply forallb_forall. intros id _.
  destruct (lookup id rel1) as [older1 | ] eqn:H1; [ | reflexivity ].
  destruct (lookup id rel2) as [older2 | ] eqn:H2; [ | reflexivity ].
  apply Pos.eqb_eq. exact (Hagree id older1 older2 H1 H2).
Qed.

Lemma union_defined (rel1 rel2 : Code_age_relation.t) :
  Code_age_relation.union rel1 rel2 <> None <-> relations_agree rel1 rel2.
Proof.
  split.
  - destruct (Code_age_relation.union rel1 rel2) as [rel | ] eqn:Hunion;
      [ | intros H; contradiction ].
    intros _. exact (proj2 (union_some rel1 rel2 rel Hunion)).
  - intros Hagree. rewrite (union_agree rel1 rel2 Hagree). discriminate.
Qed.

(* ======================================================================== *)
(* The two maps of names                                                    *)
(* ======================================================================== *)

Lemma names_disjoint_b {A : Type} (names1 names2 : Keyed.finite_map name A) :
  Keyed.is_empty
    (Keyed.inter name_eqb (Keyed.domain name_eqb names1)
       (Keyed.domain name_eqb names2))
  = true
  <-> names_disjoint names1 names2.
Proof. exact (disjoint_domains name_eqb name_eqb_eq names1 names2). Qed.

Lemma is_bound_some {A : Type} (n : name) (a : A)
    (names : Keyed.finite_map name A) :
  Keyed.lookup name_eqb n names = Some a ->
  Keyed.is_bound name_eqb n names = true.
Proof. unfold Keyed.is_bound. intros ->. reflexivity. Qed.

(* [merge], unfolded: what it answers and when. *)
Lemma merge_some (t1 t2 t : Typing_env.Serializable.t) :
  Typing_env.Serializable.merge t1 t2 = Some t ->
  t
  = Typing_env.Serializable.Build_t
      (Typing_env.Serializable.defined_symbols_without_equations t1
       ++ Typing_env.Serializable.defined_symbols_without_equations t2)
      (Typing_env.Serializable.code_age_relation t1
       ++ Typing_env.Serializable.code_age_relation t2)
      (Typing_env.Serializable.names_to_types t1
       ++ Typing_env.Serializable.names_to_types t2)
  ∧ relations_agree (Typing_env.Serializable.code_age_relation t1)
      (Typing_env.Serializable.code_age_relation t2)
  ∧ names_disjoint (Typing_env.Serializable.names_to_types t1)
      (Typing_env.Serializable.names_to_types t2).
Proof.
  unfold Typing_env.Serializable.merge.
  destruct
    (Code_age_relation.union (Typing_env.Serializable.code_age_relation t1)
       (Typing_env.Serializable.code_age_relation t2))
    as [rel | ] eqn:Hunion; [ | simpl; discriminate ].
  apply union_some in Hunion. destruct Hunion as [-> Hagree]. simpl.
  destruct
    (Keyed.is_empty
       (Keyed.inter name_eqb
          (Keyed.domain name_eqb (Typing_env.Serializable.names_to_types t1))
          (Keyed.domain name_eqb
             (Typing_env.Serializable.names_to_types t2))))
    eqn:Hdisjoint; [ | simpl; discriminate ].
  simpl. intros [= <-].
  apply names_disjoint_b in Hdisjoint. repeat split; assumption.
Qed.

Lemma merge_agree (t1 t2 : Typing_env.Serializable.t) :
  relations_agree (Typing_env.Serializable.code_age_relation t1)
    (Typing_env.Serializable.code_age_relation t2) ->
  names_disjoint (Typing_env.Serializable.names_to_types t1)
    (Typing_env.Serializable.names_to_types t2) ->
  Typing_env.Serializable.merge t1 t2
  = Some
      (Typing_env.Serializable.Build_t
         (Typing_env.Serializable.defined_symbols_without_equations t1
          ++ Typing_env.Serializable.defined_symbols_without_equations t2)
         (Typing_env.Serializable.code_age_relation t1
          ++ Typing_env.Serializable.code_age_relation t2)
         (Typing_env.Serializable.names_to_types t1
          ++ Typing_env.Serializable.names_to_types t2)).
Proof.
  intros Hagree Hdisjoint. unfold Typing_env.Serializable.merge.
  rewrite (union_agree _ _ Hagree). simpl.
  rewrite (proj2 (names_disjoint_b _ _) Hdisjoint). reflexivity.
Qed.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

Theorem predefined_exceptions : predefined_exceptions_statement.
Proof. intros symbols. cbv zeta. repeat split. Qed.

Theorem merge_defined : merge_defined_statement.
Proof.
  intros t1 t2. split.
  - destruct (Typing_env.Serializable.merge t1 t2) as [t | ] eqn:Hmerge;
      [ | intros H; contradiction ].
    intros _. exact (proj2 (merge_some t1 t2 t Hmerge)).
  - intros [Hagree Hdisjoint].
    rewrite (merge_agree t1 t2 Hagree Hdisjoint). discriminate.
Qed.

Theorem merge_answer : merge_answer_statement.
Proof.
  intros t1 t2 t Hmerge.
  destruct (merge_some t1 t2 t Hmerge) as (-> & Hagree & Hdisjoint).
  simpl. split; [ reflexivity | ]. split.
  - intros id older. unfold Code_age_relation.get_older_version_of.
    rewrite lookup_app.
    destruct (lookup id (Typing_env.Serializable.code_age_relation t1))
      as [older1 | ] eqn:H1.
    + split; [ intros H; left; exact H | ].
      intros [H | H]; [ exact H | ].
      rewrite (Hagree id older1 older H1 H). reflexivity.
    + split; [ intros H; right; exact H | ].
      intros [H | H]; [ discriminate H | exact H ].
  - intros n entry. rewrite keyed_lookup_app.
    destruct
      (Keyed.lookup name_eqb n (Typing_env.Serializable.names_to_types t1))
      as [entry1 | ] eqn:H1.
    + split; [ intros H; left; exact H | ].
      intros [H | H]; [ exact H | ].
      apply is_bound_some in H1, H. rewrite (Hdisjoint n H1) in H.
      discriminate H.
    + split; [ intros H; right; exact H | ].
      intros [H | H]; [ discriminate H | exact H ].
Qed.

Theorem merge_order : merge_order_statement.
Proof.
  intros t1 t2 t id id' Hmerge.
  destruct (merge_answer t1 t2 t Hmerge) as (_ & Holder & _).
  assert (Hgrows :
    ∀ (rel : Code_age_relation.t) (newer older : code_id),
      (∀ id next : code_id,
        Code_age_relation.get_older_version_of rel id = Some next ->
        Code_age_relation.get_older_version_of
          (Typing_env.Serializable.code_age_relation t) id
        = Some next) ->
      same_or_newer rel newer older ->
      same_or_newer (Typing_env.Serializable.code_age_relation t) newer
        older).
  { intros rel newer older Hrel H.
    induction H as [newer | newer next older Hstep H IH]; [ constructor | ].
    exact (Newer_version _ newer next older (Hrel newer next Hstep) IH). }
  intros [H | H].
  - apply (Hgrows (Typing_env.Serializable.code_age_relation t1));
      [ | exact H ].
    intros id0 next Hstep. apply Holder. left. exact Hstep.
  - apply (Hgrows (Typing_env.Serializable.code_age_relation t2));
      [ | exact H ].
    intros id0 next Hstep. apply Holder. right. exact Hstep.
Qed.

Theorem merge_not_well_formed : merge_not_well_formed_statement.
Proof.
  cbv zeta.
  assert (Hone :
    ∀ newer older : code_id,
      newer <> older ->
      well_formed
        (Code_age_relation.add Code_age_relation.empty newer older)).
  { intros newer older Hne.
    apply (add_well_formed Code_age_relation.empty newer older
             empty_well_formed).
    intros H. inversion H as [ | id next id'' Hstep ]; subst.
    - apply Hne. reflexivity.
    - discriminate Hstep. }
  split; [ apply Hone; discriminate | ].
  split; [ apply Hone; discriminate | ].
  eexists. split; [ reflexivity | ].
  intros Hwf. apply (Hwf 1%positive 2%positive); [ reflexivity | ].
  apply same_or_newer_b_decides. reflexivity.
Qed.

Theorem merge_predefined_exceptions : merge_predefined_exceptions_statement.
Proof.
  intros symbols t. apply merge_agree.
  - intros id older1 older2 H. discriminate H.
  - intros n H. discriminate H.
Qed.

Theorem merge_with_itself : merge_with_itself_statement.
Proof.
  intros t. destruct (merge_defined t t) as [Hto Hfrom]. split.
  - intros Hdefined. destruct (Hto Hdefined) as [_ Hdisjoint].
    destruct (Typing_env.Serializable.names_to_types t)
      as [ | [n entry] names]; [ reflexivity | ].
    assert (Hbound :
      Keyed.is_bound name_eqb n ((n, entry) :: names) = true).
    { apply (is_bound_some n entry).
      exact (keyed_lookup_head name_eqb name_eqb_eq n entry names). }
    rewrite (Hdisjoint n Hbound) in Hbound. discriminate Hbound.
  - intros Hnone. apply Hfrom. split.
    + intros id older1 older2 H1 H2. rewrite H1 in H2.
      injection H2 as ->. reflexivity.
    + rewrite Hnone. intros n H. discriminate H.
Qed.
