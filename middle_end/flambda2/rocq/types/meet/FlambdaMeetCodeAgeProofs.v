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

(* Proofs of the statements of FlambdaMeetCodeAgeSpec.v. Nothing here
   needs review. *)

From Stdlib Require Import PArith List Bool Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaCodeAgeRelation FlambdaCodeAgeRelationSpec
  FlambdaCodeAgeRelationProofs FlambdaTypingEnv FlambdaMeetEnv FlambdaMeet
  FlambdaMeetCodeAgeSpec.
Import ListNotations.

(* ======================================================================== *)
(* [meet_code_id], by the meet of the relation for one compilation unit     *)
(* ======================================================================== *)

Lemma meet_code_id_eq (menv : Meet_env.t) (id1 id2 : code_id) :
  meet_code_id menv id1 id2
  = if Pos.eqb id1 id2
    then Some (Meet_result.Ok Both_inputs menv)
    else
      match
        meet_in_unit (S (length (Meet_env.code_age_relation menv)))
          (Meet_env.code_age_relation menv) id1 id2
      with
      | None => None
      | Some Bottom => Some (Meet_result.Bottom (New_result tt))
      | Some Unknown => Some (Meet_result.Ok Both_inputs menv)
      | Some (Ok id) =>
        if Pos.eqb id id1
        then Some (Meet_result.Ok Left_input menv)
        else if Pos.eqb id id2
        then Some (Meet_result.Ok Right_input menv)
        else Some (Meet_result.Ok (New_result id) menv)
      end.
Proof. reflexivity. Qed.

(* What the meet of the relation answers for two different code ids, of
   every relation, with one step more than the relation has pairs. *)
Lemma meet_in_unit_some (rel : Code_age_relation.t) (id1 id2 : code_id)
    (answer : or_unknown_or_bottom code_id) :
  id1 <> id2 ->
  meet_in_unit (S (length rel)) rel id1 id2 = Some answer ->
  (answer = Ok id2 ∧ same_or_newer rel id2 id1)
  ∨ (answer = Ok id1 ∧ same_or_newer rel id1 id2)
  ∨ (answer = Bottom
     ∧ ~ same_or_newer rel id1 id2
     ∧ ~ same_or_newer rel id2 id1).
Proof.
  intros Hne. rewrite meet_in_unit_eq.
  destruct (Pos.eqb_spec id1 id2) as [Heq | _]; [ contradiction | ].
  assert (Hlen : length rel < S (length rel)) by lia.
  destruct (has_older_version_in_unit (S (length rel)) rel id2 [id1])
    as [[answer1 | ] | ] eqn:H1; simpl; [ | | discriminate ].
  2: { exfalso.
       exact (has_older_version_in_unit_not_unknown _ rel [id1] id2 H1). }
  destruct (has_older_version_in_unit (S (length rel)) rel id1 [id2])
    as [[answer2 | ] | ] eqn:H2; simpl; [ | | discriminate ].
  2: { exfalso.
       exact (has_older_version_in_unit_not_unknown _ rel [id2] id1 H2). }
  pose proof (has_older_version_in_unit_known _ rel id2 [id1] answer1 Hlen H1)
    as Hanswer1.
  pose proof (has_older_version_in_unit_known _ rel id1 [id2] answer2 Hlen H2)
    as Hanswer2.
  rewrite set_allows_singleton in Hanswer1, Hanswer2.
  intros [= <-]. destruct answer1, answer2.
  - left. split; [ reflexivity | apply Hanswer1; reflexivity ].
  - left. split; [ reflexivity | apply Hanswer1; reflexivity ].
  - right. left. split; [ reflexivity | apply Hanswer2; reflexivity ].
  - right. right. split; [ reflexivity | ].
    split; intros H;
      [ apply Hanswer2 in H | apply Hanswer1 in H ]; discriminate.
Qed.

(* ======================================================================== *)
(* What an answer says                                                      *)
(* ======================================================================== *)

Theorem meet_code_id_same : meet_code_id_same_statement.
Proof.
  intros menv id. rewrite meet_code_id_eq, Pos.eqb_refl. reflexivity.
Qed.

(* An answer, for two different code ids. *)
Lemma meet_code_id_different (menv : Meet_env.t) (id1 id2 : code_id)
    (result : Meet_result.t code_id) :
  id1 <> id2 ->
  meet_code_id menv id1 id2 = Some result ->
  (result = Meet_result.Ok Right_input menv
   ∧ same_or_newer (Meet_env.code_age_relation menv) id2 id1)
  ∨ (result = Meet_result.Ok Left_input menv
     ∧ same_or_newer (Meet_env.code_age_relation menv) id1 id2)
  ∨ (result = Meet_result.Bottom (New_result tt)
     ∧ ~ same_or_newer (Meet_env.code_age_relation menv) id1 id2
     ∧ ~ same_or_newer (Meet_env.code_age_relation menv) id2 id1).
Proof.
  intros Hne. rewrite meet_code_id_eq.
  destruct (Pos.eqb_spec id1 id2) as [Heq | _]; [ contradiction | ].
  destruct (meet_in_unit _ (Meet_env.code_age_relation menv) id1 id2)
    as [answer | ] eqn:Hmeet; [ | discriminate ].
  destruct (meet_in_unit_some _ id1 id2 answer Hne Hmeet)
    as [[-> H] | [[-> H] | [-> H]]].
  - assert (Hne' : Pos.eqb id2 id1 = false)
      by (apply Pos.eqb_neq; intros Heq; apply Hne; symmetry; exact Heq).
    rewrite Hne', Pos.eqb_refl. intros [= <-]. left.
    split; [ reflexivity | exact H ].
  - rewrite Pos.eqb_refl. intros [= <-]. right. left.
    split; [ reflexivity | exact H ].
  - intros [= <-]. right. right. split; [ reflexivity | exact H ].
Qed.

Theorem meet_code_id_ok : meet_code_id_ok_statement.
Proof.
  intros menv menv' id1 id2 r Hmeet.
  destruct (Pos.eq_dec id1 id2) as [-> | Hne].
  - rewrite meet_code_id_same in Hmeet. injection Hmeet as <- <-.
    split; [ reflexivity | ]. left. split; reflexivity.
  - destruct (meet_code_id_different menv id1 id2 _ Hne Hmeet)
      as [[[= -> ->] H] | [[[= -> ->] H] | [[=] _]]];
      (split; [ reflexivity | ]).
    + right. right. split; [ reflexivity | ]. split; assumption.
    + right. left. split; [ reflexivity | ]. split; assumption.
Qed.

Theorem meet_code_id_bottom : meet_code_id_bottom_statement.
Proof.
  intros menv id1 id2 r Hmeet.
  destruct (Pos.eq_dec id1 id2) as [-> | Hne].
  - rewrite meet_code_id_same in Hmeet. discriminate.
  - destruct (meet_code_id_different menv id1 id2 _ Hne Hmeet)
      as [[[=] _] | [[[=] _] | [_ H]]].
    exact H.
Qed.

Theorem meet_code_id_newer : meet_code_id_newer_statement.
Proof.
  intros menv menv' id1 id2 r Hmeet.
  destruct (meet_code_id_ok menv menv' id1 id2 r Hmeet)
    as [_ [[-> ->] | [[-> [_ H]] | [-> [_ H]]]]]; simpl.
  - split; constructor.
  - split; [ constructor | exact H ].
  - split; [ exact H | constructor ].
Qed.

(* ======================================================================== *)
(* Which answer there is, on a well-formed relation                         *)
(* ======================================================================== *)

Lemma steps_enough (rel : Code_age_relation.t) : length rel < S (length rel).
Proof. lia. Qed.

Theorem meet_code_id_left : meet_code_id_left_statement.
Proof.
  intros menv id1 id2 Hwf Hne H. rewrite meet_code_id_eq.
  destruct (Pos.eqb_spec id1 id2) as [Heq | _]; [ contradiction | ].
  assert (Hmeet :
            meet_in_unit (S (length (Meet_env.code_age_relation menv)))
              (Meet_env.code_age_relation menv) id1 id2
            = Some (Ok id1)).
  { apply (meet_in_unit_ok _ _ id1 id2 id1 Hwf (steps_enough _)).
    right. split; [ exact H | reflexivity ]. }
  rewrite Hmeet, Pos.eqb_refl. reflexivity.
Qed.

Theorem meet_code_id_right : meet_code_id_right_statement.
Proof.
  intros menv id1 id2 Hwf Hne H. rewrite meet_code_id_eq.
  destruct (Pos.eqb_spec id1 id2) as [Heq | _]; [ contradiction | ].
  assert (Hmeet :
            meet_in_unit (S (length (Meet_env.code_age_relation menv)))
              (Meet_env.code_age_relation menv) id1 id2
            = Some (Ok id2)).
  { apply (meet_in_unit_ok _ _ id1 id2 id2 Hwf (steps_enough _)).
    left. split; [ exact H | reflexivity ]. }
  assert (Hne' : Pos.eqb id2 id1 = false)
    by (apply Pos.eqb_neq; intros Heq; apply Hne; symmetry; exact Heq).
  rewrite Hmeet, Hne', Pos.eqb_refl. reflexivity.
Qed.

Theorem meet_code_id_unrelated : meet_code_id_unrelated_statement.
Proof.
  intros menv id1 id2 Hwf H12 H21. rewrite meet_code_id_eq.
  destruct (Pos.eqb_spec id1 id2) as [-> | _].
  - exfalso. apply H12. constructor.
  - assert (Hmeet :
              meet_in_unit (S (length (Meet_env.code_age_relation menv)))
                (Meet_env.code_age_relation menv) id1 id2
              = Some Bottom).
    { apply (meet_in_unit_bottom _ _ id1 id2 Hwf (steps_enough _)).
      split; assumption. }
    rewrite Hmeet. reflexivity.
Qed.

Theorem meet_code_id_answers : meet_code_id_answers_statement.
Proof.
  intros menv id1 id2 Hwf. rewrite meet_code_id_eq.
  destruct (Pos.eqb id1 id2); [ eexists; reflexivity | ].
  destruct (meet_in_unit_answers _ _ id1 id2 Hwf (steps_enough _))
    as [[id ->] | ->]; [ | eexists; reflexivity ].
  destruct (Pos.eqb id id1); [ eexists; reflexivity | ].
  destruct (Pos.eqb id id2); eexists; reflexivity.
Qed.

Theorem meet_code_id_no_code_lost : meet_code_id_no_code_lost_statement.
Proof.
  intros menv id1 id2 code Hwf H1 H2.
  destruct (Pos.eq_dec id1 id2) as [-> | Hne].
  - exists Both_inputs. split; [ apply meet_code_id_same | exact H1 ].
  - destruct (older_versions_chain _ code id1 id2 H1 H2) as [H | H].
    + exists Left_input.
      split; [ exact (meet_code_id_left menv id1 id2 Hwf Hne H) | exact H1 ].
    + exists Right_input.
      split; [ exact (meet_code_id_right menv id1 id2 Hwf Hne H) | exact H2 ].
Qed.

(* ======================================================================== *)
(* Where the relation has no link                                           *)
(* ======================================================================== *)

Theorem meet_code_id_no_link : meet_code_id_no_link_statement.
Proof.
  intros menv id1 id2 Hnone1 Hnone2. rewrite meet_code_id_eq.
  destruct (Pos.eqb_spec id1 id2) as [_ | Hne]; [ reflexivity | ].
  rewrite meet_in_unit_eq.
  assert (Hne12 : Pos.eqb id1 id2 = false) by (apply Pos.eqb_neq; exact Hne).
  assert (Hne21 : Pos.eqb id2 id1 = false)
    by (apply Pos.eqb_neq; intros Heq; apply Hne; symmetry; exact Heq).
  rewrite Hne12, !has_older_version_in_unit_succ.
  unfold among. simpl. rewrite Hne12, Hne21, Hnone1, Hnone2. reflexivity.
Qed.

(* ======================================================================== *)
(* An example                                                               *)
(* ======================================================================== *)

Lemma not_same_or_newer (rel : Code_age_relation.t) (id id' : code_id) :
  same_or_newer_b rel id id' = false -> ~ same_or_newer rel id id'.
Proof.
  intros Hb H. apply same_or_newer_b_decides in H. rewrite H in Hb.
  discriminate.
Qed.

Theorem meet_code_id_example : meet_code_id_example_statement.
Proof.
  split; [ | repeat split; reflexivity ].
  change (Meet_env.code_age_relation code_age_example_env)
    with (Code_age_relation.add
            (Code_age_relation.add
               (Code_age_relation.add Code_age_relation.empty 2%positive
                  1%positive)
               3%positive 1%positive)
            4%positive 2%positive).
  apply add_well_formed; [ | apply not_same_or_newer; reflexivity ].
  apply add_well_formed; [ | apply not_same_or_newer; reflexivity ].
  apply add_well_formed; [ | apply not_same_or_newer; reflexivity ].
  exact empty_well_formed.
Qed.
