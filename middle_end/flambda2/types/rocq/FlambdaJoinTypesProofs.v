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


(* Proofs of the statements of FlambdaJoinTypesSpec.v. Nothing here
   needs review. *)

From Stdlib Require Import ZArith List Bool PeanoNat Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaJoinEnv FlambdaJoinTypes FlambdaJoinSpec FlambdaJoinTypesSpec.
Import ListNotations.

(* ======================================================================== *)
(* Sets of numbers, and lists of contributors                               *)
(* ======================================================================== *)

Lemma numbers_union_in (n : Z) (numbers numbers' : list Z) :
  n ∈ numbers_union numbers numbers' <-> n ∈ numbers ∨ n ∈ numbers'.
Proof.
  unfold numbers_union.
  rewrite <- (keyed_among_in Z Z.eqb Z.eqb_eq n (Keyed.dedup Z.eqb _)).
  rewrite (keyed_among_dedup Z Z.eqb Z.eqb_eq).
  rewrite (keyed_among_in Z Z.eqb Z.eqb_eq).
  apply in_app_iff.
Qed.

(* What [known_contents] answers: the contents of the list, before what
   it was given to start with. *)
Lemma known_contents_spec {A : Type}
    (or_unknowns : list (Index.t * Or_unknown.t A)) :
  ∀ (acc contents : list (Index.t * A)),
    known_contents acc or_unknowns = Some contents ->
    map fst contents = rev (map fst or_unknowns) ++ map fst acc
    ∧ (∀ (index : Index.t) (a : A),
         In (index, a) contents ->
         In (index, a) acc ∨ In (index, Or_unknown.Known a) or_unknowns)
    ∧ (∀ (index : Index.t) (a : Or_unknown.t A),
         In (index, a) or_unknowns ->
         ∃ a' : A, a = Or_unknown.Known a' ∧ In (index, a') contents)
    ∧ ∀ (index : Index.t) (a : A), In (index, a) acc -> In (index, a) contents.
Proof.
  induction or_unknowns as [ | [id [a | ]] or_unknowns IH];
    intros acc contents Hcontents; simpl in Hcontents.
  - injection Hcontents as <-. simpl. repeat split; auto.
    intros index a [].
  - destruct (IH _ _ Hcontents) as (Hfst & Hfrom & Hto & Hacc).
    repeat split.
    + rewrite Hfst. simpl. rewrite <- app_assoc. reflexivity.
    + intros index a' Hin.
      destruct (Hfrom index a' Hin) as [[Heq | Hin'] | Hin'].
      * right. left. congruence.
      * left. exact Hin'.
      * right. right. exact Hin'.
    + intros index a' [Heq | Hin].
      * injection Heq as <- <-. exists a. split; [ reflexivity | ].
        apply Hacc. left. reflexivity.
      * exact (Hto index a' Hin).
    + intros index a' Hin. apply Hacc. right. exact Hin.
  - discriminate.
Qed.

(* ======================================================================== *)
(* What [deduce_is_int] and [deduce_get_tag] answer                         *)
(* ======================================================================== *)

Lemma block_not_immediate (statics : static_env) (i tag : Z)
    (fields : list value) :
  block_of statics (Value_const (Tagged_immediate i)) <> Some (tag, fields).
Proof. discriminate. Qed.

Theorem deduce_is_int_simple_is_sound : deduce_is_int_simple_sound.
Proof.
  intros statics vars v is_int immediates get_tag blocks extensions is_unique
    simple Hsatisfied Hsimple.
  rewrite variant_satisfied in Hsatisfied.
  unfold deduce_is_int_simple, deduce_is_int in Hsimple.
  destruct Hsatisfied
    as [(i & -> & His_int & Himmediates & _)
       | (tag & fields & Hblock & His_int & _ & Hblocks & _)].
  - (* An immediate. *)
    left. split; [ exists i; reflexivity | ].
    destruct blocks as [blocks | ].
    + destruct (row_like_for_blocks_is_bottom blocks).
      * injection Hsimple as <-. reflexivity.
      * destruct immediates as [immediates | ].
        -- destruct (is_obviously_bottom immediates) eqn:Hbottom.
           ++ exfalso.
              exact (is_obviously_bottom_satisfied _ _ _ _ Hbottom Himmediates).
           ++ destruct is_int as [is_int | ]; [ | discriminate ].
              injection Hsimple as <-. exact His_int.
        -- destruct is_int as [is_int | ]; [ | discriminate ].
           injection Hsimple as <-. exact His_int.
    + destruct immediates as [immediates | ].
      * destruct (is_obviously_bottom immediates) eqn:Hbottom.
        -- exfalso.
           exact (is_obviously_bottom_satisfied _ _ _ _ Hbottom Himmediates).
        -- destruct is_int as [is_int | ]; [ | discriminate ].
           injection Hsimple as <-. exact His_int.
      * destruct is_int as [is_int | ]; [ | discriminate ].
        injection Hsimple as <-. exact His_int.
  - (* A block. *)
    right. split; [ exists tag, fields; exact Hblock | ].
    destruct blocks as [blocks | ].
    + destruct (row_like_for_blocks_is_bottom blocks) eqn:Hbottom.
      * exfalso.
        exact (row_like_for_blocks_is_bottom_satisfied _ _ _ _ _ Hbottom
                 Hblocks).
      * destruct immediates as [immediates | ].
        -- destruct (is_obviously_bottom immediates).
           ++ injection Hsimple as <-. reflexivity.
           ++ destruct is_int as [is_int | ]; [ | discriminate ].
              injection Hsimple as <-. exact His_int.
        -- destruct is_int as [is_int | ]; [ | discriminate ].
           injection Hsimple as <-. exact His_int.
    + destruct immediates as [immediates | ].
      * destruct (is_obviously_bottom immediates).
        -- injection Hsimple as <-. reflexivity.
        -- destruct is_int as [is_int | ]; [ | discriminate ].
           injection Hsimple as <-. exact His_int.
      * destruct is_int as [is_int | ]; [ | discriminate ].
        injection Hsimple as <-. exact His_int.
Qed.

(* The tag of a block that a row-like structure with no other case
   admits is one of its known tags. *)
Lemma row_like_tag_among (statics : static_env) (vars : env) (tag : Z)
    (fields : list value)
    (known_tags : Keyed.finite_map Z (Or_unknown.t row_like_block_case))
    (alloc_mode : Alloc_mode.t) :
  row_like_for_blocks_satisfied statics vars tag fields
    (Row_like_for_blocks known_tags Or_bottom.Bottom alloc_mode) ->
  Keyed.among Z.eqb tag (Keyed.domain Z.eqb known_tags) = true.
Proof.
  rewrite row_like_for_blocks_find_iff,
    (keyed_among_domain Z Z.eqb Z.eqb_eq).
  unfold Keyed.is_bound.
  destruct (Keyed.lookup Z.eqb tag known_tags); [ reflexivity | intros [] ].
Qed.

Theorem deduce_get_tag_simple_is_sound : deduce_get_tag_simple_sound.
Proof.
  intros statics vars v is_int immediates get_tag blocks extensions is_unique
    tag fields Hsatisfied Hblock.
  rewrite variant_satisfied in Hsatisfied.
  destruct Hsatisfied
    as [(i & -> & _) | (tag' & fields' & Hblock' & _ & Hget_tag & Hblocks & _)];
    [ exfalso; exact (block_not_immediate _ _ _ _ Hblock) | ].
  rewrite Hblock in Hblock'. injection Hblock' as <- <-.
  assert (Hvar :
    match
      match get_tag with
      | Some var => Ok (Var var)
      | None => @Unknown simple
      end
    with
    | Bottom => False
    | Ok simple =>
      eval_simple vars simple = Some (Value_const (Naked_immediate tag))
    | Unknown => True
    end).
  { destruct get_tag as [var | ]; [ exact Hget_tag | exact I ]. }
  unfold deduce_get_tag_simple, deduce_get_tag.
  destruct blocks as [[known_tags [other | ] alloc_mode] | ];
    [ exact Hvar | | exact Hvar ].
  unfold row_like_for_blocks_all_tags. cbv beta iota.
  pose proof (row_like_tag_among _ _ _ _ _ _ Hblocks) as Hamong.
  unfold row_like_block_case in *.
  destruct (Keyed.is_empty (Keyed.domain Z.eqb known_tags)) eqn:Hempty.
  - apply (keyed_is_empty_among Z Z.eqb Z.eqb_eq) with (key := tag) in Hempty.
    exact (eq_true_false_abs _ Hamong Hempty).
  - destruct (Keyed.get_singleton Z.eqb (Keyed.domain Z.eqb known_tags))
      as [tag' | ] eqn:Hsingleton; [ | exact Hvar ].
    pose proof
      (proj1 (keyed_get_singleton Z Z.eqb Z.eqb_eq tag' _) Hsingleton tag)
      as Heq.
    rewrite Heq in Hamong. apply Z.eqb_eq in Hamong. subst tag'.
    reflexivity.
Qed.

(* ======================================================================== *)
(* The interface: what a growing state keeps                                *)
(* ======================================================================== *)

Section Traversal.

Context (typing_env_well_formed : Typing_env.t -> Prop).

Context {state : Type}
  (joined_env : state -> Index.t -> option Typing_env.t)
  (definitions_of_existentials :
     state -> finite_map (Simples_in_joined_envs.t * flambda_kind))
  (kind_in_target_env : state -> variable -> option flambda_kind)
  (state_valid : state -> Prop)
  (state_kinded : state -> Prop).

Local Abbreviation envs_well_formed :=
  (joined_envs_well_formed typing_env_well_formed joined_env).
Local Abbreviation envs_kinded := (joined_envs_kinded joined_env).
Local Abbreviation grows :=
  (state_grows joined_env definitions_of_existentials kind_in_target_env).
Local Abbreviation extends :=
  (extends_input joined_env definitions_of_existentials).
Local Abbreviation args_in_scope := (join_args_in_scope joined_env).
Local Abbreviation exists_in_target :=
  (exists_in_target_env kind_in_target_env).
Local Abbreviation in_target := (answer_in_target kind_in_target_env).
Local Abbreviation kinded_in_target :=
  (answer_kinded_in_target kind_in_target_env).
Local Abbreviation of_kind_in_target :=
  (simple_of_kind_in_target kind_in_target_env).
Local Abbreviation step_sound :=
  (join_step_sound typing_env_well_formed joined_env
     definitions_of_existentials kind_in_target_env state_valid state_kinded).

Lemma grows_refl (s : state) : grows s s.
Proof. repeat split; auto. Qed.

Lemma grows_trans (s s' s'' : state) :
  grows s s' -> grows s' s'' -> grows s s''.
Proof.
  intros (Henv & Hdefs & Hkinds) (Henv' & Hdefs' & Hkinds').
  repeat split.
  - intros index. rewrite Henv'. apply Henv.
  - intros x definition Hx. apply Hdefs', Hdefs, Hx.
  - intros x kind Hx. apply Hkinds', Hkinds, Hx.
Qed.

Lemma grows_joined_env (s s' : state) (index : Index.t) :
  grows s s' -> joined_env s' index = joined_env s index.
Proof. intros (Henv & _). apply Henv. Qed.

Lemma grows_well_formed (s s' : state) :
  grows s s' -> envs_well_formed s -> envs_well_formed s'.
Proof.
  intros (Henv & _) Hwf index use Huse. rewrite Henv in Huse.
  exact (Hwf index use Huse).
Qed.

Lemma grows_kinded (s s' : state) :
  grows s s' -> envs_kinded s -> envs_kinded s'.
Proof.
  intros (Henv & _) Hkinded index use Huse. rewrite Henv in Huse.
  exact (Hkinded index use Huse).
Qed.

Lemma grows_args_in_scope {X : Type} (P : Typing_env.t -> X -> Prop)
    (s s' : state) (args : list (Index.t * X)) :
  grows s s' -> args_in_scope P s args -> args_in_scope P s' args.
Proof.
  intros (Henv & _) Hargs index x Hin.
  destruct (Hargs index x Hin) as (use & Huse & HP).
  exists use. rewrite Henv. split; assumption.
Qed.

(* A valuation that extends an input at a later state extends it at an
   earlier one. *)
Lemma grows_extends (s s' : state) (index : Index.t)
    (valuation valuation' : env) :
  grows s s' ->
  extends s' index valuation valuation' ->
  extends s index valuation valuation'.
Proof.
  intros (Henv & Hdefs & _) (use & Huse & Hagrees & Hholds).
  exists use. rewrite <- Henv. split; [ exact Huse | ].
  split; [ exact Hagrees | ].
  intros x simples kind simple v Hx.
  apply (Hholds x simples kind simple v). apply Hdefs. exact Hx.
Qed.

Lemma grows_exists (s s' : state) (x : variable) :
  grows s s' -> exists_in_target s x = true -> exists_in_target s' x = true.
Proof.
  intros (_ & _ & Hkinds). unfold exists_in_target_env.
  destruct (kind_in_target_env s x) as [kind | ] eqn:Hkind; [ | discriminate ].
  rewrite (Hkinds x kind Hkind). reflexivity.
Qed.

Lemma grows_in_target {Y : Type} (variables_of : Y -> list variable)
    (s s' : state) (y : Y) :
  grows s s' -> in_target variables_of s y -> in_target variables_of s' y.
Proof.
  intros Hgrows Htarget x Hx. exact (grows_exists _ _ _ Hgrows (Htarget x Hx)).
Qed.

Lemma grows_of_kind_in_target (s s' : state) (simple : simple)
    (kind : flambda_kind) :
  grows s s' ->
  of_kind_in_target s simple kind -> of_kind_in_target s' simple kind.
Proof.
  intros (_ & _ & Hkinds). destruct simple as [x | sym | c]; simpl; auto.
Qed.

Lemma grows_kinded_in_target {Y : Type}
    (aliases_of : Y -> list (simple * flambda_kind)) (s s' : state) (y : Y) :
  grows s s' ->
  kinded_in_target aliases_of s y -> kinded_in_target aliases_of s' y.
Proof.
  intros Hgrows Hkinded simple kind Hin.
  exact (grows_of_kind_in_target _ _ _ _ Hgrows (Hkinded simple kind Hin)).
Qed.

(* ======================================================================== *)
(* [n_way_join_unknown]                                                     *)
(* ======================================================================== *)

Theorem n_way_join_unknown_is_sound :
  n_way_join_unknown_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded.
Proof.
  intros A B variables_of_arg aliases_of_arg variables_of_answer
    aliases_of_answer bound n_way_join_contents Hcontents s s' args answer
    Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_unknown in Hstep.
  destruct (known_contents [] args) as [contents | ] eqn:Hknown.
  - destruct (known_contents_spec args [] contents Hknown)
      as (Hfst & Hfrom & Hto & _).
    assert (Hdistinct' : join_args_distinct contents).
    { unfold join_args_distinct. rewrite Hfst, app_nil_r.
      apply NoDup_rev. exact Hdistinct. }
    assert (Hargs' :
      args_in_scope (arg_in_scope_and_kinded variables_of_arg aliases_of_arg)
        s contents).
    { intros index a Hin. destruct (Hfrom index a Hin) as [[] | Hin'].
      exact (Hargs index (Or_unknown.Known a) Hin'). }
    destruct
      (Hcontents s s' contents answer Hvalid Hwf Hkinded Hdistinct' Hargs'
         Hstep)
      as (Hvalid' & Hgrows & Htarget & Hbound & Hkinds).
    split; [ exact Hvalid' | ]. split; [ exact Hgrows | ].
    split; [ exact Htarget | ]. split; [ | exact Hkinds ].
    intros index x use statics valuation valuation' Hin Huse Hsatisfied
      Hextends.
    destruct (Hto index x Hin) as (a & -> & Hin').
    specialize
      (Hbound index a use statics valuation valuation' Hin' Huse Hsatisfied
         Hextends).
    destruct answer; exact Hbound.
  - injection Hstep as <- <-.
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ].
    split.
    + intros index x use statics valuation valuation' _ _ _ _.
      destruct x; exact I.
    + intros Hk. split; [ exact Hk | intros simple kind [] ].
Qed.

(* ======================================================================== *)
(* The functions that call the join of [Simple]s                            *)
(* ======================================================================== *)

Section Simples.

Context
  (n_way_join_simples :
     state -> flambda_kind -> list (Index.t * simple)
     -> option (Or_bottom.t simple * state)).

Hypothesis Hsimples :
  n_way_join_simples_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    n_way_join_simples.

Theorem n_way_join_relation_simples_is_sound :
  n_way_join_relation_simples_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    n_way_join_simples.
Proof.
  intros s s' simples x Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_relation_simples in Hstep.
  destruct (n_way_join_simples s (Naked_number Kind_naked_immediate) simples)
    as [[joined s1] | ] eqn:Hjoin; [ | discriminate ].
  assert (Hkinds :
    args_in_scope
      (fun use simple =>
         simple_of_kind use simple (Naked_number Kind_naked_immediate))
      s simples).
  { intros index simple Hin.
    destruct (Hargs index simple Hin) as (use & Huse & _ & Haliases).
    exists use. split; [ exact Huse | ]. apply Haliases. left. reflexivity. }
  destruct
    (Hsimples s s1 _ simples joined Hvalid Hwf Hkinded Hdistinct Hkinds Hjoin)
    as (Hvalid1 & Hgrows & _ & _ & Hok & Hkinded1).
  assert (Hnone :
    Some (None, s1) = Some (x, s') ->
    state_valid s' ∧ grows s s'
    ∧ in_target free_variables_of_option s' x
    ∧ (∀ (index : Index.t) (simple : FlambdaModel.simple)
         (use : Typing_env.t) (statics : static_env)
         (valuation valuation' : env),
         In (index, simple) simples ->
         joined_env s' index = Some use ->
         typing_env_satisfied_strictly statics valuation use ->
         extends s' index valuation valuation' ->
         ∀ n : Z,
           eval_simple valuation simple
           = Some (Value_const (Naked_immediate n)) ->
           variable_is valuation' x n)
    ∧ (state_kinded s ->
       state_kinded s' ∧ kinded_in_target aliases_of_relation s' x)).
  { intros [= <- <-].
    split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
    split; [ intros y [] | ]. split; [ intros; exact I | ].
    intros Hk. split; [ apply Hkinded1; exact Hk | intros simple kind [] ]. }
  destruct joined as [[var | sym | c] | ];
    [ | apply Hnone; exact Hstep .. ].
  injection Hstep as <- <-.
  destruct (Hok (Var var) eq_refl) as (Htarget & Hbound).
  split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
  split; [ exact Htarget | ].
  split.
  - intros index simple use statics valuation valuation' Hin Huse Hsatisfied
      Hextends n Heval.
    exact
      (Hbound index simple use statics valuation valuation' _ Hin Huse
         Hsatisfied Hextends Heval).
  - intros Hk. split; [ apply Hkinded1; exact Hk | ].
    intros simple kind [[= <- <-] | []].
    apply Hkinded1; [ exact Hk | reflexivity ].
Qed.

(* What the [Simple] of a head says of null, for [is_null_simples]. *)
Definition is_null_simple_of (head : head_of_kind_value) (simple : simple)
    : Prop :=
  match is_null_of_head head with
  | Not_null => simple = untagged_const_bool false
  | Maybe_null (Some x) => simple = Var x
  | Maybe_null None => False
  end.

Lemma is_null_simples_spec (heads : list (Index.t * head_of_kind_value)) :
  ∀ simples : list (Index.t * simple),
    is_null_simples heads = Some simples ->
    map fst simples = map fst heads
    ∧ (∀ (index : Index.t) (head : head_of_kind_value),
         In (index, head) heads ->
         ∃ simple : simple,
           In (index, simple) simples ∧ is_null_simple_of head simple)
    ∧ ∀ (index : Index.t) (simple : simple),
        In (index, simple) simples ->
        ∃ head : head_of_kind_value,
          In (index, head) heads ∧ is_null_simple_of head simple.
Proof.
  induction heads as [ | [id [non_null is_null]] heads IH];
    intros simples Hsimples'; simpl in Hsimples'.
  - injection Hsimples' as <-. repeat split; [ intros ? ? [] | intros ? ? [] ].
  - assert (Hcons :
      ∀ simple : simple,
        is_null_simple_of (Head_of_kind_value non_null is_null) simple ->
        option_map (cons (id, simple)) (is_null_simples heads) = Some simples ->
        map fst simples = map fst ((id, Head_of_kind_value non_null is_null)
                                   :: heads)
        ∧ (∀ (index : Index.t) (head : head_of_kind_value),
             In (index, head)
               ((id, Head_of_kind_value non_null is_null) :: heads) ->
             ∃ simple : FlambdaModel.simple,
               In (index, simple) simples ∧ is_null_simple_of head simple)
        ∧ ∀ (index : Index.t) (simple : FlambdaModel.simple),
            In (index, simple) simples ->
            ∃ head : head_of_kind_value,
              In (index, head)
                ((id, Head_of_kind_value non_null is_null) :: heads)
              ∧ is_null_simple_of head simple).
    { intros simple Hsimple Hrest.
      destruct (is_null_simples heads) as [rest | ]; [ | discriminate ].
      injection Hrest as <-.
      destruct (IH rest eq_refl) as (Hfst & Hto & Hfrom).
      repeat split.
      - simpl. rewrite Hfst. reflexivity.
      - intros index head [[= <- <-] | Hin].
        + exists simple. split; [ left; reflexivity | exact Hsimple ].
        + destruct (Hto index head Hin) as (simple' & Hin' & Hsimple').
          exists simple'. split; [ right; exact Hin' | exact Hsimple' ].
      - intros index simple' [[= <- <-] | Hin].
        + eexists. split; [ left; reflexivity | exact Hsimple ].
        + destruct (Hfrom index simple' Hin) as (head & Hin' & Hsimple').
          exists head. split; [ right; exact Hin' | exact Hsimple' ]. }
    destruct is_null as [ | [x | ]].
    + exact (Hcons _ eq_refl Hsimples').
    + exact (Hcons _ eq_refl Hsimples').
    + discriminate.
Qed.

Theorem n_way_join_is_null_is_sound :
  n_way_join_is_null_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    n_way_join_simples.
Proof.
  intros s s' heads is_null Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_is_null in Hstep.
  (* The answer that says nothing. *)
  assert (Hnone :
    ∀ s1 : state,
      state_valid s1 -> grows s s1 -> (state_kinded s -> state_kinded s1) ->
      Some (Maybe_null None, s1) = Some (is_null, s') ->
      state_valid s' ∧ grows s s'
      ∧ in_target variables_of_is_null s' is_null
      ∧ (∀ (index : Index.t) (head : head_of_kind_value)
           (use : Typing_env.t) (statics : static_env)
           (valuation valuation' : env),
           In (index, head) heads ->
           joined_env s' index = Some use ->
           typing_env_satisfied_strictly statics valuation use ->
           extends s' index valuation valuation' ->
           ∀ null : bool,
             is_null_says valuation (is_null_of_head head) null ->
             is_null_says valuation' is_null null)
      ∧ (state_kinded s ->
         state_kinded s' ∧ kinded_in_target aliases_of_is_null s' is_null)).
  { intros s1 Hvalid1 Hgrows Hk [= <- <-].
    split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
    split; [ intros y [] | ]. split; [ intros; exact I | ].
    intros Hk'. split; [ exact (Hk Hk') | intros simple kind [] ]. }
  destruct (is_null_simples heads) as [simples | ] eqn:Hsimples';
    [ | exact (Hnone s Hvalid (grows_refl s) (fun H => H) Hstep) ].
  destruct (is_null_simples_spec heads simples Hsimples')
    as (Hfst & Hto & Hfrom).
  destruct (n_way_join_simples s (Naked_number Kind_naked_immediate) simples)
    as [[joined s1] | ] eqn:Hjoin; [ | discriminate ].
  assert (Hdistinct' : join_args_distinct simples).
  { unfold join_args_distinct. rewrite Hfst. exact Hdistinct. }
  assert (Hkinds :
    args_in_scope
      (fun use simple =>
         simple_of_kind use simple (Naked_number Kind_naked_immediate))
      s simples).
  { intros index simple Hin.
    destruct (Hfrom index simple Hin) as ([non_null is_null'] & Hin' & Hsimple).
    destruct (Hargs index _ Hin') as (use & Huse & _ & Haliases).
    exists use. split; [ exact Huse | ].
    unfold is_null_simple_of in Hsimple. simpl in Hsimple.
    destruct is_null' as [ | [x | ]]; [ | | contradiction ]; subst simple.
    - reflexivity.
    - apply Haliases. simpl. apply in_or_app. right. left. reflexivity. }
  destruct
    (Hsimples s s1 _ simples joined Hvalid Hwf Hkinded Hdistinct' Hkinds Hjoin)
    as (Hvalid1 & Hgrows & _ & _ & Hok & Hkinded1).
  assert (Hk1 : state_kinded s -> state_kinded s1).
  { intros Hk. apply Hkinded1. exact Hk. }
  (* What the join of the [Simple]s gives for a head. *)
  assert (Hjoined :
    ∀ (joined' : simple) (index : Index.t) (head : head_of_kind_value)
      (use : Typing_env.t) (statics : static_env) (valuation valuation' : env)
      (null : bool),
      joined = Or_bottom.Ok joined' ->
      In (index, head) heads ->
      joined_env s1 index = Some use ->
      typing_env_satisfied_strictly statics valuation use ->
      extends s1 index valuation valuation' ->
      is_null_says valuation (is_null_of_head head) null ->
      eval_simple valuation' joined'
      = Some (Value_const (Naked_immediate (if null then 1%Z else 0%Z)))).
  { intros joined' index head use statics valuation valuation' null Hjoined'
      Hin Huse Hsatisfied Hextends Hsays.
    destruct (Hok joined' Hjoined') as (_ & Hbound).
    destruct (Hto index head Hin) as (simple & Hin' & Hsimple).
    apply
      (Hbound index simple use statics valuation valuation' _ Hin' Huse
         Hsatisfied Hextends).
    unfold is_null_simple_of in Hsimple.
    destruct (is_null_of_head head) as [ | [x | ]];
      [ | | contradiction ]; subst simple.
    - simpl in Hsays. subst null. reflexivity.
    - exact Hsays. }
  destruct joined as [[var | sym | c] | ].
  - (* A variable. *)
    injection Hstep as <- <-.
    destruct (Hok (Var var) eq_refl) as (Htarget & _).
    split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
    split; [ exact Htarget | ].
    split.
    + intros index head use statics valuation valuation' Hin Huse Hsatisfied
        Hextends null Hsays.
      exact
        (Hjoined _ index head use statics valuation valuation' null eq_refl
           Hin Huse Hsatisfied Hextends Hsays).
    + intros Hk. split; [ exact (Hk1 Hk) | ].
      intros simple kind [[= <- <-] | []].
      apply Hkinded1; [ exact Hk | reflexivity ].
  - discriminate.
  - (* A constant. *)
    assert (Hfalse :
      ∀ i : Z,
        c = Naked_immediate i -> Z.eqb i 0 = true ->
        Some (Not_null, s1) = Some (is_null, s') ->
        state_valid s' ∧ grows s s'
        ∧ in_target variables_of_is_null s' is_null
        ∧ (∀ (index : Index.t) (head : head_of_kind_value)
             (use : Typing_env.t) (statics : static_env)
             (valuation valuation' : env),
             In (index, head) heads ->
             joined_env s' index = Some use ->
             typing_env_satisfied_strictly statics valuation use ->
             extends s' index valuation valuation' ->
             ∀ null : bool,
               is_null_says valuation (is_null_of_head head) null ->
               is_null_says valuation' is_null null)
        ∧ (state_kinded s ->
           state_kinded s' ∧ kinded_in_target aliases_of_is_null s' is_null)).
    { intros i -> Hzero [= <- <-]. apply Z.eqb_eq in Hzero. subst i.
      split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
      split; [ intros y [] | ].
      split.
      - intros index head use statics valuation valuation' Hin Huse
          Hsatisfied Hextends null Hsays.
        pose proof
          (Hjoined _ index head use statics valuation valuation' null eq_refl
             Hin Huse Hsatisfied Hextends Hsays) as Heval.
        simpl in Heval. destruct null; [ discriminate | reflexivity ].
      - intros Hk. split; [ exact (Hk1 Hk) | intros simple kind [] ]. }
    destruct c as [i | | | | | | | | | | | | | | ];
      try exact (Hnone s1 Hvalid1 Hgrows Hk1 Hstep).
    destruct (Z.eqb i 0) eqn:Hzero.
    + exact (Hfalse i eq_refl Hzero Hstep).
    + exact (Hnone s1 Hvalid1 Hgrows Hk1 Hstep).
  - exact (Hnone s1 Hvalid1 Hgrows Hk1 Hstep).
Qed.

End Simples.

(* ======================================================================== *)
(* Numbers                                                                  *)
(* ======================================================================== *)

Lemma fold_union_keeps (ts : list (Index.t * list Z)) :
  ∀ (acc : list Z) (n : Z),
    n ∈ acc ->
    n ∈ List.fold_left (fun t1 t2 => numbers_union t1 (snd t2)) ts acc.
Proof.
  induction ts as [ | [id t] ts IH]; intros acc n Hin; simpl; [ exact Hin | ].
  apply IH. apply numbers_union_in. left. exact Hin.
Qed.

Lemma fold_union_in (ts : list (Index.t * list Z)) :
  ∀ (acc : list Z) (index : Index.t) (t : list Z) (n : Z),
    In (index, t) ts -> n ∈ t ->
    n ∈ List.fold_left (fun t1 t2 => numbers_union t1 (snd t2)) ts acc.
Proof.
  induction ts as [ | [id t'] ts IH]; intros acc index t n Hin Hn; simpl;
    [ destruct Hin | ].
  destruct Hin as [[= <- <-] | Hin].
  - apply fold_union_keeps. apply numbers_union_in. right. exact Hn.
  - exact (IH _ index t n Hin Hn).
Qed.

Theorem n_way_join_head_of_kind_naked_numbers_is_sound :
  n_way_join_head_of_kind_naked_numbers_sound typing_env_well_formed
    joined_env definitions_of_existentials kind_in_target_env state_valid
    state_kinded.
Proof.
  intros k s s' args answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  destruct args as [ | [id1 head1] heads]; [ discriminate | ].
  injection Hstep as <- <-.
  split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
  split; [ intros x [] | ].
  split.
  - intros index numbers use statics valuation valuation' Hin _ _ _ v
      (c & n & Hv & Hkind & Hnumber & Hn).
    exists c, n. repeat split; try assumption. simpl.
    destruct Hin as [[= <- <-] | Hin].
    + apply fold_union_keeps. exact Hn.
    + exact (fold_union_in _ _ index numbers n Hin Hn).
  - intros Hk. split; [ exact Hk | intros simple kind [] ].
Qed.

Section Reduce.

Context
  (reduce_head_of_kind_naked_immediate :
     Typing_env.t -> head_of_kind_naked_immediate
     -> Or_bottom.t head_of_kind_naked_immediate).

Hypothesis Hreduce :
  reduce_head_of_kind_naked_immediate_sound
    reduce_head_of_kind_naked_immediate.

(* The numbers that the fold answers hold those that it was given to
   start with, and every number that has one of the heads. *)
Lemma join_naked_immediates_spec (s : state)
    (heads : list (Index.t * head_of_kind_naked_immediate)) :
  ∀ (immediates : Or_unknown.t (list Z)) (imms : list Z),
    join_naked_immediates joined_env reduce_head_of_kind_naked_immediate s
      immediates heads
    = Some (Or_unknown.Known imms) ->
    (∃ imms0 : list Z,
       immediates = Or_unknown.Known imms0 ∧ ∀ n : Z, n ∈ imms0 -> n ∈ imms)
    ∧ ∀ (index : Index.t) (head : head_of_kind_naked_immediate)
        (use : Typing_env.t) (statics : static_env) (valuation : env)
        (v : value),
        In (index, head) heads ->
        joined_env s index = Some use ->
        typing_env_satisfied_strictly statics valuation use ->
        head_of_kind_naked_immediate_satisfied statics valuation v head ->
        ∃ n : Z, v = Value_const (Naked_immediate n) ∧ n ∈ imms.
Proof.
  induction heads as [ | [id2 head2] heads IH]; intros immediates imms Hjoin;
    simpl in Hjoin.
  - injection Hjoin as ->. split; [ exists imms; auto | intros ? ? ? ? ? ? [] ].
  - destruct (joined_env s id2) as [tenv | ] eqn:Htenv; [ | discriminate ].
    destruct (reduce_head_of_kind_naked_immediate tenv head2)
      as [head2' | ] eqn:Hreduced.
    + destruct (IH _ imms Hjoin) as ((imms0' & Himms0' & Hkeeps) & Hheads).
      destruct immediates as [imms0 | ]; [ | discriminate ].
      destruct (naked_immediates head2') as [imms2 | ] eqn:Himms2;
        [ | discriminate ].
      injection Himms0' as <-.
      split.
      * exists imms0. split; [ reflexivity | ].
        intros n Hn. apply Hkeeps, numbers_union_in. left. exact Hn.
      * intros index head use statics valuation v [[= <- <-] | Hin] Huse
          Hsatisfied Hhead.
        -- rewrite Htenv in Huse. injection Huse as <-.
           destruct (Hreduce tenv statics valuation v head2 Hsatisfied Hhead)
             as (head' & Hhead' & n & Hv & Hn & _).
           rewrite Hreduced in Hhead'. injection Hhead' as <-.
           rewrite Himms2 in Hn.
           exists n. split; [ exact Hv | ].
           apply Hkeeps, numbers_union_in. right. exact Hn.
        -- exact (Hheads index head use statics valuation v Hin Huse
                    Hsatisfied Hhead).
    + destruct (IH _ imms Hjoin) as (Himms0 & Hheads).
      split; [ exact Himms0 | ].
      intros index head use statics valuation v [[= <- <-] | Hin] Huse
        Hsatisfied Hhead.
      * rewrite Htenv in Huse. injection Huse as <-.
        destruct (Hreduce tenv statics valuation v head2 Hsatisfied Hhead)
          as (head' & Hhead' & _).
        congruence.
      * exact (Hheads index head use statics valuation v Hin Huse Hsatisfied
                 Hhead).
Qed.

Theorem n_way_join_head_of_kind_naked_immediate_is_sound :
  n_way_join_head_of_kind_naked_immediate_sound typing_env_well_formed
    joined_env definitions_of_existentials kind_in_target_env state_valid
    state_kinded reduce_head_of_kind_naked_immediate.
Proof.
  intros s s' heads answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_head_of_kind_naked_immediate in Hstep.
  destruct
    (join_naked_immediates joined_env reduce_head_of_kind_naked_immediate s
       (Or_unknown.Known []) heads)
    as [[imms | ] | ] eqn:Hjoin; [ | | discriminate ].
  - cbv beta iota in Hstep.
    destruct (Keyed.is_empty imms); [ discriminate | ].
    injection Hstep as <- <-.
    destruct (join_naked_immediates_spec s heads _ _ Hjoin) as (_ & Hheads).
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ].
    split.
    + intros index head use statics valuation valuation' Hin Huse Hsatisfied
        _ v Hhead.
      destruct (Hheads index head use statics valuation v Hin Huse Hsatisfied
                  Hhead)
        as (n & Hv & Hn).
      exists n. split; [ exact Hv | ]. split; [ exact Hn | intros ? ? [] ].
    + intros Hk. split; [ exact Hk | intros simple kind [] ].
  - injection Hstep as <- <-.
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ].
    split; [ intros; exact I | ].
    intros Hk. split; [ exact Hk | intros simple kind [] ].
Qed.

End Reduce.

(* ======================================================================== *)
(* Environment extensions                                                   *)
(* ======================================================================== *)

Section Extension.

Context
  (join_env_n_way_join_env_extension :
     state -> list (Index.t * env_extension)
     -> option (Or_bottom.t (env_extension * state))).

Hypothesis Hextension :
  n_way_join_env_extension_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    join_env_n_way_join_env_extension.

Theorem n_way_join_env_extension_is_sound :
  n_way_join_env_extension_sound_here typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    join_env_n_way_join_env_extension.
Proof.
  intros s s' extensions answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_env_extension in Hstep.
  destruct (join_env_n_way_join_env_extension s extensions)
    as [joined | ] eqn:Hjoin; [ | discriminate ].
  assert (Hscope :
    args_in_scope env_extension_in_scope s extensions).
  { intros index extension Hin.
    destruct (Hargs index extension Hin) as (use & Huse & Hknown & _).
    exists use. split; [ exact Huse | exact Hknown ]. }
  assert (Hkinds :
    args_in_scope env_extension_kinded s extensions).
  { intros index extension Hin.
    destruct (Hargs index extension Hin) as (use & Huse & _ & Haliases).
    exists use. split; [ exact Huse | exact Haliases ]. }
  destruct
    (Hextension s extensions joined Hvalid Hwf Hkinded Hdistinct Hscope Hjoin)
    as (Hbottom & Hok & Hkinded').
  destruct joined as [[joined s1] | ].
  - injection Hstep as <- <-.
    destruct (Hok joined s1 eq_refl) as (Hvalid1 & Hgrows & Htarget & Hbound).
    split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
    split; [ exact Htarget | ].
    split.
    + intros index extension use statics valuation valuation' Hin Huse
        Hsatisfied Hextends Hholds.
      exact
        (Hbound index extension use statics valuation valuation' Hin Huse
           Hsatisfied Hextends Hholds).
    + intros Hk. exact (Hkinded' Hk Hkinds joined s1 eq_refl).
  - injection Hstep as <- <-. rewrite (Hbottom eq_refl).
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ].
    split; [ intros ? ? ? ? ? ? [] | ].
    intros Hk. split; [ exact Hk | intros simple kind [] ].
Qed.

End Extension.

End Traversal.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

Theorem flat_heads_sound : flat_heads_sound_statement.
Proof.
  intros typing_env_well_formed state joined_env definitions_of_existentials
    kind_in_target_env state_valid state_kinded n_way_join_simples
    import_type join_env_n_way_join_env_extension
    reduce_head_of_kind_naked_immediate
    (_ & Hsimples & _ & Hextension) Hreduce.
  split; [ apply n_way_join_unknown_is_sound | ].
  split; [ apply n_way_join_relation_simples_is_sound; exact Hsimples | ].
  split; [ apply n_way_join_is_null_is_sound; exact Hsimples | ].
  split;
    [ apply n_way_join_head_of_kind_naked_immediate_is_sound; exact Hreduce
    | ].
  split; [ apply n_way_join_head_of_kind_naked_numbers_is_sound | ].
  split; [ apply n_way_join_env_extension_is_sound; exact Hextension | ].
  split;
    [ exact deduce_is_int_simple_is_sound
    | exact deduce_get_tag_simple_is_sound ].
Qed.
