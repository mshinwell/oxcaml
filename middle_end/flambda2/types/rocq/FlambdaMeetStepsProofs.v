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



(* Proofs of the statements of FlambdaMeetStepsSpec.v. Nothing here
   needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaEnvAliasesSpec
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvProofs
  FlambdaMeetGrammar FlambdaExpandHead FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec FlambdaMeetStepsSpec.
Import ListNotations.

(* ======================================================================== *)
(* The relations of a naked immediate, reduced                              *)
(* ======================================================================== *)

Lemma relation_eqb_eq : decides_equality relation_eqb.
Proof.
  intros r r'. destruct r, r'; cbn; split; intros H; try reflexivity;
    discriminate.
Qed.

Lemma inverse_relation_eqb_eq : decides_equality inverse_relation_eqb.
Proof.
  intros [r n] [r' n']. unfold inverse_relation_eqb. cbn [fst snd].
  rewrite andb_true_iff, (relation_eqb_eq r r'), (name_eqb_eq n n').
  split.
  - intros [-> ->]. reflexivity.
  - intros H. inversion H. split; reflexivity.
Qed.

(* What the fold of [reduce_head_of_kind_naked_immediate] keeps: the
   number is among the numbers, and each relation kept relates the
   value of its name to the number. *)
Definition reduce_acc_holds (statics : static_env) (valuation : env) (i : Z)
    (acc : reduce_acc) : Prop :=
  match reduce_imms acc with
  | Or_unknown.Unknown => True
  | Or_unknown.Known numbers => i ∈ numbers
  end
  ∧ ∀ (relation : Relation.t) (n : name),
      (relation, n) ∈ reduce_relations acc ->
      ∃ w : value,
        value_of_name valuation n = Some w
        ∧ relation_holds statics relation w i.

Lemma eval_simple_const (valuation : env) (c : const) :
  eval_simple valuation (Const c) = Some (Value_const c).
Proof. reflexivity. Qed.

Theorem reduce_head_of_kind_naked_immediate_sound
    : reduce_head_of_kind_naked_immediate_sound_statement.
Proof.
  intros Hexact statics valuation tenv head v Henv (i & Hv & Himms & Hrels).
  unfold reduce_head_of_kind_naked_immediate.
  set (step := fun (state : Or_bottom.t reduce_acc)
                   (inverse : Relation.t * name) => _).
  assert (Hfold :
    ∀ (relations : list (Relation.t * name)) (acc : reduce_acc),
      (∀ (relation : Relation.t) (n : name),
         (relation, n) ∈ relations ->
         ∃ w : value,
           value_of_name valuation n = Some w
           ∧ relation_holds statics relation w i) ->
      reduce_acc_holds statics valuation i acc ->
      ∃ acc' : reduce_acc,
        List.fold_left step relations (Or_bottom.Ok acc) = Or_bottom.Ok acc'
        ∧ reduce_acc_holds statics valuation i acc').
  { induction relations as [ | [relation n] relations IH ];
      intros acc Hall Hacc.
    - exists acc. cbn. auto.
    - cbn [List.fold_left].
      destruct (Hall relation n (or_introl eq_refl)) as (w & Hw & Hholds).
      assert (Hrest :
        ∀ (relation : Relation.t) (n : name),
          (relation, n) ∈ relations ->
          ∃ w : value,
            value_of_name valuation n = Some w
            ∧ relation_holds statics relation w i).
      { intros relation' n' Hin. apply Hall. right. exact Hin. }
      assert (Hcanonical :=
        canonical_ignoring_name_mode_satisfied (fun _ => False) statics
          valuation tenv (simple_of_name n) Henv).
      unfold value_of_name in Hw. rewrite Hw in Hcanonical.
      destruct Hacc as [Hnumbers Hkept].
      assert (Hstep :
        ∃ acc1 : reduce_acc,
          step (Or_bottom.Ok acc) (relation, n) = Or_bottom.Ok acc1
          ∧ reduce_acc_holds statics valuation i acc1).
      { unfold step. cbn [fst snd].
        destruct (Typing_env.get_canonical_simple_ignoring_name_mode tenv
                    (simple_of_name n)) as [ x | s | c ] eqn:Hcan.
        - eexists. split; [ reflexivity | ].
          split; [ exact Hnumbers | ]. cbn [reduce_relations].
          intros relation' n' [ Heq | Hin ]; [ | exact (Hkept _ _ Hin) ].
          inversion Heq; subst. exists w. split; [ exact Hcanonical | ].
          exact Hholds.
        - eexists. split; [ reflexivity | ].
          split; [ exact Hnumbers | ]. cbn [reduce_relations].
          intros relation' n' [ Heq | Hin ]; [ | exact (Hkept _ _ Hin) ].
          inversion Heq; subst. exists w. split; [ exact Hcanonical | ].
          exact Hholds.
        - rewrite eval_simple_const in Hcanonical.
          injection Hcanonical as Hc. subst w.
          destruct (Relation.of_const relation c) as [ imm | ] eqn:Hconst.
          + assert (Himm : i = imm) by exact (Hexact _ _ _ _ _ Hholds Hconst).
            subst imm.
            destruct (reduce_imms acc) as [ numbers | ] eqn:Hreduce.
            * destruct (Keyed.same_keys_b Z.eqb [i] numbers).
              -- exists acc. split; [ reflexivity | ].
                 split; [ rewrite Hreduce; exact Hnumbers | exact Hkept ].
              -- assert (Hamong : Keyed.among Z.eqb i numbers = true).
                 { apply (keyed_among_in Z Z.eqb z_eqb_decides_equality).
                   exact Hnumbers. }
                 rewrite Hamong. cbn [negb].
                 eexists. split; [ reflexivity | ].
                 split; [ cbn; left; reflexivity | exact Hkept ].
            * eexists. split; [ reflexivity | ].
              split; [ cbn; left; reflexivity | exact Hkept ].
          + eexists. split; [ reflexivity | ].
            split; [ exact Hnumbers | exact Hkept ]. }
      destruct Hstep as (acc1 & Hstep & Hacc1).
      rewrite Hstep. exact (IH acc1 Hrest Hacc1). }
  destruct (Hfold (inverse_relations head)
              {| reduce_imms := naked_immediates head;
                 reduce_relations := [];
                 reduce_changed := false |}
              Hrels)
    as (acc & Hfolded & Hnumbers & Hkept).
  { split; [ exact Himms | ]. intros relation n []. }
  rewrite Hfolded.
  destruct (reduce_changed acc); cbn [negb].
  - unfold head_of_kind_naked_immediate_from_descr.
    assert (Hsatisfied :
      head_of_kind_naked_immediate_satisfied statics valuation v
        (Head_of_kind_naked_immediate (reduce_imms acc)
           (Keyed.dedup inverse_relation_eqb (rev (reduce_relations acc))))).
    { exists i. split; [ exact Hv | ]. split; [ exact Hnumbers | ].
      cbn [inverse_relations]. intros relation n Hin. apply Hkept.
      apply in_rev.
      apply (keyed_among_in _ inverse_relation_eqb inverse_relation_eqb_eq).
      rewrite <- (keyed_among_dedup _ inverse_relation_eqb
                    inverse_relation_eqb_eq).
      apply (keyed_among_in _ inverse_relation_eqb inverse_relation_eqb_eq).
      exact Hin. }
    destruct (reduce_imms acc) as [ [ | number numbers ] | ] eqn:Hreduce.
    + destruct Hnumbers.
    + eexists. split; [ reflexivity | exact Hsatisfied ].
    + eexists. split; [ reflexivity | exact Hsatisfied ].
  - exists head. split; [ reflexivity | ].
    exists i. split; [ exact Hv | ]. split; [ exact Himms | exact Hrels ].
Qed.

(* ======================================================================== *)
(* Extending an environment, and a valuation                                *)
(* ======================================================================== *)

Lemma keeps_names_refl (tenv : Typing_env.t) : keeps_names tenv tenv.
Proof.
  intros n ty binding_time_and_mode Hlookup. exists ty.
  split; [ exact Hlookup | reflexivity ].
Qed.

Lemma keeps_names_trans (tenv1 tenv2 tenv3 : Typing_env.t) :
  keeps_names tenv1 tenv2 -> keeps_names tenv2 tenv3 ->
  keeps_names tenv1 tenv3.
Proof.
  intros H12 H23 n ty binding_time_and_mode Hlookup.
  destruct (H12 n ty binding_time_and_mode Hlookup) as (ty2 & Hlookup2 & Hk2).
  destruct (H23 n ty2 binding_time_and_mode Hlookup2)
    as (ty3 & Hlookup3 & Hk3).
  exists ty3. split; [ exact Hlookup3 | congruence ].
Qed.

Lemma meet_env_extends_refl (menv : Meet_env.t) : meet_env_extends menv menv.
Proof.
  repeat split; try reflexivity.
  - intros x Hamong. exact Hamong.
  - apply keeps_names_refl.
Qed.

Lemma meet_env_extends_trans (menv1 menv2 menv3 : Meet_env.t) :
  meet_env_extends menv1 menv2 -> meet_env_extends menv2 menv3 ->
  meet_env_extends menv1 menv3.
Proof.
  intros (Hs12 & Hp12 & Hm12 & Hd12 & Ha12 & Hv12 & Hk12)
    (Hs23 & Hp23 & Hm23 & Hd23 & Ha23 & Hv23 & Hk23).
  repeat split; try congruence.
  - intros x Hamong. apply Hv23, Hv12, Hamong.
  - exact (keeps_names_trans _ _ _ Hk12 Hk23).
Qed.

(* A variable that an environment knows is known to one that keeps its
   names. *)
Lemma keeps_names_mem (tenv tenv' : Typing_env.t) (x : variable) :
  keeps_names tenv tenv' ->
  Typing_env.mem None tenv (Name_var x) = true ->
  Typing_env.mem None tenv' (Name_var x) = true.
Proof.
  intros Hkeeps. unfold Typing_env.mem.
  destruct (Keyed.lookup name_eqb (Name_var x)
              (Typing_env.names_to_types tenv))
    as [[ty binding_time_and_mode] | ] eqn:Hlookup; [ | discriminate ].
  intros _.
  destruct (Hkeeps _ _ _ Hlookup) as (ty' & Hlookup' & _).
  rewrite Hlookup'. reflexivity.
Qed.

Lemma extended_from_refl (tenv : Typing_env.t) (valuation : env) :
  extended_from tenv valuation valuation.
Proof. intros x _. reflexivity. Qed.

Lemma extended_from_trans (tenv tenv' : Typing_env.t)
    (valuation valuation' valuation'' : env) :
  keeps_names tenv tenv' ->
  extended_from tenv valuation valuation' ->
  extended_from tenv' valuation' valuation'' ->
  extended_from tenv valuation valuation''.
Proof.
  intros Hkeeps H1 H2 x Hmem.
  rewrite (H2 x (keeps_names_mem _ _ _ Hkeeps Hmem)). exact (H1 x Hmem).
Qed.

Lemma meet_env_extends_keeps_names (menv menv' : Meet_env.t) :
  meet_env_extends menv menv' ->
  keeps_names (Meet_env.typing_env menv) (Meet_env.typing_env menv').
Proof. intros (_ & _ & _ & _ & _ & _ & Hkeeps). exact Hkeeps. Qed.

(* ======================================================================== *)
(* The meet of a part of a type                                             *)
(* ======================================================================== *)

Lemma extract_value_map {A B : Type} (f : A -> B) (r : meet_return_value A)
    (a1 a2 : A) :
  extract_value (map_return_value f r) (f a1) (f a2)
  = f (extract_value r a1 a2).
Proof. destruct r; reflexivity. Qed.

Lemma map_result_ok_cases {A B : Type} (f : A -> B)
    (result : Meet_result.t A) (r' : meet_return_value B)
    (menv' : Meet_env.t) :
  map_result f result = Meet_result.Ok r' menv' ->
  ∃ r : meet_return_value A,
    result = Meet_result.Ok r menv' ∧ r' = map_return_value f r.
Proof.
  destruct result as [ r0 | r env ]; [ discriminate | ].
  destruct r; cbn; intros [= <- <-]; eexists; split; reflexivity.
Qed.

Lemma map_result_ok_eq {A B : Type} (f : A -> B) (r : meet_return_value A)
    (menv : Meet_env.t) :
  map_result f (Meet_result.Ok r menv)
  = Meet_result.Ok (map_return_value f r) menv.
Proof. destruct r; reflexivity. Qed.

Theorem map_result_ok : map_result_ok_statement.
Proof.
  intros type_well_formed A B fits_a satisfied_a fits_b satisfied_b f menv a1
    a2 result Hfits Hsatisfied [Hkeeps Hsound].
  split.
  - intros r' menv' Hresult.
    destruct (map_result_ok_cases f result r' menv' Hresult)
      as (r & -> & ->).
    destruct (Hkeeps r menv' eq_refl) as (Hextends & Henv & Ha).
    split; [ exact Hextends | ]. split; [ exact Henv | ].
    rewrite extract_value_map. apply Hfits, Ha.
  - intros statics valuation Henv H1 H2.
    apply Hsatisfied in H1. apply Hsatisfied in H2.
    destruct (Hsound statics valuation Henv H1 H2)
      as (r & menv' & valuation' & -> & Hextended & Henv' & Ha).
    exists (map_return_value f r), menv', valuation'.
    split; [ apply map_result_ok_eq | ]. split; [ exact Hextended | ].
    split; [ exact Henv' | ]. rewrite extract_value_map.
    apply Hsatisfied, Ha.
Qed.

(* A call that answers bottom is right if nothing has both inputs. *)
Lemma meet_call_ok_bottom (type_well_formed : flambda_type -> bool)
    {A : Type} (fits : Typing_env.t -> A -> Prop)
    (satisfied : static_env -> env -> A -> Prop) (menv : Meet_env.t)
    (a1 a2 : A) (r : meet_return_value unit) :
  (∀ (statics : static_env) (valuation : env),
     typing_env_satisfied_strictly statics valuation
       (Meet_env.typing_env menv) ->
     satisfied statics valuation a1 -> satisfied statics valuation a2 ->
     False) ->
  meet_call_ok type_well_formed fits satisfied menv a1 a2
    (Meet_result.Bottom r).
Proof.
  intros Hnone. split.
  - intros r' menv' Hresult. discriminate Hresult.
  - intros statics valuation Henv H1 H2.
    destruct (Hnone statics valuation Henv H1 H2).
Qed.

(* A call that answers in the environment that it was given is right if
   what it answers fits and is true where both inputs are. *)
Lemma meet_call_ok_same_env (type_well_formed : flambda_type -> bool)
    {A : Type} (fits : Typing_env.t -> A -> Prop)
    (satisfied : static_env -> env -> A -> Prop) (menv : Meet_env.t)
    (a1 a2 : A) (r : meet_return_value A) :
  typing_env_fits type_well_formed (Meet_env.typing_env menv) ->
  fits (Meet_env.typing_env menv) (extract_value r a1 a2) ->
  (∀ (statics : static_env) (valuation : env),
     satisfied statics valuation a1 -> satisfied statics valuation a2 ->
     satisfied statics valuation (extract_value r a1 a2)) ->
  meet_call_ok type_well_formed fits satisfied menv a1 a2
    (Meet_result.Ok r menv).
Proof.
  intros Henv Hfits Hsatisfied. split.
  - intros r' menv' [= <- <-].
    split; [ apply meet_env_extends_refl | ]. split; assumption.
  - intros statics valuation Hvaluation H1 H2.
    exists r, menv, valuation. split; [ reflexivity | ].
    split; [ apply extended_from_refl | ]. split; [ exact Hvaluation | ].
    exact (Hsatisfied statics valuation H1 H2).
Qed.

Theorem meet_unknown_ok : meet_unknown_ok_statement.
Proof.
  intros type_well_formed A fits satisfied meet_contents contents_is_bottom
    Hbottom Hok menv x1 x2 result Henv Hfits1 Hfits2 Hmeet.
  unfold meet_unknown in Hmeet.
  destruct x1 as [ c1 | ], x2 as [ c2 | ].
  - destruct (contents_is_bottom c1) eqn:Hb1;
      destruct (contents_is_bottom c2) eqn:Hb2; cbn in Hmeet.
    + injection Hmeet as <-. apply meet_call_ok_bottom.
      intros statics valuation _ H1 _. exact (Hbottom _ _ _ Hb1 H1).
    + injection Hmeet as <-. apply meet_call_ok_bottom.
      intros statics valuation _ H1 _. exact (Hbottom _ _ _ Hb1 H1).
    + injection Hmeet as <-. apply meet_call_ok_bottom.
      intros statics valuation _ _ H2. exact (Hbottom _ _ _ Hb2 H2).
    + destruct (meet_contents menv c1 c2) as [ result0 | ] eqn:Hcontents;
        [ | discriminate ].
      injection Hmeet as <-.
      apply (map_result_ok type_well_formed A (Or_unknown.t A) fits satisfied
               (or_unknown_fits fits) (or_unknown_satisfied satisfied)
               Or_unknown.Known menv c1 c2 result0).
      * intros tenv a Ha. exact Ha.
      * intros statics valuation a. reflexivity.
      * exact (Hok menv c1 c2 result0 Henv Hfits1 Hfits2 Hcontents).
  - destruct (contents_is_bottom c1) eqn:Hb1; injection Hmeet as <-.
    + apply meet_call_ok_bottom.
      intros statics valuation _ H1 _. exact (Hbottom _ _ _ Hb1 H1).
    + apply meet_call_ok_same_env; [ exact Henv | exact Hfits1 | ].
      intros statics valuation H1 _. exact H1.
  - destruct (contents_is_bottom c2) eqn:Hb2; injection Hmeet as <-.
    + apply meet_call_ok_bottom.
      intros statics valuation _ _ H2. exact (Hbottom _ _ _ Hb2 H2).
    + apply meet_call_ok_same_env; [ exact Henv | exact Hfits2 | ].
      intros statics valuation _ H2. exact H2.
  - injection Hmeet as <-.
    apply meet_call_ok_same_env; [ exact Henv | exact I | ].
    intros statics valuation _ _. exact I.
Qed.

(* What [combine_meet_return_values] answers for a pair: each part of
   it is a part of an input or what the meet of that part answered. *)
Lemma combine_extract {A B C : Type} (rebuild : A -> B -> C)
    (res_a : meet_return_value A) (res_b : meet_return_value B)
    (left_a right_a : A) (left_b right_b : B) :
  ∃ (a : A) (b : B),
    extract_value
      (combine_meet_return_values res_a res_b
         (fun _ =>
            rebuild (extract_value res_a left_a right_a)
              (extract_value res_b left_b right_b)))
      (rebuild left_a left_b) (rebuild right_a right_b)
    = rebuild a b
    ∧ (a = left_a ∨ a = right_a ∨ a = extract_value res_a left_a right_a)
    ∧ (b = left_b ∨ b = right_b ∨ b = extract_value res_b left_b right_b).
Proof.
  destruct res_a, res_b; cbn; eexists; eexists;
    (split; [ reflexivity | ]); split; auto.
Qed.

Theorem combine_results2_ok : combine_results2_ok_statement.
Proof.
  intros type_well_formed A B C fits_a satisfied_a fits_b satisfied_b fits_c
    satisfied_c meet_a meet_b rebuild menv left_a right_a left_b right_b
    result tenv [Hstable_a1 Hstable_a2] [Hstable_b1 Hstable_b2] Hok_a Hok_b
    Hfits_c Hsatisfied_c Henv Hla Hra Hlb Hrb Hmeet.
  unfold combine_results2 in Hmeet.
  destruct (meet_a menv left_a right_a) as [ result_a | ] eqn:Hmeet_a;
    [ | discriminate ].
  destruct (Hok_a menv left_a right_a result_a Henv Hla Hra Hmeet_a)
    as [Hkeeps_a Hsound_a].
  cbn in Hmeet.
  destruct result_a as [ r_a | res_a menv1 ].
  { injection Hmeet as <-. apply meet_call_ok_bottom.
    intros statics valuation Hvaluation H1 H2.
    apply Hsatisfied_c in H1. apply Hsatisfied_c in H2.
    destruct (Hsound_a statics valuation Hvaluation (proj1 H1) (proj1 H2))
      as (r & menv' & valuation' & Hresult & _).
    discriminate Hresult. }
  destruct (Hkeeps_a res_a menv1 eq_refl) as (Hextends1 & Henv1 & Hanswer_a).
  destruct (meet_b menv1 left_b right_b) as [ result_b | ] eqn:Hmeet_b;
    [ | discriminate ].
  assert (Hlb1 := Hstable_b1 menv menv1 left_b Hextends1 Hlb).
  assert (Hrb1 := Hstable_b1 menv menv1 right_b Hextends1 Hrb).
  destruct (Hok_b menv1 left_b right_b result_b Henv1 Hlb1 Hrb1 Hmeet_b)
    as [Hkeeps_b Hsound_b].
  cbn in Hmeet.
  destruct result_b as [ r_b | res_b menv2 ].
  { injection Hmeet as <-. apply meet_call_ok_bottom.
    intros statics valuation Hvaluation H1 H2.
    apply Hsatisfied_c in H1. apply Hsatisfied_c in H2.
    destruct (Hsound_a statics valuation Hvaluation (proj1 H1) (proj1 H2))
      as (r & menv' & valuation1 & Hresult & Hextended1 & Hvaluation1 & _).
    injection Hresult as <- <-.
    destruct (Hsound_b statics valuation1 Hvaluation1
                (Hstable_b2 statics _ valuation valuation1 left_b Hlb
                   Hextended1 (proj2 H1))
                (Hstable_b2 statics _ valuation valuation1 right_b Hrb
                   Hextended1 (proj2 H2)))
      as (r & menv' & valuation' & Hresult & _).
    discriminate Hresult. }
  injection Hmeet as <-.
  destruct (Hkeeps_b res_b menv2 eq_refl) as (Hextends2 & Henv2 & Hanswer_b).
  assert (Hextends := meet_env_extends_trans _ _ _ Hextends1 Hextends2).
  destruct (combine_extract rebuild res_a res_b left_a right_a left_b right_b)
    as (a & b & Hextract & Ha & Hb).
  split.
  - intros r menv' [= <- <-].
    split; [ exact Hextends | ]. split; [ exact Henv2 | ].
    rewrite Hextract. apply Hfits_c.
    + destruct Ha as [ -> | [ -> | -> ] ].
      * exact (Hstable_a1 menv menv2 left_a Hextends Hla).
      * exact (Hstable_a1 menv menv2 right_a Hextends Hra).
      * exact (Hstable_a1 menv1 menv2 _ Hextends2 Hanswer_a).
    + destruct Hb as [ -> | [ -> | -> ] ].
      * exact (Hstable_b1 menv menv2 left_b Hextends Hlb).
      * exact (Hstable_b1 menv menv2 right_b Hextends Hrb).
      * exact Hanswer_b.
  - intros statics valuation Hvaluation H1 H2.
    apply Hsatisfied_c in H1. apply Hsatisfied_c in H2.
    destruct H1 as [Hsla Hslb], H2 as [Hsra Hsrb].
    destruct (Hsound_a statics valuation Hvaluation Hsla Hsra)
      as (r & menv' & valuation1 & Hresult & Hextended1 & Hvaluation1
          & Hsanswer_a).
    injection Hresult as <- <-.
    destruct (Hsound_b statics valuation1 Hvaluation1
                (Hstable_b2 statics _ valuation valuation1 left_b Hlb
                   Hextended1 Hslb)
                (Hstable_b2 statics _ valuation valuation1 right_b Hrb
                   Hextended1 Hsrb))
      as (r & menv' & valuation2 & Hresult & Hextended2 & Hvaluation2
          & Hsanswer_b).
    injection Hresult as <- <-.
    assert (Hextended :
      extended_from (Meet_env.typing_env menv) valuation valuation2).
    { exact (extended_from_trans _ _ _ _ _
               (meet_env_extends_keeps_names _ _ Hextends1) Hextended1
               Hextended2). }
    eexists. exists menv2, valuation2. split; [ reflexivity | ].
    split; [ exact Hextended | ]. split; [ exact Hvaluation2 | ].
    rewrite Hextract. apply Hsatisfied_c. split.
    + destruct Ha as [ -> | [ -> | -> ] ].
      * exact (Hstable_a2 statics _ valuation valuation2 left_a Hla Hextended
                 Hsla).
      * exact (Hstable_a2 statics _ valuation valuation2 right_a Hra
                 Hextended Hsra).
      * exact (Hstable_a2 statics _ valuation1 valuation2 _ Hanswer_a
                 Hextended2 Hsanswer_a).
    + destruct Hb as [ -> | [ -> | -> ] ].
      * exact (Hstable_b2 statics _ valuation valuation2 left_b Hlb Hextended
                 Hslb).
      * exact (Hstable_b2 statics _ valuation valuation2 right_b Hrb
                 Hextended Hsrb).
      * exact Hsanswer_b.
Qed.

(* ======================================================================== *)
(* Sets                                                                     *)
(* ======================================================================== *)

Theorem set_meet_cases : set_meet_cases_statement.
Proof.
  intros K B eqb of_set env s1 s2 Heqb. unfold set_meet.
  assert (Hin := keyed_among_in K eqb Heqb).
  destruct (Keyed.all_among eqb s1 s2) eqn:H12;
    destruct (Keyed.all_among eqb s2 s1) eqn:H21.
  - split; [ reflexivity | ]. exists s1. split; [ reflexivity | ].
    split; [ | intros Hne _; exact Hne ].
    intros key. split; [ | tauto ]. intros Hkey. split; [ exact Hkey | ].
    apply Hin. apply (proj1 (keyed_all_among K eqb Heqb s1 s2) H12).
    apply Hin, Hkey.
  - split; [ reflexivity | ]. exists s1. split; [ reflexivity | ].
    split; [ | intros Hne _; exact Hne ].
    intros key. split; [ | tauto ]. intros Hkey. split; [ exact Hkey | ].
    apply Hin. apply (proj1 (keyed_all_among K eqb Heqb s1 s2) H12).
    apply Hin, Hkey.
  - split; [ reflexivity | ]. exists s2. split; [ reflexivity | ].
    split; [ | intros _ Hne; exact Hne ].
    intros key. split; [ | tauto ]. intros Hkey. split; [ | exact Hkey ].
    apply Hin. apply (proj1 (keyed_all_among K eqb Heqb s2 s1) H21).
    apply Hin, Hkey.
  - assert (Hinter :
      ∀ key : K, key ∈ Keyed.inter eqb s1 s2 <-> key ∈ s1 ∧ key ∈ s2).
    { intros key. rewrite <- !Hin, (keyed_among_inter K eqb Heqb).
      apply andb_true_iff. }
    destruct (Keyed.inter eqb s1 s2) as [ | first rest ] eqn:Hs; cbn.
    + intros key Hkey. apply Hinter in Hkey. destruct Hkey.
    + split; [ reflexivity | ]. exists (first :: rest).
      split; [ reflexivity | ]. split; [ exact Hinter | ].
      intros _ _. discriminate.
Qed.

Theorem naked_number_meet_ok : naked_number_meet_ok_statement.
Proof.
  intros type_well_formed k v menv t1 t2 result Henv Hf1 Hf2 [= <-].
  unfold meet_head_of_kind_naked_number.
  assert (Hcases :=
    set_meet_cases Z (list Z) Z.eqb (fun s => s) menv t1 t2
      z_eqb_decides_equality).
  assert (Hboth :
    naked_numbers_satisfied k v t1 -> naked_numbers_satisfied k v t2 ->
    ∃ (c : const) (n : Z),
      v = Value_const c
      ∧ kind_of_const c = Naked_number k
      ∧ number_of_const c = Some n
      ∧ n ∈ t1 ∧ n ∈ t2).
  { intros (c & n & -> & Hk & Hn & Hin1) (c' & n' & [= <-] & _ & Hn' & Hin2).
    rewrite Hn in Hn'. injection Hn' as <-. exists c, n. auto. }
  destruct (set_meet Z.eqb (fun s : list Z => s) menv t1 t2)
    as [ r | r env' ].
  - apply meet_call_ok_bottom. intros statics valuation _ H1 H2.
    destruct (Hboth H1 H2) as (c & n & _ & _ & _ & Hin1 & Hin2).
    exact (Hcases n (conj Hin1 Hin2)).
  - destruct Hcases as (-> & s & Hextract & Hmem & Hne).
    apply meet_call_ok_same_env; [ exact Henv | | ].
    + rewrite Hextract. exact (Hne Hf1 Hf2).
    + intros statics valuation H1 H2. rewrite Hextract.
      destruct (Hboth H1 H2) as (c & n & Hv & Hk & Hn & Hin1 & Hin2).
      exists c, n. split; [ exact Hv | ]. split; [ exact Hk | ].
      split; [ exact Hn | ]. apply Hmem. split; assumption.
Qed.
