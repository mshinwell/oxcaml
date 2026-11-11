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
