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



(* Proofs of the statements of FlambdaMeetExamplesSpec.v. Nothing here
   needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaEnvAliasesSpec
  FlambdaEnvAliasesProofs FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvProofs FlambdaTypingEnvExamplesProofs FlambdaMeetGrammar
  FlambdaExpandHead FlambdaMeetEnv FlambdaMeet FlambdaMeetSpec
  FlambdaMeetProofs FlambdaMeetExamplesSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* The meaning of a type that is given in full, unfolded. *)
Ltac open_type := repeat (autorewrite with type_satisfied; cbn).

(* The first binding of a key in a list that begins with a binding. *)
Lemma lookup_cons_cases {K A : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) (key bound : K) (a a' : A)
    (bindings : list (K * A)) :
  Keyed.lookup eqb key ((bound, a) :: bindings) = Some a' ->
  (key = bound ∧ a' = a)
  ∨ (key <> bound ∧ Keyed.lookup eqb key bindings = Some a').
Proof.
  simpl. destruct (eqb key bound) eqn:Heq.
  - intros H. injection H as <-. left.
    split; [ apply Heqb; exact Heq | reflexivity ].
  - intros H. right. split; [ | exact H ].
    intros ->. rewrite (proj2 (Heqb bound bound) eq_refl) in Heq.
    discriminate Heq.
Qed.

(* The cases of a lookup in a list that is given in full. *)
Ltac lookup_cases H :=
  repeat
    (first
       [ discriminate H
       | apply (lookup_cons_cases name_eqb name_eqb_eq) in H;
         destruct H as [[-> H] | [? H]]; [ try congruence | ] ]);
  try (injection H as -> ->).

(* ======================================================================== *)
(* The step for [Get_tag]                                                   *)
(* ======================================================================== *)

Theorem example_get_tag_env_made : example_get_tag_env_made_statement.
Proof.
  intros join type_of_get_tag_scrutinee define_again.
  vm_compute. reflexivity.
Qed.

Lemma example_tag_is_get_tag (statics : static_env) (vars : env) (i : Z) :
  lookup example_p vars = Some (Value_const (Tagged_immediate i)) ->
  head_of_kind_naked_immediate_satisfied statics vars
    (Value_const (Naked_immediate 0))
    {| naked_immediates := Or_unknown.Unknown;
       inverse_relations := [(Relation.Get_tag, Name_var example_p)] |}.
Proof.
  intros Hp. exists 0. split; [ reflexivity | ]. split; [ exact I | ].
  intros relation n [Hin | []]. injection Hin as <- <-.
  exists (Value_const (Tagged_immediate i)). split; [ exact Hp | ].
  left. exists i. reflexivity.
Qed.

Theorem example_get_tag_env_satisfied
    : example_get_tag_env_satisfied_statement.
Proof.
  split; [ | split ].
  - split; [ reflexivity | ]. split; [ | apply empty_respected ].
    intros n ty btm v Hlookup Hvalue.
    apply (keyed_lookup_in name_eqb name_eqb_eq) in Hlookup.
    vm_compute in Hlookup.
    repeat (destruct Hlookup as [Hlookup | Hlookup];
            [ injection Hlookup as <- <- <- | ]); [ .. | contradiction ].
    all: cbv in Hvalue; injection Hvalue as <-; right; open_type.
    all: try reflexivity.
    + right. split; [ discriminate | ]. split; [ | exact I ].
      left. exists 7. repeat split.
    + apply (example_tag_is_get_tag _ _ 7). reflexivity.
  - apply (proj2 (alias_satisfied _ _ _ _ _)). split; reflexivity.
  - apply (proj2 (alias_satisfied _ _ _ _ _)). split; reflexivity.
Qed.

Theorem compiler_meet_get_tag : compiler_meet_get_tag_statement.
Proof.
  intros join. eexists. eexists. split; [ vm_compute; reflexivity | ].
  intros valuation' Hextended [_ [Hnames _]].
  assert (Hp : lookup example_p valuation'
               = Some (Value_const (Tagged_immediate 7)))
    by (apply Hextended; reflexivity).
  refine (_ (Hnames (Name_var example_p) _ _ _ eq_refl Hp)).
  intros [[[] _] | Hsatisfied].
  revert Hsatisfied. open_type.
  intros [[Hnull _] | [_ [[[i [_ [_ [Himmediate _]]]] | Hblock] _]]].
  - discriminate Hnull.
  - exact Himmediate.
  - destruct Hblock as [tag [fields [Hblock _]]]. discriminate Hblock.
Qed.

Theorem compiler_meet_not_sound : compiler_meet_not_sound_statement.
Proof.
  intros type_well_formed typing_env_well_formed join Hinputs Hsound.
  destruct example_get_tag_env_satisfied as [Henv [Ht1 Ht2]].
  destruct (compiler_meet_get_tag join) as [t [tenv' [Hmeet Hnot]]].
  destruct (Hsound _ _ _ _ _ _ _ Hinputs Henv Ht1 Ht2 Hmeet)
    as [t0 [tenv0 [valuation' [Hresult [Hextended [Hsatisfied _]]]]]].
  injection Hresult as <- <-. exact (Hnot valuation' Hextended Hsatisfied).
Qed.

(* ======================================================================== *)
(* A join that has its contract                                             *)
(* ======================================================================== *)

Theorem forgetful_join_sound : forgetful_join_sound_statement.
Proof.
  intros type_well_formed typing_env_well_formed meet_head initial_env result
    scoped_envs initial_tenv Hsound Hkeeps Hfits Hscoped Hjoin.
  injection Hjoin as <-. split; [ | split; [ | split ] ].
  - intros scoped_env statics valuation Hin Hinitial Hscoped_env.
    exists valuation. split; [ | exact Hinitial ].
    intros x v _ Hlookup. exact Hlookup.
  - repeat split; try reflexivity.
    + intros x Hamong. exact Hamong.
    + intros n ty binding_time_and_mode Hlookup. exists ty.
      split; [ exact Hlookup | reflexivity ].
  - exact Hfits.
  - intros x Hknown Hunknown. unfold initial_tenv in Hunknown.
    rewrite Hknown in Hunknown. discriminate Hunknown.
Qed.

Theorem meet_to_prove_get_tag : meet_to_prove_get_tag_statement.
Proof.
  eexists. eexists. split; [ vm_compute; reflexivity | ]. split.
  - split; [ reflexivity | ]. split.
    + intros n ty btm v Hlookup Hvalue.
      apply (keyed_lookup_in name_eqb name_eqb_eq) in Hlookup.
      repeat (destruct Hlookup as [Hlookup | Hlookup];
              [ injection Hlookup as <- <- <- | ]); [ .. | contradiction ].
      all: cbv in Hvalue; injection Hvalue as <-; right; open_type.
      all: try reflexivity.
      * right. split; [ discriminate | ]. split; [ | exact I ].
        left. exists 7. repeat split.
      * split; reflexivity.
      * right. split; [ discriminate | ]. split; [ | exact I ].
        left. exists 7. repeat split.
      * apply (example_tag_is_get_tag _ _ 7). reflexivity.
    + apply aliases_respected_of_bindings.
      * intros n c Hin.
        repeat (destruct Hin as [Hin | Hin]; [ injection Hin as <- <- | ]);
          [ .. | contradiction ]; reflexivity.
      * intros c aliases n mode Hin. destruct Hin.
      * intros k aliases n mode Hin Hmode.
        repeat (destruct Hin as [Hin | Hin]; [ injection Hin as <- <- | ]);
          [ .. | contradiction ].
        repeat (destruct Hmode as [Hmode | Hmode];
                [ injection Hmode as <- <- | ]);
          [ .. | contradiction ]; reflexivity.
  - apply (proj2
             (alias_satisfied _ _ _ (Naked_number Kind_naked_immediate)
                (Var example_tag))).
    split; reflexivity.
Qed.

(* ======================================================================== *)
(* Adding an equation can forget                                            *)
(* ======================================================================== *)

Theorem add_equation_forgets : add_equation_forgets_statement.
Proof.
  intros join. eexists. split; [ vm_compute; reflexivity | ]. split.
  - split; [ reflexivity | ]. split; [ | apply empty_respected ].
    intros n ty btm v Hlookup Hvalue.
    lookup_cases Hlookup.
    all: cbv in Hvalue; injection Hvalue as <-; right; open_type.
    all: try reflexivity.
    right. split; [ discriminate | ]. split; [ reflexivity | exact I ].
  - intros [_ [Hnames _]].
    refine (_ (Hnames (Name_var example_x) _ _ _ eq_refl eq_refl)).
    intros [[[] _] | Hsatisfied]. revert Hsatisfied. open_type.
    intros [[Hnull _] | [_ [_ Hz]]]; [ discriminate Hnull | ].
    discriminate Hz.
Qed.

(* ======================================================================== *)
(* Poison                                                                   *)
(* ======================================================================== *)

Theorem meet_through_poison : meet_through_poison_statement.
Proof.
  split; [ | split; [ | split ] ].
  - split; [ reflexivity | ]. split; [ | apply empty_respected ].
    intros n ty btm v Hlookup Hvalue.
    apply (keyed_lookup_in name_eqb name_eqb_eq) in Hlookup.
    repeat (destruct Hlookup as [Hlookup | Hlookup];
            [ injection Hlookup as <- <- <- | ]); [ .. | contradiction ].
    all: cbv in Hvalue; injection Hvalue as <-.
    + left. split; [ | reflexivity ]. left.
      exists (Value_const (Poison Value)).
      split; [ reflexivity | exists Value; reflexivity ].
    + right. open_type. reflexivity.
  - apply (proj2 (alias_satisfied _ _ _ _ _)). split; reflexivity.
  - apply (proj2 (any_non_null_value_satisfied _ _ _)).
    split; [ reflexivity | discriminate ].
  - intros join. vm_compute. reflexivity.
Qed.
