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

(* Proofs of the statements of FlambdaSimplifySwitchFuelSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaCseSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaMeetGrammar
  FlambdaExpandHead FlambdaMeetEnv FlambdaMeet FlambdaMeetSpec
  FlambdaMeetTerminationSpec FlambdaMeetTerminationProofs FlambdaMeetDepthSpec
  FlambdaMeetRelationFuelSpec FlambdaMeetRelationFuelProofs
  FlambdaSimplifyPrimitivesSpec FlambdaSimplifySwitchSpec
  FlambdaSimplifySwitchArmsSpec FlambdaSimplifySwitchMergeSpec
  FlambdaSimplifySwitchFuelSpec.
From OxCamlFlambda2Types Require FlambdaMeetExamplesSpec
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs
  FlambdaJoinEnv FlambdaJoinMeet FlambdaMeetDepthProofs.
Import ListNotations.

Lemma prune_arms_agree (meet meet' : meet_function) (tenv : Typing_env.t)
    (scrutinee_ty : flambda_type) (arms : list (Z * apply_cont)) :
  (∀ i : Z,
    meet tenv scrutinee_ty (this_naked_immediate i)
    = meet' tenv scrutinee_ty (this_naked_immediate i)) ->
  prune_arms meet tenv scrutinee_ty arms
  = prune_arms meet' tenv scrutinee_ty arms.
Proof.
  intros Hagree. induction arms as [ | [i ac] arms IH]; [ reflexivity | ].
  cbn [prune_arms]. unfold arm_kept. rewrite Hagree, IH. reflexivity.
Qed.

Lemma simplify_arms_agree (meet meet' : meet_function)
    (rewrite : apply_cont_rewrite) (tenv : Typing_env.t)
    (scrutinee_ty : flambda_type) (arms : list (Z * apply_cont)) :
  (∀ i : Z,
    meet tenv scrutinee_ty (this_naked_immediate i)
    = meet' tenv scrutinee_ty (this_naked_immediate i)) ->
  simplify_arms meet rewrite tenv scrutinee_ty arms
  = simplify_arms meet' rewrite tenv scrutinee_ty arms.
Proof.
  intros Hagree. induction arms as [ | [i ac] arms IH]; [ reflexivity | ].
  cbn [simplify_arms]. unfold simplify_arm. rewrite Hagree, IH. reflexivity.
Qed.

Theorem slices_of_agreeing_meets : slices_of_agreeing_meets_statement.
Proof.
  intros meet meet' rewrite known fresh tenv scrutinee arms Hagree.
  unfold simplify_switch, simplify_switch_arms, simplify_switch_merging.
  destruct
    (Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal)
       scrutinee) as [[[scrutinee_ty canonical] | ] | ] eqn:Hty;
    cbn beta iota; try (repeat split; reflexivity).
  rewrite
    (prune_arms_agree meet meet' tenv scrutinee_ty arms
       (fun i => Hagree scrutinee_ty canonical i Hty)),
    (simplify_arms_agree meet meet' rewrite tenv scrutinee_ty arms
       (fun i => Hagree scrutinee_ty canonical i Hty)).
  repeat split; reflexivity.
Qed.

Theorem switch_fuel : switch_fuel_statement.
Proof.
  intros join choices tenv scrutinee fuel Hjoin Hshapes Hfree Hconsistent
    Hfuel scrutinee_ty canonical i Hty.
  exact
    (proj2
       (meet_fuel_enough_stable join choices 2 fuel tenv scrutinee_ty
          (this_naked_immediate i)
          (naked_immediate_fuel_enough join choices tenv scrutinee_ty i Hjoin
             Hshapes Hfree Hconsistent) Hfuel)).
Qed.

Theorem switch_arm_keeps : switch_arm_keeps_statement.
Proof.
  intros join choices tenv tenv' scrutinee fuel scrutinee_ty ty canonical i
    Hjoin Hshapes Hfree Hconsistent Hfuel _ Hmeet.
  exact
    (naked_immediate_meet_keeps join choices fuel tenv tenv' scrutinee_ty ty i
       Hjoin Hshapes Hfree Hconsistent Hfuel Hmeet).
Qed.

Theorem switch_slices_fuel : switch_slices_fuel_statement.
Proof.
  intros join choices rewrite known fresh tenv scrutinee arms fuel Hjoin
    Hshapes Hfree Hconsistent Hfuel.
  apply slices_of_agreeing_meets.
  exact
    (switch_fuel join choices tenv scrutinee fuel Hjoin Hshapes Hfree
       Hconsistent Hfuel).
Qed.

Theorem model_switch_fuel : model_switch_fuel_statement.
Proof.
  intros join_choices choices join_depth [fuel_env fuel_types fuel_meet]
    [fuel_env' fuel_types' fuel_meet'] tenv scrutinee Hfuel Henv Htypes
    Hmeet Hmeet' Hchoices Hvalues Haliases.
  cbn [FlambdaJoinMeet.fuel_of_env FlambdaJoinMeet.fuel_of_types
       FlambdaJoinMeet.fuel_of_meet] in Hfuel, Henv, Htypes, Hmeet, Hmeet'.
  subst fuel_env' fuel_types'.
  set (fuel :=
    {| FlambdaJoinMeet.fuel_of_env := fuel_env;
       FlambdaJoinMeet.fuel_of_types := fuel_types;
       FlambdaJoinMeet.fuel_of_meet := fuel_meet |}).
  pose proof
    (FlambdaMeetDepthProofs.model_join_of_nothing join_choices join_depth
       fuel Hfuel) as Hjoin.
  intros scrutinee_ty canonical i Hty.
  change
    (Meet.meet
       (FlambdaJoinMeet.model_join_scoped_envs join_choices join_depth fuel)
       choices fuel_meet tenv scrutinee_ty (this_naked_immediate i)
     = Meet.meet
         (FlambdaJoinMeet.model_join_scoped_envs join_choices join_depth fuel)
         choices fuel_meet' tenv scrutinee_ty (this_naked_immediate i)).
  rewrite
    (switch_fuel _ choices tenv scrutinee fuel_meet Hjoin Hchoices Hvalues
       Haliases Hmeet scrutinee_ty canonical i Hty).
  rewrite
    (switch_fuel _ choices tenv scrutinee fuel_meet' Hjoin Hchoices Hvalues
       Haliases Hmeet' scrutinee_ty canonical i Hty).
  reflexivity.
Qed.

Theorem flat_switch_fuel : flat_switch_fuel_statement.
Proof.
  intros join choices tenv scrutinee fuel Hconsistent Hscrutinee Hfuel
    scrutinee_ty canonical i Hty.
  destruct (Hscrutinee scrutinee_ty canonical Hty)
    as (n & ty & Hcanonical & Hsimple & Hfind & e & He & Hflat).
  pose proof
    (alias_flat_const_fuel_enough join choices tenv scrutinee_ty ty n e
       (Naked_immediate i) Hconsistent Hcanonical Hsimple Hfind He Hflat
       eq_refl) as Henough.
  exact
    (proj2
       (meet_fuel_enough_stable join choices 1 fuel tenv scrutinee_ty
          (this_const (Naked_immediate i)) Henough Hfuel)).
Qed.

Theorem example_switch_fuel : example_switch_fuel_statement.
Proof.
  intros join choices fuel arms Hjoin Hshapes Hfuel.
  apply
    (slices_of_agreeing_meets _ _ (fun _ ac => ac) [] []
       FlambdaMeetExamplesSpec.example_get_tag_env
       (Var FlambdaMeetExamplesSpec.example_tag) arms).
  assert (Hwf :
    FlambdaTypingEnvInvariantSpec.typing_env_well_formed
      FlambdaMeetExamplesSpec.example_get_tag_env
    = true) by (vm_compute; reflexivity).
  pose proof
    (proj1 (FlambdaTypingEnvInvariantProofs.typing_env_well_formed_iff _) Hwf)
    as Hconditions.
  destruct Hconditions as [_ [_ [Hconsistent _]]].
  apply switch_fuel; try assumption.
  apply values_extension_free_of_entries. vm_compute. reflexivity.
Qed.

Theorem example_switch_under_arm : example_switch_under_arm_statement.
Proof.
  set (tenv' :=
    match example_arm_env with
    | Some tenv' => tenv'
    | None => Typing_env.create
    end).
  assert (Harm : example_arm_env = Some tenv') by (vm_compute; reflexivity).
  exists tenv'. split; [ exact Harm | ].
  split; [ vm_compute; reflexivity | ].
  split; [ | intros ac0 ac1; vm_compute; reflexivity ].
  intros join choices fuel arms Hjoin Hshapes Hfuel.
  assert (Hgood :
    values_extension_free tenv'
    ∧ aliases_consistent (Typing_env.aliases tenv')).
  { unfold example_arm_env in Harm.
    destruct
      (Meet.meet FlambdaMeetExamplesSpec.forgetful_join repaired_choices 2
         example_two_relations_env FlambdaMeetExamplesSpec.example_tag_type
         (this_naked_immediate 1)) as [[[ty tenv''] | ] | ] eqn:Hmeet;
      try discriminate Harm.
    injection Harm as Harm. rewrite <- Harm.
    assert (Hwf :
      FlambdaTypingEnvInvariantSpec.typing_env_well_formed
        example_two_relations_env
      = true) by (vm_compute; reflexivity).
    pose proof
      (proj1 (FlambdaTypingEnvInvariantProofs.typing_env_well_formed_iff _)
         Hwf) as Hconditions.
    destruct Hconditions as [_ [_ [Hconsistent _]]].
    refine
      (naked_immediate_meet_keeps FlambdaMeetExamplesSpec.forgetful_join
         repaired_choices 2 example_two_relations_env tenv''
         FlambdaMeetExamplesSpec.example_tag_type ty 1%Z
         FlambdaMeetDepthProofs.forgetful_join_of_nothing
         (proj2 choices_get_tag_shapes) _ Hconsistent (le_n 2) Hmeet).
    apply values_extension_free_of_entries. vm_compute. reflexivity. }
  destruct Hgood as [Hfree Hconsistent].
  apply
    (slices_of_agreeing_meets _ _ (fun _ ac => ac) [] [] tenv'
       (Var FlambdaMeetExamplesSpec.example_tag) arms).
  apply switch_fuel; assumption.
Qed.
