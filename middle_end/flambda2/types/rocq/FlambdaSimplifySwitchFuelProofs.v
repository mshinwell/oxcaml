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
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs.
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

Theorem relation_switch_fuel : relation_switch_fuel_statement.
Proof.
  intros join choices tenv scrutinee fuel Hjoin Hshapes Hfree Hconsistent
    Hscrutinee Hfuel scrutinee_ty canonical i Hty.
  destruct (Hscrutinee scrutinee_ty canonical Hty)
    as (n & ty & Hcanonical & Hsimple & Hfind & head & -> & Hone).
  pose proof
    (relation_const_fuel_enough join choices tenv scrutinee_ty n head
       (Naked_immediate i) Hjoin Hshapes Hfree Hconsistent Hcanonical Hsimple
       Hfind Hone) as Henough.
  exact
    (proj2
       (meet_fuel_enough_stable join choices 2 fuel tenv scrutinee_ty
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
  apply relation_switch_fuel; try assumption.
  - apply values_extension_free_of_entries. vm_compute. reflexivity.
  - intros scrutinee_ty canonical Hty. vm_compute in Hty.
    injection Hty as <- <-.
    exists (Name_var FlambdaMeetExamplesSpec.example_tag).
    eexists. split; [ vm_compute; reflexivity | ].
    split; [ vm_compute; reflexivity | ].
    split; [ vm_compute; reflexivity | ].
    eexists. split; [ reflexivity | cbn; lia ].
Qed.
