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



(* Proofs of the statements of FlambdaMeetEnvSpec.v. Nothing here
   needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaEnvAliasesSpec
  FlambdaEnvAliasesProofs FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvProofs FlambdaTypingEnvInvariantSpec
  FlambdaTypingEnvInvariantProofs FlambdaTypingEnvOperationsSpec
  FlambdaTypingEnvOperationsProofs FlambdaTypingEnvKindedSpec
  FlambdaTypingEnvKindedProofs FlambdaMeetGrammar FlambdaExpandHead
  FlambdaMeetEnv FlambdaMeet FlambdaMeetSpec FlambdaMeetStepsSpec
  FlambdaMeetStepsProofs FlambdaMeetEnvSpec.
Import ListNotations.

(* ======================================================================== *)
(* From one environment to another that has the same names                  *)
(* ======================================================================== *)

(* A type that fits an environment fits another in which the variables
   that were bound are bound and every simple has the kinds that it
   had. *)
Lemma type_fits_kept (type_well_formed : flambda_type -> bool)
    (tenv tenv' : Typing_env.t) (ty : flambda_type) :
  (∀ x : variable,
     Typing_env.mem None tenv (Name_var x) = true ->
     Typing_env.mem None tenv' (Name_var x) = true) ->
  (∀ (s : simple) (kind : flambda_kind),
     simple_of_kind tenv s kind -> simple_of_kind tenv' s kind) ->
  type_fits type_well_formed tenv ty ->
  type_fits type_well_formed tenv' ty.
Proof.
  intros Hmem Hkind (Hwf & Hclosed & Hkinded).
  split; [ exact Hwf | ]. split.
  - intros x Hin. exact (Hmem x (Hclosed x Hin)).
  - intros s kind Hin. exact (Hkind s kind (Hkinded s kind Hin)).
Qed.

Lemma is_obviously_bottom_unknown (kind : flambda_kind) :
  is_obviously_bottom (unknown kind) = false.
Proof. destruct kind as [ | [] | | ]; reflexivity. Qed.

Lemma aliases_with_kinds_unknown (kind : flambda_kind) :
  aliases_with_kinds (unknown kind) = [].
Proof. destruct kind as [ | [] | | ]; reflexivity. Qed.

(* ======================================================================== *)
(* [make_bottom]                                                            *)
(* ======================================================================== *)

Theorem make_bottom_keeps : make_bottom_keeps_statement.
Proof.
  intros type_well_formed menv (Hinvariant & Hbottom & Haliases & Hfits).
  split.
  - repeat split; try reflexivity.
    + intros x Hamong. exact Hamong.
    + intros n ty binding_time_and_mode Hlookup. exists ty.
      split; [ exact Hlookup | reflexivity ].
  - change (Meet_env.typing_env (Meet_env.make_bottom menv))
      with (Typing_env.make_bottom (Meet_env.typing_env menv)).
    split; [ exact (make_bottom_invariant _ Hinvariant) | ].
    split; [ intros Hfalse; discriminate Hfalse | ].
    split; [ exact (make_bottom_aliases_kinded _ Haliases) | ].
    intros n ty binding_time_and_mode Hlookup.
    apply (type_fits_kept type_well_formed (Meet_env.typing_env menv)).
    + intros x Hmem. exact Hmem.
    + intros s kind Hkind. apply make_bottom_simple_of_kind. exact Hkind.
    + exact (Hfits n ty binding_time_and_mode Hlookup).
Qed.

(* ======================================================================== *)
(* [add_variable_definition]                                                *)
(* ======================================================================== *)

Lemma add_variable_definition_names (tenv : Typing_env.t) (var : variable)
    (kind : flambda_kind) (name_mode : Name_mode.t) :
  Typing_env.names_to_types
    (Typing_env.add_variable_definition tenv var kind name_mode)
  = (Name_var var,
     (unknown kind,
      Binding_time.With_name_mode.create (Typing_env.next_binding_time tenv)
        name_mode))
    :: Typing_env.names_to_types tenv.
Proof. reflexivity. Qed.

Theorem add_variable_definition_keeps
    : add_variable_definition_keeps_statement.
Proof.
  intros type_well_formed menv var kind name_mode menv'
    (Hinvariant & Hbottom & Haliases & Hfits) Hfresh Hunknown.
  set (tenv := Meet_env.typing_env menv) in *.
  set (tenv' := Typing_env.add_variable_definition tenv var kind name_mode).
  assert (Hnone :
    Keyed.lookup name_eqb (Name_var var) (Typing_env.names_to_types tenv)
    = None).
  { destruct (Keyed.lookup name_eqb (Name_var var)
                (Typing_env.names_to_types tenv))
      as [ [ty binding_time_and_mode] | ] eqn:Hlookup; [ | reflexivity ].
    rewrite (proj2 (mem_var_lookup tenv var)) in Hfresh;
      [ discriminate Hfresh | ].
    exists ty, binding_time_and_mode. exact Hlookup. }
  assert (Hother :
    ∀ n : name,
      n <> Name_var var ->
      Keyed.lookup name_eqb n (Typing_env.names_to_types tenv')
      = Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)).
  { intros n Hn. unfold tenv'. rewrite add_variable_definition_names.
    apply (keyed_lookup_other name_eqb name_eqb_eq). exact Hn. }
  assert (Hkeeps : keeps_names tenv tenv').
  { intros n ty binding_time_and_mode Hlookup. exists ty.
    split; [ | reflexivity ]. rewrite Hother; [ exact Hlookup | ].
    intros ->. rewrite Hnone in Hlookup. discriminate Hlookup. }
  assert (Hkind :
    ∀ (s : simple) (kind' : flambda_kind),
      simple_of_kind tenv s kind' -> simple_of_kind tenv' s kind').
  { intros s kind' Hs. apply add_variable_definition_simple_of_kind.
    destruct (simple_equal s (Var var)) eqn:Hsame.
    - apply simple_equal_decides_equality in Hsame. subst s.
      destruct Hs as [ty Hfind]. exfalso.
      destruct (find_cases tenv (Name_var var) (Some kind') ty Hfind)
        as [ [binding_time_and_mode Hlookup] | Hrest ].
      + rewrite Hnone in Hlookup. discriminate Hlookup.
      + unfold Typing_env.find,
          Typing_env.find_with_binding_time_and_mode' in Hfind.
        rewrite Hnone in Hfind. discriminate Hfind.
    - right. split; [ | exact Hs ]. intros ->.
      rewrite (proj2 (simple_equal_decides_equality _ _) eq_refl) in Hsame.
      discriminate Hsame. }
  split.
  - repeat split; try reflexivity.
    + intros x Hamong. exact Hamong.
    + exact Hkeeps.
  - change (Meet_env.typing_env menv') with tenv'.
    split.
    { exact (add_variable_definition_invariant tenv var kind name_mode
               Hinvariant Hfresh). }
    split.
    { intros Hnot_bottom n ty binding_time_and_mode Hlookup.
      destruct (name_eqb n (Name_var var)) eqn:Hn.
      - apply name_eqb_eq in Hn. subst n. unfold tenv' in Hlookup.
        rewrite add_variable_definition_names in Hlookup.
        rewrite (keyed_lookup_head name_eqb name_eqb_eq) in Hlookup.
        injection Hlookup as <- _. apply is_obviously_bottom_unknown.
      - rewrite Hother in Hlookup.
        + exact (Hbottom Hnot_bottom n ty binding_time_and_mode Hlookup).
        + intros ->. rewrite (proj2 (name_eqb_eq _ _) eq_refl) in Hn.
          discriminate Hn. }
    split.
    { exact (add_variable_definition_aliases_kinded tenv var kind name_mode
               (proj1 Hinvariant) Hfresh Haliases). }
    intros n ty binding_time_and_mode Hlookup.
    destruct (name_eqb n (Name_var var)) eqn:Hn.
    + apply name_eqb_eq in Hn. subst n. unfold tenv' in Hlookup.
      rewrite add_variable_definition_names in Hlookup.
      rewrite (keyed_lookup_head name_eqb name_eqb_eq) in Hlookup.
      injection Hlookup as <- _.
      split; [ exact Hunknown | ]. split.
      * intros x Hin. rewrite free_variables_unknown in Hin. destruct Hin.
      * intros s kind' Hin. rewrite aliases_with_kinds_unknown in Hin.
        destruct Hin.
    + rewrite Hother in Hlookup.
      * apply (type_fits_kept type_well_formed tenv tenv').
        -- intros x Hmem. exact (keeps_names_mem _ _ _ Hkeeps Hmem).
        -- exact Hkind.
        -- exact (Hfits n ty binding_time_and_mode Hlookup).
      * intros ->. rewrite (proj2 (name_eqb_eq _ _) eq_refl) in Hn.
        discriminate Hn.
Qed.
