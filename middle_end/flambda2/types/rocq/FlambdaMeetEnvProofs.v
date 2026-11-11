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
  FlambdaTypeWellFormedSpec FlambdaTypeWellFormedProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaEnvAliasesSpec
  FlambdaEnvAliasesProofs FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvProofs FlambdaTypingEnvInvariantSpec
  FlambdaTypingEnvInvariantProofs FlambdaTypingEnvOperationsSpec
  FlambdaTypingEnvOperationsProofs FlambdaTypingEnvKindedSpec
  FlambdaTypingEnvKindedProofs FlambdaMeetGrammar FlambdaExpandHead
  FlambdaMeetEnv FlambdaMeet FlambdaMeetSpec FlambdaMeetProofs
  FlambdaExpandHeadSpec FlambdaExpandHeadProofs FlambdaMeetStepsSpec
  FlambdaMeetStepsProofs FlambdaMeetEnvSpec.
Import ListNotations.

(* ======================================================================== *)
(* From one environment to another that has the same names                  *)
(* ======================================================================== *)

(* A type that fits an environment fits another in which the variables
   that were bound are bound and every simple has the kinds that it
   had. *)
Lemma type_fits_kept (tenv tenv' : Typing_env.t) (ty : flambda_type) :
  (∀ x : variable,
     Typing_env.mem None tenv (Name_var x) = true ->
     Typing_env.mem None tenv' (Name_var x) = true) ->
  (∀ (s : simple) (kind : flambda_kind),
     simple_of_kind tenv s kind -> simple_of_kind tenv' s kind) ->
  type_fits tenv ty ->
  type_fits tenv' ty.
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
  intros menv (Hinvariant & Hwf & Hkinded & Hbottom).
  split.
  - repeat split; try reflexivity.
    + intros s kind Hkind. apply make_bottom_simple_of_kind. exact Hkind.
    + intros x Hamong. exact Hamong.
    + intros n ty binding_time_and_mode Hlookup. exists ty.
      split; [ exact Hlookup | reflexivity ].
  - change (Meet_env.typing_env (Meet_env.make_bottom menv))
      with (Typing_env.make_bottom (Meet_env.typing_env menv)).
    split; [ exact (make_bottom_invariant _ Hinvariant) | ].
    split; [ exact (make_bottom_types_well_formed _ Hwf) | ].
    split; [ exact (make_bottom_kinded _ Hkinded) | ].
    intros Hfalse. discriminate Hfalse.
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
  intros menv var kind name_mode menv' (Hinvariant & Hwf & Hkinded & Hbottom)
    Hfresh.
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
    + exact Hkind.
    + intros x Hamong. exact Hamong.
    + exact Hkeeps.
  - change (Meet_env.typing_env menv') with tenv'.
    split.
    { exact (add_variable_definition_invariant tenv var kind name_mode
               Hinvariant Hfresh). }
    split.
    { exact (add_variable_definition_types_well_formed tenv var kind
               name_mode Hwf). }
    split.
    { exact (add_variable_definition_kinded tenv var kind name_mode
               (proj1 Hinvariant) Hfresh Hkinded). }
    intros Hnot_bottom n ty binding_time_and_mode Hlookup.
    destruct (name_eqb n (Name_var var)) eqn:Hn.
    + apply name_eqb_eq in Hn. subst n. unfold tenv' in Hlookup.
      rewrite add_variable_definition_names in Hlookup.
      rewrite (keyed_lookup_head name_eqb name_eqb_eq) in Hlookup.
      injection Hlookup as <- _. apply is_obviously_bottom_unknown.
    + rewrite Hother in Hlookup.
      * exact (Hbottom Hnot_bottom n ty binding_time_and_mode Hlookup).
      * intros ->. rewrite (proj2 (name_eqb_eq _ _) eq_refl) in Hn.
        discriminate Hn.
Qed.

(* ======================================================================== *)
(* The typing environment of a meet, extended                               *)
(* ======================================================================== *)

(* What [meet_env_extends] says of the two typing environments. *)
Definition tenv_extends (tenv tenv' : Typing_env.t) : Prop :=
  Typing_env.current_scope tenv' = Typing_env.current_scope tenv
  ∧ Typing_env.prev_levels tenv' = Typing_env.prev_levels tenv
  ∧ Typing_env.min_binding_time tenv' = Typing_env.min_binding_time tenv
  ∧ Typing_env.defined_symbols tenv' = Typing_env.defined_symbols tenv
  ∧ (∀ (s : simple) (kind : flambda_kind),
      simple_of_kind tenv s kind -> simple_of_kind tenv' s kind)
  ∧ keeps_names tenv tenv'.

Lemma tenv_extends_refl (tenv : Typing_env.t) : tenv_extends tenv tenv.
Proof.
  repeat split; try reflexivity.
  - intros s kind Hkind. exact Hkind.
  - apply keeps_names_refl.
Qed.

Lemma tenv_extends_trans (tenv1 tenv2 tenv3 : Typing_env.t) :
  tenv_extends tenv1 tenv2 -> tenv_extends tenv2 tenv3 ->
  tenv_extends tenv1 tenv3.
Proof.
  intros (Hs12 & Hp12 & Hm12 & Hd12 & Hkind12 & Hk12)
    (Hs23 & Hp23 & Hm23 & Hd23 & Hkind23 & Hk23).
  repeat split; try congruence.
  - intros s kind Hkind. exact (Hkind23 s kind (Hkind12 s kind Hkind)).
  - exact (keeps_names_trans _ _ _ Hk12 Hk23).
Qed.

Lemma meet_env_extends_tenv (menv menv' : Meet_env.t) :
  meet_env_extends menv menv' ->
  tenv_extends (Meet_env.typing_env menv) (Meet_env.typing_env menv').
Proof.
  intros (Hs & Hp & Hm & Hd & Hkind & _ & _ & Hk).
  repeat split; assumption.
Qed.

(* The environment of a meet with another typing environment that
   extends its own. *)
Lemma meet_env_extends_with (menv : Meet_env.t) (tenv' : Typing_env.t) :
  tenv_extends (Meet_env.typing_env menv) tenv' ->
  meet_env_extends menv (Meet_env.with_typing_env menv tenv').
Proof.
  intros (Hs & Hp & Hm & Hd & Hkind & Hk).
  repeat split; try assumption; try reflexivity.
  intros x Hamong. exact Hamong.
Qed.

(* A name that is bound stays bound. *)
Lemma tenv_extends_mem (tenv tenv' : Typing_env.t) (n : name) :
  tenv_extends tenv tenv' ->
  Typing_env.mem None tenv n = true ->
  Typing_env.mem None tenv' n = true.
Proof.
  intros (_ & _ & _ & Hd & _ & Hk) Hmem. destruct n as [ x | sym ].
  - exact (keeps_names_mem _ _ _ Hk Hmem).
  - unfold Typing_env.mem in *. rewrite Hd. exact Hmem.
Qed.

Lemma tenv_extends_type_fits (tenv tenv' : Typing_env.t)
    (ty : flambda_type) :
  tenv_extends tenv tenv' -> type_fits tenv ty -> type_fits tenv' ty.
Proof.
  intros Hextends. apply type_fits_kept.
  - intros x Hmem. exact (tenv_extends_mem _ _ _ Hextends Hmem).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 Hextends))))).
Qed.

(* What the invariant says of the names. *)
Lemma invariant_names (tenv : Typing_env.t) :
  typing_env_invariant tenv ->
  types_closed tenv ∧ symbols_defined tenv ∧ symbols_recorded tenv.
Proof.
  intros [Hwf _]. apply typing_env_well_formed_iff in Hwf.
  destruct Hwf as [[_ [_ [_ [Hclosed [Hsymbols Hrecorded]]]]] _].
  auto.
Qed.

(* A name that is of a kind is bound. *)
Lemma simple_of_kind_mem (tenv : Typing_env.t) (n : name)
    (kind : flambda_kind) :
  typing_env_invariant tenv ->
  simple_of_kind tenv (simple_of_name n) kind ->
  Typing_env.mem None tenv n = true.
Proof.
  intros Hinvariant Hkind.
  destruct (invariant_names tenv Hinvariant) as (_ & Hsymbols & _).
  apply simple_of_kind_name in Hkind.
  destruct Hkind as [ (ty & binding_time_and_mode & Hlookup & _)
                    | (_ & Hmem & _) ]; [ | exact Hmem ].
  destruct n as [ x | sym ].
  - apply mem_var_lookup. exists ty, binding_time_and_mode. exact Hlookup.
  - exact (Hsymbols sym ty binding_time_and_mode Hlookup).
Qed.

(* ======================================================================== *)
(* A name is given a type                                                   *)
(* ======================================================================== *)

Section Replace_equation.

Variable tenv : Typing_env.t.
Variable n : name.
Variable ty : flambda_type.

Hypothesis Hinvariant : typing_env_invariant tenv.
Hypothesis Hkind : simple_of_kind tenv (simple_of_name n) (kind ty).

Let tenv' := Typing_env.replace_equation tenv n ty.

(* The type that the name had is of the kind of the new one. *)
Lemma replace_equation_same_kind (ty0 : flambda_type)
    (binding_time_and_mode : Binding_time.With_name_mode.t) :
  Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
  = Some (ty0, binding_time_and_mode) ->
  kind ty = kind ty0.
Proof.
  intros Hlookup. apply simple_of_kind_name in Hkind.
  destruct Hkind as [ (ty1 & binding_time_and_mode1 & Hlookup1 & Hkind1)
                    | (Hnone & _) ].
  - rewrite Hlookup in Hlookup1. injection Hlookup1 as <- _.
    symmetry. exact Hkind1.
  - rewrite Hlookup in Hnone. discriminate Hnone.
Qed.

Lemma replace_equation_keeps_names : keeps_names tenv tenv'.
Proof.
  destruct (invariant_names tenv Hinvariant) as (_ & _ & Hrecorded).
  intros m ty0 binding_time_and_mode Hlookup.
  destruct (name_eqb m n) eqn:Hm.
  - apply name_eqb_eq in Hm. subst m. exists ty.
    split; [ | exact (replace_equation_same_kind _ _ Hlookup) ].
    unfold tenv'. rewrite replace_equation_lookup.
    destruct n as [ x | sym ].
    + rewrite Hlookup. reflexivity.
    + rewrite (Hrecorded sym ty0 binding_time_and_mode Hlookup).
      reflexivity.
  - exists ty0. split; [ | reflexivity ].
    unfold tenv'. rewrite replace_equation_lookup_other; [ exact Hlookup | ].
    intros ->. rewrite (proj2 (name_eqb_eq _ _) eq_refl) in Hm.
    discriminate Hm.
Qed.

Lemma replace_equation_tenv_extends : tenv_extends tenv tenv'.
Proof.
  assert (Hframe := replace_equation_frame tenv n ty). cbv zeta in Hframe.
  destruct Hframe as (Hsymbols & Hprev & Hscope & _ & _ & _ & Hmin & _).
  split; [ exact Hscope | ]. split; [ exact Hprev | ].
  split; [ exact Hmin | ]. split; [ exact Hsymbols | ].
  split; [ | exact replace_equation_keeps_names ].
  intros s kind0 Hs.
  exact (proj2 (replace_equation_simple_of_kind tenv n ty s kind0 Hkind) Hs).
Qed.

(* An environment that fits, with the new type for the name, fits: if
   the type fits, is not obviously bottom nor obviously unknown, and is
   not an alias unless the name is not canonical. *)
Lemma replace_equation_fits :
  typing_env_fits tenv ->
  type_fits tenv ty ->
  (∀ alias : simple,
     get_alias_opt ty = Some alias ->
     ~ is_canonical (Typing_env.aliases tenv) (simple_of_name n)) ->
  is_obviously_unknown ty = false ->
  is_obviously_bottom ty = false ->
  typing_env_fits tenv'.
Proof.
  intros (_ & Hwf & Hkinded & Hbottom) (Hty_wf & Hty_closed & Hty_kinded)
    Halias Hunknown Hnot_bottom.
  assert (Hmem := simple_of_kind_mem tenv n (kind ty) Hinvariant Hkind).
  split.
  { apply replace_equation_invariant; try assumption.
    - intros ty0 binding_time_and_mode Hlookup.
      exact (replace_equation_same_kind _ _ Hlookup).
    - left. exact Hunknown. }
  split; [ exact (replace_equation_types_well_formed tenv n ty Hty_wf Hwf) | ].
  split.
  { exact (replace_equation_kinded tenv n ty Hkind Hty_kinded Hkinded). }
  intros His_bottom m ty0 binding_time_and_mode Hlookup.
  destruct (name_eqb m n) eqn:Hm.
  - apply name_eqb_eq in Hm. subst m.
    unfold tenv' in Hlookup. rewrite replace_equation_lookup in Hlookup.
    assert (Hsame : ty0 = ty).
    { destruct n as [ x | sym ].
      - destruct (Keyed.lookup name_eqb (Name_var x)
                    (Typing_env.names_to_types tenv)) as [ entry | ];
          [ | discriminate Hlookup ].
        injection Hlookup as <- _. reflexivity.
      - injection Hlookup as <- _. reflexivity. }
    rewrite Hsame. exact Hnot_bottom.
  - unfold tenv' in Hlookup.
    rewrite replace_equation_lookup_other in Hlookup.
    + apply (Hbottom) with (n := m)
        (binding_time_and_mode := binding_time_and_mode);
        [ | exact Hlookup ].
      assert (Hframe := replace_equation_frame tenv n ty). cbv zeta in Hframe.
      destruct Hframe as (_ & _ & _ & _ & _ & _ & _ & Hsame & _).
      unfold tenv' in His_bottom. rewrite Hsame in His_bottom.
      exact His_bottom.
    + intros ->. rewrite (proj2 (name_eqb_eq _ _) eq_refl) in Hm.
      discriminate Hm.
Qed.

(* No equation is added but on the name. *)
Lemma replace_equation_valued (valuation : env) (v : value) :
  value_of_name valuation n = Some v ->
  keeps_equations_valued tenv tenv' valuation valuation.
Proof.
  intros Hv cut_after Hvalued one_level m ty0 Hin Hscope Hequation.
  assert (Hframe := replace_equation_frame tenv n ty). cbv zeta in Hframe.
  destruct Hframe as (_ & Hprev & Hcurrent_scope & _).
  fold tenv' in Hprev, Hcurrent_scope.
  destruct Hin as [ <- | Hin ].
  - destruct (replace_equation_equations tenv n m ty ty0 Hequation)
      as [ [-> _] | Hold ]; [ exists v; exact Hv | ].
    apply (Hvalued (Typing_env.current_level tenv) m ty0);
      [ left; reflexivity | | exact Hold ].
    exact (eq_ind _ (fun scope => (cut_after < scope)%Z) Hscope _
             Hcurrent_scope).
  - rewrite Hprev in Hin.
    exact (Hvalued one_level m ty0 (or_intror Hin) Hscope Hequation).
Qed.

End Replace_equation.

(* ======================================================================== *)
(* Two canonical elements are made aliases                                  *)
(* ======================================================================== *)

Lemma invariant_aliases_consistent (tenv : Typing_env.t) :
  typing_env_invariant tenv ->
  aliases_consistent (Typing_env.aliases tenv).
Proof.
  intros [Hwf _]. apply typing_env_well_formed_iff in Hwf.
  destruct Hwf as [_ [_ [Hconsistent _]]]. exact Hconsistent.
Qed.

Section Add_alias.

Variable tenv : Typing_env.t.
Variable canonical_element1 canonical_element2 : simple.
Variable result : Typing_env.add_alias_result.

Hypothesis Hadd :
  Typing_env.add_alias tenv canonical_element1 canonical_element2
  = Some (Ok result).

Let tenv' := Typing_env.add_alias_result_t result.

Lemma add_alias_tenv_extends : tenv_extends tenv tenv'.
Proof.
  assert (Hframe := add_alias_frame tenv _ _ result Hadd).
  cbv zeta in Hframe.
  destruct Hframe as (_ & Hsymbols & Hprev & Hcurrent & Hnames & _ & Hmin & _).
  fold tenv' in Hsymbols, Hprev, Hcurrent, Hnames, Hmin.
  split; [ unfold Typing_env.current_scope; rewrite Hcurrent; reflexivity | ].
  split; [ exact Hprev | ]. split; [ exact Hmin | ].
  split; [ exact Hsymbols | ]. split.
  - intros s kind Hs.
    exact (proj2 (add_alias_simple_of_kind tenv _ _ result s kind Hadd) Hs).
  - intros n ty binding_time_and_mode Hlookup. exists ty.
    split; [ | reflexivity ]. rewrite Hnames. exact Hlookup.
Qed.

Lemma add_alias_valued (valuation : env) :
  keeps_equations_valued tenv tenv' valuation valuation.
Proof.
  assert (Hframe := add_alias_frame tenv _ _ result Hadd).
  cbv zeta in Hframe.
  destruct Hframe as (_ & _ & Hprev & Hcurrent & _).
  fold tenv' in Hprev, Hcurrent.
  intros cut_after Hvalued one_level n ty Hin.
  rewrite Hprev, Hcurrent in Hin. exact (Hvalued one_level n ty Hin).
Qed.

Lemma add_alias_fits (kind : flambda_kind) :
  typing_env_fits tenv ->
  is_canonical (Typing_env.aliases tenv) canonical_element1 ->
  is_canonical (Typing_env.aliases tenv) canonical_element2 ->
  Typing_env.mem_simple None tenv canonical_element1 = true ->
  Typing_env.mem_simple None tenv canonical_element2 = true ->
  simple_of_kind tenv canonical_element1 kind ->
  simple_of_kind tenv canonical_element2 kind ->
  typing_env_fits tenv'.
Proof.
  intros (Hinvariant & Hwf & Hkinded & Hbottom) Hc1 Hc2 Hm1 Hm2 Hk1 Hk2.
  assert (Hframe := add_alias_frame tenv _ _ result Hadd).
  cbv zeta in Hframe.
  destruct Hframe as (_ & _ & _ & _ & Hnames & _ & _ & His_bottom).
  fold tenv' in Hnames, His_bottom.
  split.
  { exact (add_alias_invariant tenv _ _ result Hinvariant Hc1 Hc2 Hm1 Hm2
             Hadd). }
  split; [ exact (add_alias_types_well_formed tenv _ _ result Hadd Hwf) | ].
  split.
  { exact (add_alias_kinded tenv _ _ result kind
             (invariant_aliases_consistent tenv Hinvariant) Hc1 Hc2 Hk1 Hk2
             Hadd Hkinded). }
  intros Hnot_bottom n ty binding_time_and_mode Hlookup.
  rewrite Hnames in Hlookup. rewrite His_bottom in Hnot_bottom.
  exact (Hbottom Hnot_bottom n ty binding_time_and_mode Hlookup).
Qed.

(* The two that come out of it are the two that went in, and the one
   demoted is no longer canonical. *)
Lemma add_alias_demoted :
  typing_env_invariant tenv ->
  is_canonical (Typing_env.aliases tenv) canonical_element1 ->
  is_canonical (Typing_env.aliases tenv) canonical_element2 ->
  canonical_element1 <> canonical_element2 ->
  ((Typing_env.canonical_element result = canonical_element1
    ∧ simple_of_name (Typing_env.demoted_name result) = canonical_element2)
   ∨ (Typing_env.canonical_element result = canonical_element2
      ∧ simple_of_name (Typing_env.demoted_name result)
        = canonical_element1))
  ∧ ~ is_canonical (Typing_env.aliases tenv')
        (simple_of_name (Typing_env.demoted_name result)).
Proof.
  intros Hinvariant Hc1 Hc2 Hdifferent.
  assert (Hconsistent := invariant_aliases_consistent tenv Hinvariant).
  assert (Hframe := add_alias_frame tenv _ _ result Hadd).
  cbv zeta in Hframe.
  destruct Hframe
    as ((added & Hadded & Haliases & Hcanonical & Hdemoted) & _).
  fold tenv' in Haliases.
  assert (Hresult := add_result _ _ _ _ _ _ added Hadded).
  assert (Hwhich :
    (Typing_env.canonical_element result = canonical_element1
     ∧ simple_of_name (Typing_env.demoted_name result) = canonical_element2)
    ∨ (Typing_env.canonical_element result = canonical_element2
       ∧ simple_of_name (Typing_env.demoted_name result)
         = canonical_element1)).
  { rewrite Hcanonical, Hdemoted.
    destruct (Aliases.defined_earlier _ _ canonical_element1
                canonical_element2); [ left | right ]; exact Hresult. }
  split; [ exact Hwhich | ].
  intros Hstill.
  assert (Hof :=
    add_canonical_element _ _ _ _ _ _ added
      (simple_of_name (Typing_env.demoted_name result)) Hconsistent Hc1 Hc2
      Hadded).
  rewrite <- Haliases in Hof.
  rewrite (canonical_element_of_canonical _ _ Hstill) in Hof.
  assert (Hwas :
    canonical_element_of (Typing_env.aliases tenv)
      (simple_of_name (Typing_env.demoted_name result))
    = simple_of_name (Typing_env.demoted_name result)).
  { apply canonical_element_of_canonical.
    destruct Hwhich as [ [_ ->] | [_ ->] ]; assumption. }
  rewrite Hwas, <- Hdemoted in Hof.
  rewrite (proj2 (simple_equal_eq _ _) eq_refl) in Hof.
  rewrite <- Hcanonical in Hof.
  destruct Hwhich as [ [H1 H2] | [H1 H2] ]; congruence.
Qed.

End Add_alias.

(* ======================================================================== *)
(* Facts about types                                                        *)
(* ======================================================================== *)

Lemma kind_alias_type_of (k : flambda_kind) (s : simple) :
  kind (alias_type_of k s) = k.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma get_alias_opt_alias_type_of (k : flambda_kind) (s : simple) :
  get_alias_opt (alias_type_of k s) = Some s.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma aliases_with_kinds_alias_type_of (k : flambda_kind) (s : simple) :
  aliases_with_kinds (alias_type_of k s) = [(s, k)].
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma free_variables_alias_type_of (k : flambda_kind) (s : simple)
    (x : variable) :
  x ∈ free_variables (alias_type_of k s) -> s = Var x.
Proof.
  destruct k as [ | [] | | ]; destruct s as [ y | sym | c ]; cbn;
    intros Hin; try contradiction; destruct Hin as [ -> | [] ]; reflexivity.
Qed.

Lemma is_obviously_unknown_alias_type_of (k : flambda_kind) (s : simple) :
  is_obviously_unknown (alias_type_of k s) = false.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma is_obviously_bottom_alias_type_of (k : flambda_kind) (s : simple) :
  is_obviously_bottom (alias_type_of k s) = false.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma kind_type_for_const (c : const) :
  kind (type_for_const c) = kind_of_const c.
Proof.
  destruct c as [i | i | f | f | i | i | i | i | i | i | i | i | i | | k];
    try reflexivity.
  apply kind_unknown.
Qed.

(* The constant that a type that is not an alias has for only value is
   of the kind of the type. *)
Lemma must_be_singleton_kind (ty : flambda_type) (c : const) :
  get_alias_opt ty = None ->
  must_be_singleton ty = Some (Some c) ->
  kind_of_const c = kind ty.
Proof.
  destruct ty as [ descr | descr | k descr | descr | descr ];
    destruct descr as [ | [ head | s ] | ]; cbn;
    try discriminate.
  - intros _.
    destruct head as [ [ | [ ? immediates ? blocks ? ? | | | | ] | ] [ | ] ];
      try discriminate.
    destruct blocks as [ blocks | ]; [ | discriminate ].
    destruct (negb (row_like_for_blocks_is_bottom blocks));
      [ discriminate | ].
    destruct immediates as [ immediates | ]; [ | discriminate ].
    destruct (must_be_singleton immediates) as [ [ c0 | ] | ];
      try discriminate.
    destruct c0 as [i | i | f | f | i | i | i | i | i | i | i | i | i | | k];
      try discriminate; try (intros [= <-]; reflexivity).
    destruct k as [ | [] | | ]; try discriminate.
    intros [= <-]. reflexivity.
  - intros _. destruct (naked_immediates head) as [ numbers | ];
      [ | discriminate ].
    destruct (Keyed.get_singleton Z.eqb numbers); [ | discriminate ].
    intros [= <-]. reflexivity.
  - intros _. destruct (Keyed.get_singleton Z.eqb head); [ | discriminate ].
    intros [= <-]. destruct k; reflexivity.
Qed.

(* A type made of an expanded type is not an alias. *)
Lemma get_alias_opt_to_type (expanded : Expanded_type.t) :
  get_alias_opt (Expanded_type.to_type expanded) = None.
Proof.
  destruct expanded as [k [ | [ ] | ]]; cbn; try reflexivity;
    destruct k as [ | [] | | ]; reflexivity.
Qed.

(* ======================================================================== *)
(* The functions that add an equation: what they keep                       *)
(* ======================================================================== *)

(* What is used of the predicate of well-formed types, beside what
   its own file states: the type of a constant, expanded, is well
   formed, and a well-formed type that is not an alias is the type
   made of what it expands to. *)
Lemma to_type_create_const_well_formed (c : const) :
  type_well_formed (Expanded_type.to_type (Expanded_type.create_const c))
  = true.
Proof.
  destruct c as [i | i | f | f | i | i | i | i | i | i | i | i | i | | k];
    try reflexivity.
  apply unknown_well_formed.
Qed.

Lemma of_non_alias_type_well_formed (ty : flambda_type)
    (expanded : Expanded_type.t) :
  Expanded_type.of_non_alias_type ty = Some expanded ->
  type_well_formed ty = true ->
  type_well_formed (Expanded_type.to_type expanded) = true.
Proof.
  intros Hexpanded Hwf.
  destruct ty as [ descr | descr | k descr | descr | descr ];
    destruct descr as [ | [ head | s ] | ]; cbn in Hexpanded;
    try discriminate Hexpanded; injection Hexpanded as <-;
    try exact Hwf; try reflexivity.
  - destruct k; try reflexivity; discriminate Hwf.
  - destruct k; try reflexivity; discriminate Hwf.
Qed.

Section Keeps.

Lemma mem_simple_of_name (tenv : Typing_env.t) (n : name) :
  Typing_env.mem_simple None tenv (simple_of_name n)
  = Typing_env.mem None tenv n.
Proof. destruct n; reflexivity. Qed.

Lemma type_fits_alias (tenv : Typing_env.t) (k : flambda_kind) (s : simple) :
  Typing_env.mem_simple None tenv s = true ->
  simple_of_kind tenv s k ->
  type_fits tenv (alias_type_of k s).
Proof.
  intros Hmem Hkind. split; [ apply alias_type_of_well_formed | ]. split.
  - intros x Hin. apply free_variables_alias_type_of in Hin. subst s.
    exact Hmem.
  - intros s' k' Hin. rewrite aliases_with_kinds_alias_type_of in Hin.
    destruct Hin as [ [= <- <-] | [] ]. exact Hkind.
Qed.

Lemma type_fits_of_non_alias (tenv : Typing_env.t) (ty : flambda_type)
    (expanded : Expanded_type.t) :
  Expanded_type.of_non_alias_type ty = Some expanded ->
  type_fits tenv ty ->
  type_fits tenv (Expanded_type.to_type expanded).
Proof.
  intros Hexpanded (Hwf & Hclosed & Hkinded).
  split; [ exact (of_non_alias_type_well_formed ty expanded Hexpanded Hwf) | ].
  split.
  - intros x Hin.
    rewrite (of_non_alias_type_free_variables ty expanded Hexpanded) in Hin.
    exact (Hclosed x Hin).
  - intros s k Hin.
    rewrite (of_non_alias_type_aliases ty expanded Hexpanded) in Hin.
    exact (Hkinded s k Hin).
Qed.

(* The type that an environment that fits answers for a name fits. *)
Lemma find_type_fits (tenv : Typing_env.t) (n : name)
    (kind : option flambda_kind) (ty : flambda_type) :
  typing_env_fits tenv ->
  Typing_env.find tenv n kind = Some ty ->
  type_fits tenv ty.
Proof.
  intros Hfits Hfind.
  destruct (find_cases tenv n kind ty Hfind)
    as [ [binding_time_and_mode Hlookup] | [ [k ->] | -> ] ].
  - exact (fits_types tenv n ty binding_time_and_mode Hfits Hlookup).
  - split; [ apply bottom_well_formed | ]. split.
    + intros x Hin. rewrite free_variables_bottom in Hin. destruct Hin.
    + intros s k' Hin. rewrite bottom_aliases in Hin. destruct Hin.
  - split; [ exact any_non_null_value_well_formed | ]. split.
    + intros x Hin. destruct Hin.
    + intros s k' Hin. destruct Hin.
Qed.

(* [replace_concrete_equation]. *)
Lemma replace_concrete_equation_keeps (tenv tenv' : Typing_env.t) (n : name)
    (ty : flambda_type) :
  typing_env_fits tenv ->
  type_fits tenv ty ->
  simple_of_kind tenv (simple_of_name n) (kind ty) ->
  get_alias_opt ty = None ->
  is_obviously_unknown ty = false ->
  is_obviously_bottom ty = false ->
  Meet_env.replace_concrete_equation tenv n ty = Some tenv' ->
  tenv_extends tenv tenv' ∧ typing_env_fits tenv'.
Proof.
  intros Hfits Hty Hkind Hconcrete Hunknown Hbottom Hreplace.
  assert (Hinvariant := proj1 Hfits).
  unfold Meet_env.replace_concrete_equation in Hreplace.
  destruct (must_be_singleton ty) as [ [ const | ] | ] eqn:Hsingleton;
    [ | | discriminate Hreplace ]; cbn in Hreplace.
  - (* The name becomes an alias of the constant. *)
    destruct (Aliases.canonical (Typing_env.aliases tenv) (simple_of_name n))
      eqn:Hcanonical; [ | discriminate Hreplace ].
    destruct (Typing_env.add_alias tenv (simple_of_name n) (Const const))
      as [ [ | result | ] | ] eqn:Hadd; try discriminate Hreplace.
    cbn in Hreplace.
    destruct (name_eqb (Typing_env.demoted_name result) n
              && simple_equal (Typing_env.canonical_element result)
                   (Const const)) eqn:Hcheck; [ | discriminate Hreplace ].
    injection Hreplace as <-.
    apply andb_true_iff in Hcheck. destruct Hcheck as [Hdemoted Hconst].
    apply name_eqb_eq in Hdemoted. apply simple_equal_eq in Hconst.
    rewrite Hdemoted, Hconst.
    assert (Hkind_const : kind_of_const const = kind ty).
    { exact (must_be_singleton_kind ty const Hconcrete Hsingleton). }
    assert (Hconst_kind : simple_of_kind tenv (Const const) (kind ty)).
    { cbn. rewrite kind_type_for_const. exact Hkind_const. }
    assert (Hmem : Typing_env.mem_simple None tenv (simple_of_name n) = true).
    { rewrite mem_simple_of_name.
      exact (simple_of_kind_mem tenv n (kind ty) Hinvariant Hkind). }
    assert (Hextends1 := add_alias_tenv_extends tenv _ _ result Hadd).
    assert (Hfits1 :=
      add_alias_fits tenv _ _ result Hadd (kind ty) Hfits
        Hcanonical eq_refl Hmem eq_refl Hkind Hconst_kind).
    set (tenv1 := Typing_env.add_alias_result_t result) in *.
    set (alias := alias_type_of (kind_of_const const) (Const const)).
    assert (Hkind1 : simple_of_kind tenv1 (simple_of_name n) (kind alias)).
    { unfold alias. rewrite kind_alias_type_of, Hkind_const.
      exact (proj1 (proj2 (proj2 (proj2 (proj2 Hextends1)))) _ _ Hkind). }
    split.
    + exact (tenv_extends_trans _ _ _ Hextends1
               (replace_equation_tenv_extends tenv1 n alias (proj1 Hfits1)
                  Hkind1)).
    + apply (replace_equation_fits tenv1 n alias (proj1 Hfits1) Hkind1
               Hfits1).
      * apply type_fits_alias; [ reflexivity | ].
        cbn. apply kind_type_for_const.
      * intros s _.
        destruct (add_alias_demoted tenv _ _ result Hadd Hinvariant
                    Hcanonical eq_refl) as [_ Hnot].
        { destruct n; discriminate. }
        rewrite Hdemoted in Hnot. exact Hnot.
      * apply is_obviously_unknown_alias_type_of.
      * apply is_obviously_bottom_alias_type_of.
  - (* The name gets the type. *)
    rewrite Hconcrete in Hreplace. injection Hreplace as <-.
    split.
    + exact (replace_equation_tenv_extends tenv n ty Hinvariant Hkind).
    + apply (replace_equation_fits tenv n ty Hinvariant Hkind Hfits
               Hty); try assumption.
      intros s Hs. rewrite Hconcrete in Hs. discriminate Hs.
Qed.

(* The meet that the functions are given. *)
Variable mh : meet_expanded_head.
Hypothesis Hmh : meet_expanded_head_keeps mh.

Lemma simple_of_kind_of_find (tenv : Typing_env.t) (n : name)
    (kind : flambda_kind) (ty : flambda_type) :
  Typing_env.find tenv n (Some kind) = Some ty ->
  simple_of_kind tenv (simple_of_name n) kind.
Proof. intros Hfind. destruct n; exists ty; exact Hfind. Qed.

(* [add_concrete_equation_on_canonical_name]. *)
Lemma add_concrete_equation_on_canonical_name_keeps (menv menv' : Meet_env.t)
    (n : name) (ty : Expanded_type.t) :
  typing_env_fits (Meet_env.typing_env menv) ->
  type_fits (Meet_env.typing_env menv)
    (Expanded_type.to_type ty) ->
  Expanded_type.kind ty = kind (Expanded_type.to_type ty) ->
  Meet_env.add_concrete_equation_on_canonical_name true menv n ty mh
  = Some (Or_bottom.Ok menv') ->
  meet_env_extends menv menv'
  ∧ typing_env_fits (Meet_env.typing_env menv').
Proof.
  intros Hfits Hty Hcoherent Hadd.
  unfold Meet_env.add_concrete_equation_on_canonical_name in Hadd.
  destruct (Typing_env.find (Meet_env.typing_env menv) n
              (Some (Expanded_type.kind ty)))
    as [ existing | ] eqn:Hfind; [ | discriminate Hadd ].
  cbn in Hadd.
  destruct (Expanded_type.of_non_alias_type existing)
    as [ existing_ty | ] eqn:Hexisting; [ | discriminate Hadd ].
  cbn in Hadd.
  destruct (mh menv ty existing_ty) as [ result | ] eqn:Hmeet;
    [ | discriminate Hadd ].
  cbn in Hadd.
  destruct result as [ r0 | r menv1 ]; [ discriminate Hadd | ].
  assert (Hinputs :
    meet_inputs_well_formed (Meet_env.typing_env menv)
      (Expanded_type.to_type ty) (Expanded_type.to_type existing_ty)).
  { split; [ exact Hfits | ]. split; [ exact Hty | ]. split.
    - exact (type_fits_of_non_alias _ _ _ Hexisting
               (find_type_fits _ _ _ _ Hfits Hfind)).
    - rewrite (proj2 (of_non_alias_type_kind _ _ Hexisting)).
      rewrite (find_kind _ _ _ _ Hfind). symmetry. exact Hcoherent. }
  destruct (Hmh menv menv1 ty existing_ty r Hinputs Hmeet)
    as (Hextends1 & Hfits1 & Hanswer & Hkind_answer & Hnot_bottom
        & Hunknown).
  assert (Hreplace :
    ∀ (answer : Expanded_type.t) (tenv2 : Typing_env.t),
      extract_value r ty existing_ty = answer ->
      (r = Left_input ∨ r = New_result answer) ->
      Meet_env.replace_concrete_equation (Meet_env.typing_env menv1) n
        (Expanded_type.to_type answer)
      = Some tenv2 ->
      meet_env_extends menv (Meet_env.with_typing_env menv1 tenv2)
      ∧ typing_env_fits tenv2).
  { intros answer tenv2 Hextract Hr Hreplace. rewrite Hextract in *.
    assert (Hkind_n :
      simple_of_kind (Meet_env.typing_env menv1) (simple_of_name n)
        (kind (Expanded_type.to_type answer))).
    { rewrite Hkind_answer, <- Hcoherent.
      apply (proj1 (proj2 (proj2 (proj2 (proj2
               (meet_env_extends_tenv _ _ Hextends1)))))).
      exact (simple_of_kind_of_find _ _ _ _ Hfind). }
    destruct (replace_concrete_equation_keeps _ tenv2 n _ Hfits1 Hanswer
                Hkind_n (get_alias_opt_to_type answer))
      as [Hextends2 Hfits2]; try assumption.
    - destruct (is_obviously_unknown (Expanded_type.to_type answer));
        [ | reflexivity ].
      destruct (Hunknown eq_refl) as [ -> | -> ];
        destruct Hr as [ Hr | Hr ]; discriminate Hr.
    - split; [ | exact Hfits2 ].
      exact (meet_env_extends_trans _ _ _ Hextends1
               (meet_env_extends_with menv1 tenv2 Hextends2)). }
  destruct r as [ | | | answer ].
  - destruct (Meet_env.replace_concrete_equation (Meet_env.typing_env menv1)
                n (Expanded_type.to_type ty))
      as [ tenv2 | ] eqn:Hreplaced; [ | discriminate Hadd ].
    injection Hadd as <-.
    exact (Hreplace ty tenv2 eq_refl (or_introl eq_refl) Hreplaced).
  - injection Hadd as <-. split; assumption.
  - injection Hadd as <-. split; assumption.
  - destruct (Meet_env.replace_concrete_equation (Meet_env.typing_env menv1)
                n (Expanded_type.to_type answer))
      as [ tenv2 | ] eqn:Hreplaced; [ | discriminate Hadd ].
    injection Hadd as <-.
    exact (Hreplace answer tenv2 eq_refl (or_intror eq_refl) Hreplaced).
Qed.

(* [adding_equation_for_name]. *)
Lemma adding_equation_for_name_keeps (menv menv' : Meet_env.t) (n : name)
    (f : Meet_env.t -> option (Or_bottom.t Meet_env.t)) :
  (∀ menv1 menv2 : Meet_env.t,
     Meet_env.typing_env menv1 = Meet_env.typing_env menv ->
     f menv1 = Some (Or_bottom.Ok menv2) ->
     meet_env_extends menv1 menv2
     ∧ typing_env_fits (Meet_env.typing_env menv2)) ->
  Meet_env.adding_equation_for_name menv n f = Some (Or_bottom.Ok menv') ->
  meet_env_extends menv menv'
  ∧ typing_env_fits (Meet_env.typing_env menv').
Proof.
  intros Hf Hadding. unfold Meet_env.adding_equation_for_name in Hadding.
  match type of Hadding with
  | context [ f ?env ] =>
    destruct (f env) as [ [ menv2 | ] | ] eqn:Hrun;
      try discriminate Hadding;
      destruct (Hf env menv2 eq_refl Hrun) as [Hextends Hfits]
  end.
  injection Hadding as <-. split; [ | exact Hfits ].
  destruct Hextends as (Hs & Hp & Hm & Hd & Hkind & _ & Hv & Hk).
  exact (conj Hs (conj Hp (conj Hm (conj Hd (conj Hkind (conj eq_refl
           (conj Hv Hk))))))).
Qed.

(* [add_or_delay_concrete_equation_on_canonical_name]. *)
Lemma add_or_delay_concrete_equation_on_canonical_name_keeps
    (menv menv' : Meet_env.t) (n : name) (ty : Expanded_type.t) :
  typing_env_fits (Meet_env.typing_env menv) ->
  type_fits (Meet_env.typing_env menv)
    (Expanded_type.to_type ty) ->
  Expanded_type.kind ty = kind (Expanded_type.to_type ty) ->
  Meet_env.add_or_delay_concrete_equation_on_canonical_name true menv n ty mh
  = Some (Or_bottom.Ok menv') ->
  meet_env_extends menv menv'
  ∧ typing_env_fits (Meet_env.typing_env menv').
Proof.
  intros Hfits Hty Hcoherent Hadd.
  unfold Meet_env.add_or_delay_concrete_equation_on_canonical_name in Hadd.
  destruct (Keyed.among name_eqb n (Meet_env.adding_equations_for_names menv)).
  - injection Hadd as <-.
    split; [ apply meet_env_extends_refl | exact Hfits ].
  - apply (adding_equation_for_name_keeps menv menv' n _) in Hadd;
      [ exact Hadd | ].
    intros menv1 menv2 Hsame Hrun.
    apply (add_concrete_equation_on_canonical_name_keeps menv1 menv2 n ty);
      try assumption; rewrite Hsame; assumption.
Qed.

(* [add_concrete_equation_on_const]. *)
Lemma add_concrete_equation_on_const_keeps (menv menv' : Meet_env.t)
    (const : const) (ty : Expanded_type.t) :
  typing_env_fits (Meet_env.typing_env menv) ->
  type_fits (Meet_env.typing_env menv)
    (Expanded_type.to_type ty) ->
  kind (type_for_const const) = kind (Expanded_type.to_type ty) ->
  Meet_env.add_concrete_equation_on_const true menv const ty mh
  = Some (Or_bottom.Ok menv') ->
  meet_env_extends menv menv'
  ∧ typing_env_fits (Meet_env.typing_env menv').
Proof.
  intros Hfits Hty Hkind Hadd.
  unfold Meet_env.add_concrete_equation_on_const in Hadd.
  destruct (mh menv ty (Expanded_type.create_const const))
    as [ [ r0 | r menv1 ] | ] eqn:Hmeet; try discriminate Hadd.
  injection Hadd as <-.
  assert (Hinputs :
    meet_inputs_well_formed (Meet_env.typing_env menv)
      (Expanded_type.to_type ty)
      (Expanded_type.to_type (Expanded_type.create_const const))).
  { split; [ exact Hfits | ]. split; [ exact Hty | ]. split.
    - split; [ apply to_type_create_const_well_formed | ]. split.
      + intros x Hin. rewrite create_const_free_variables in Hin.
        destruct Hin.
      + apply create_const_kinded.
    - rewrite (proj2 (create_const_kind const)). symmetry. exact Hkind. }
  destruct (Hmh menv menv1 ty _ r Hinputs Hmeet) as (Hextends & Hfits1 & _).
  split; assumption.
Qed.

(* [add_or_delay_concrete_equation_on_canonical]. *)
Lemma add_or_delay_concrete_equation_on_canonical_keeps
    (menv menv' : Meet_env.t) (canonical : simple) (ty : Expanded_type.t) :
  typing_env_fits (Meet_env.typing_env menv) ->
  type_fits (Meet_env.typing_env menv)
    (Expanded_type.to_type ty) ->
  Expanded_type.kind ty = kind (Expanded_type.to_type ty) ->
  simple_of_kind (Meet_env.typing_env menv) canonical
    (kind (Expanded_type.to_type ty)) ->
  Meet_env.add_or_delay_concrete_equation_on_canonical true menv canonical ty
    mh
  = Some (Or_bottom.Ok menv') ->
  meet_env_extends menv menv'
  ∧ typing_env_fits (Meet_env.typing_env menv').
Proof.
  intros Hfits Hty Hcoherent Hkind Hadd.
  destruct canonical as [ x | sym | const ]; cbn in Hadd.
  - exact (add_or_delay_concrete_equation_on_canonical_name_keeps _ _ _ _
             Hfits Hty Hcoherent Hadd).
  - exact (add_or_delay_concrete_equation_on_canonical_name_keeps _ _ _ _
             Hfits Hty Hcoherent Hadd).
  - exact (add_concrete_equation_on_const_keeps _ _ _ _ Hfits Hty Hkind Hadd).
Qed.

(* ------------------------------------------------------------------------ *)
(* Canonical elements                                                       *)
(* ------------------------------------------------------------------------ *)

Lemma invariant_aliases_known (tenv : Typing_env.t) :
  typing_env_invariant tenv -> aliases_known tenv.
Proof.
  intros [Hwf _]. apply typing_env_well_formed_iff in Hwf.
  destruct Hwf as (_ & _ & _ & _ & Hknown & _). exact Hknown.
Qed.

(* A simple that is of a kind is bound. *)
Lemma simple_of_kind_mem_simple (tenv : Typing_env.t) (s : simple)
    (kind : flambda_kind) :
  typing_env_invariant tenv ->
  simple_of_kind tenv s kind ->
  Typing_env.mem_simple None tenv s = true.
Proof.
  intros Hinvariant Hkind. destruct s as [ x | sym | c ]; [ | | reflexivity ].
  - exact (simple_of_kind_mem tenv (Name_var x) kind Hinvariant Hkind).
  - exact (simple_of_kind_mem tenv (Name_symbol sym) kind Hinvariant Hkind).
Qed.

(* A simple that is bound is of some kind. *)
Lemma mem_simple_of_some_kind (tenv : Typing_env.t) (s : simple) :
  Typing_env.mem_simple None tenv s = true ->
  ∃ kind : flambda_kind, simple_of_kind tenv s kind.
Proof.
  intros Hmem.
  assert (Hname :
    ∀ n : name,
      Typing_env.mem None tenv n = true ->
      ∃ kind : flambda_kind, simple_of_kind tenv (simple_of_name n) kind).
  { intros n Hn.
    destruct (Keyed.lookup name_eqb n (Typing_env.names_to_types tenv))
      as [ [ty binding_time_and_mode] | ] eqn:Hlookup.
    - exists (kind ty). apply simple_of_kind_name. left.
      exists ty, binding_time_and_mode. split; [ exact Hlookup | reflexivity ].
    - exists Value. apply simple_of_kind_name. right. auto. }
  destruct s as [ x | sym | c ].
  - exact (Hname (Name_var x) Hmem).
  - exact (Hname (Name_symbol sym) Hmem).
  - exists (kind (type_for_const c)). reflexivity.
Qed.

Lemma tenv_extends_mem_simple (tenv tenv' : Typing_env.t) (s : simple) :
  tenv_extends tenv tenv' ->
  Typing_env.mem_simple None tenv s = true ->
  Typing_env.mem_simple None tenv' s = true.
Proof.
  intros Hextends Hmem. destruct s as [ x | sym | c ]; [ | | reflexivity ].
  - exact (tenv_extends_mem _ _ (Name_var x) Hextends Hmem).
  - exact (tenv_extends_mem _ _ (Name_symbol sym) Hextends Hmem).
Qed.

Lemma get_canonical_simple_ignoring_name_mode_eq (tenv : Typing_env.t)
    (s : simple) :
  Typing_env.get_canonical_simple_ignoring_name_mode tenv s
  = canonical_element_of (Typing_env.aliases tenv) s.
Proof.
  destruct s as [ x | sym | c ]; [ | | reflexivity ].
  - exact (get_canonical_ignoring_name_mode _ (Name_var x)).
  - exact (get_canonical_ignoring_name_mode _ (Name_symbol sym)).
Qed.

(* The canonical element of a simple that is of a kind is canonical and
   of that kind. *)
Lemma canonical_of_kind (tenv : Typing_env.t) (s : simple)
    (kind : flambda_kind) :
  typing_env_invariant tenv ->
  aliases_kinded tenv ->
  simple_of_kind tenv s kind ->
  is_canonical (Typing_env.aliases tenv)
    (Typing_env.get_canonical_simple_ignoring_name_mode tenv s)
  ∧ simple_of_kind tenv
      (Typing_env.get_canonical_simple_ignoring_name_mode tenv s) kind.
Proof.
  intros Hinvariant Hkinded Hkind.
  rewrite get_canonical_simple_ignoring_name_mode_eq.
  assert (Hconsistent := invariant_aliases_consistent tenv Hinvariant).
  split; [ exact (canonical_element_canonical _ s Hconsistent) | ].
  destruct (canonical_cases (Typing_env.aliases tenv) s)
    as [ [_ ->] | (n & canonical_element & -> & Hdemoted & _ & Hof) ];
    [ exact Hkind | ].
  destruct (invariant_aliases_known tenv Hinvariant n canonical_element
              Hdemoted) as [_ Hmem].
  destruct (mem_simple_of_some_kind tenv canonical_element Hmem)
    as [kind' Hkind'].
  rewrite Hof.
  assert (Hsame : kind = kind').
  { apply (Hkinded (simple_of_name n) canonical_element kind kind');
      [ | exact Hkind | exact Hkind' ].
    unfold aliased. rewrite Hof. symmetry.
    apply canonical_element_of_canonical. rewrite <- Hof.
    exact (canonical_element_canonical _ _ Hconsistent). }
  rewrite Hsame. exact Hkind'.
Qed.

(* ------------------------------------------------------------------------ *)
(* A name is demoted                                                        *)
(* ------------------------------------------------------------------------ *)

(* [record_demotion]. *)
Lemma record_demotion_keeps (menv menv' : Meet_env.t) (kind : flambda_kind)
    (demoted : name) (canonical : simple) :
  typing_env_fits (Meet_env.typing_env menv) ->
  ~ is_canonical (Typing_env.aliases (Meet_env.typing_env menv))
      (simple_of_name demoted) ->
  simple_of_kind (Meet_env.typing_env menv) (simple_of_name demoted) kind ->
  simple_of_kind (Meet_env.typing_env menv) canonical kind ->
  Meet_env.record_demotion true menv kind demoted canonical mh
  = Some (Or_bottom.Ok menv') ->
  meet_env_extends menv menv'
  ∧ typing_env_fits (Meet_env.typing_env menv').
Proof.
  intros Hfits Hnot_canonical Hkind_demoted Hkind_canonical Hrecord.
  assert (Hinvariant := proj1 Hfits).
  set (tenv := Meet_env.typing_env menv) in *.
  unfold Meet_env.record_demotion in Hrecord.
  fold tenv in Hrecord.
  destruct (Typing_env.find tenv demoted (Some kind))
    as [ ty_of_demoted | ] eqn:Hfind; [ | discriminate Hrecord ].
  cbv beta iota in Hrecord.
  set (alias := alias_type_of kind canonical) in *.
  set (menv1 :=
    Meet_env.map_typing_env menv
      (fun tenv => Typing_env.replace_equation tenv demoted alias)) in *.
  set (tenv1 := Typing_env.replace_equation tenv demoted alias).
  assert (Hkind_alias :
    simple_of_kind tenv (simple_of_name demoted)
      (FlambdaTypeGrammar.kind alias)).
  { unfold alias. rewrite kind_alias_type_of. exact Hkind_demoted. }
  assert (Hextends1 : tenv_extends tenv tenv1).
  { exact (replace_equation_tenv_extends tenv demoted alias Hinvariant
             Hkind_alias). }
  assert (Hfits1 : typing_env_fits tenv1).
  { apply (replace_equation_fits tenv demoted alias Hinvariant Hkind_alias
             Hfits).
    - apply type_fits_alias; [ | exact Hkind_canonical ].
      exact (simple_of_kind_mem_simple tenv canonical kind Hinvariant
               Hkind_canonical).
    - intros s _. exact Hnot_canonical.
    - apply is_obviously_unknown_alias_type_of.
    - apply is_obviously_bottom_alias_type_of. }
  change (Meet_env.typing_env menv1) with tenv1 in Hrecord.
  destruct (expand_head0 tenv1 ty_of_demoted (Some (simple_of_name demoted)))
    as [ expanded | ] eqn:Hexpand; [ | discriminate Hrecord ].
  cbv beta iota in Hrecord.
  assert (Hkind_found : FlambdaTypeGrammar.kind ty_of_demoted = kind).
  { exact (find_kind _ _ _ _ Hfind). }
  assert (Hexpanded :
    type_fits tenv1 (Expanded_type.to_type expanded)
    ∧ Expanded_type.kind expanded = kind
    ∧ FlambdaTypeGrammar.kind (Expanded_type.to_type expanded) = kind).
  { unfold expand_head0 in Hexpand.
    destruct (get_alias_opt ty_of_demoted) as [ s | ].
    - unfold expand_head_of_alias_type in Hexpand.
      assert (Hfound :
        ∃ found : flambda_type,
          Typing_env.find tenv1 demoted
            (Some (FlambdaTypeGrammar.kind ty_of_demoted))
          = Some found
          ∧ Expanded_type.of_non_alias_type found = Some expanded).
      { destruct demoted as [ x | sym ]; cbn [simple_of_name] in Hexpand;
          destruct (Typing_env.find tenv1 _
                      (Some (FlambdaTypeGrammar.kind ty_of_demoted)))
            as [ found | ] eqn:Hfound; try discriminate Hexpand;
          exists found; (split; [ reflexivity | exact Hexpand ]). }
      destruct Hfound as (found & Hfound & Hof).
      split.
      + exact (type_fits_of_non_alias _ _ _ Hof
                 (find_type_fits _ _ _ _ Hfits1 Hfound)).
      + destruct (of_non_alias_type_kind _ _ Hof) as [-> ->].
        rewrite (find_kind _ _ _ _ Hfound). auto.
    - split.
      + apply (type_fits_of_non_alias _ _ _ Hexpand).
        apply (tenv_extends_type_fits _ _ _ Hextends1).
        exact (find_type_fits _ _ _ _ Hfits Hfind).
      + destruct (of_non_alias_type_kind _ _ Hexpand) as [-> ->]. auto. }
  destruct Hexpanded as (Hty & Hkind1 & Hkind2).
  destruct (add_or_delay_concrete_equation_on_canonical_keeps menv1 menv'
              canonical expanded Hfits1 Hty) as [Hextends2 Hfits2].
  - rewrite Hkind1, Hkind2. reflexivity.
  - rewrite Hkind2.
    exact (proj1 (proj2 (proj2 (proj2 (proj2 Hextends1)))) _ _
             Hkind_canonical).
  - exact Hrecord.
  - split; [ | exact Hfits2 ].
    exact (meet_env_extends_trans _ _ _
             (meet_env_extends_with menv tenv1 Hextends1) Hextends2).
Qed.

(* [add_alias_between_canonicals]. *)
Lemma add_alias_between_canonicals_keeps (menv menv' : Meet_env.t)
    (kind : flambda_kind) (canonical_element1 canonical_element2 : simple) :
  typing_env_fits (Meet_env.typing_env menv) ->
  is_canonical (Typing_env.aliases (Meet_env.typing_env menv))
    canonical_element1 ->
  is_canonical (Typing_env.aliases (Meet_env.typing_env menv))
    canonical_element2 ->
  simple_of_kind (Meet_env.typing_env menv) canonical_element1 kind ->
  simple_of_kind (Meet_env.typing_env menv) canonical_element2 kind ->
  Meet_env.add_alias_between_canonicals true menv kind canonical_element1
    canonical_element2 mh
  = Some (Or_bottom.Ok menv') ->
  meet_env_extends menv menv'
  ∧ typing_env_fits (Meet_env.typing_env menv').
Proof.
  intros Hfits Hc1 Hc2 Hkind1 Hkind2 Hadd.
  assert (Hinvariant := proj1 Hfits).
  set (tenv := Meet_env.typing_env menv) in *.
  unfold Meet_env.add_alias_between_canonicals in Hadd. fold tenv in Hadd.
  destruct (simple_equal canonical_element1 canonical_element2) eqn:Hsame.
  { injection Hadd as <-.
    split; [ apply meet_env_extends_refl | exact Hfits ]. }
  destruct (Typing_env.add_alias tenv canonical_element1 canonical_element2)
    as [ [ | result | ] | ] eqn:Halias; try discriminate Hadd.
  - injection Hadd as <-.
    split; [ apply meet_env_extends_refl | exact Hfits ].
  - cbv beta iota in Hadd.
    assert (Hdifferent : canonical_element1 <> canonical_element2).
    { intros Heq. apply simple_equal_eq in Heq. rewrite Heq in Hsame.
      discriminate Hsame. }
    assert (Hextends1 := add_alias_tenv_extends tenv _ _ result Halias).
    assert (Hfits1 :=
      add_alias_fits tenv _ _ result Halias kind Hfits Hc1
        Hc2
        (simple_of_kind_mem_simple tenv _ kind Hinvariant Hkind1)
        (simple_of_kind_mem_simple tenv _ kind Hinvariant Hkind2)
        Hkind1 Hkind2).
    destruct (add_alias_demoted tenv _ _ result Halias Hinvariant Hc1 Hc2
                Hdifferent) as [Hwhich Hnot].
    set (tenv1 := Typing_env.add_alias_result_t result) in *.
    assert (Hkept :
      ∀ s : simple, simple_of_kind tenv s kind -> simple_of_kind tenv1 s kind).
    { intros s.
      exact (proj1 (proj2 (proj2 (proj2 (proj2 Hextends1)))) s kind). }
    destruct (record_demotion_keeps (Meet_env.with_typing_env menv tenv1)
                menv' kind (Typing_env.demoted_name result)
                (Typing_env.canonical_element result) Hfits1 Hnot)
      as [Hextends2 Hfits2].
    + apply Hkept. destruct Hwhich as [ [_ ->] | [_ ->] ]; assumption.
    + apply Hkept. destruct Hwhich as [ [-> _] | [-> _] ]; assumption.
    + exact Hadd.
    + split; [ | exact Hfits2 ].
      exact (meet_env_extends_trans _ _ _
               (meet_env_extends_with menv tenv1 Hextends1) Hextends2).
Qed.

(* ------------------------------------------------------------------------ *)
(* A simple is given a type                                                 *)
(* ------------------------------------------------------------------------ *)

(* [add_equation_on_simple ~raise_on_bottom:true]. *)
Lemma add_equation_on_simple0_keeps (menv menv' : Meet_env.t) (s : simple)
    (ty : flambda_type) :
  typing_env_fits (Meet_env.typing_env menv) ->
  type_fits (Meet_env.typing_env menv) ty ->
  simple_of_kind (Meet_env.typing_env menv) s (kind ty) ->
  Meet_env.add_equation_on_simple0 true menv s ty mh
  = Some (Or_bottom.Ok menv') ->
  meet_env_extends menv menv'
  ∧ typing_env_fits (Meet_env.typing_env menv').
Proof.
  intros Hfits Hty Hkind Hadd.
  assert (Hinvariant := proj1 Hfits).
  assert (Hkinded := proj1 (proj2 (proj1 (proj2 (proj2 Hfits))))).
  set (tenv := Meet_env.typing_env menv) in *.
  unfold Meet_env.add_equation_on_simple0 in Hadd. fold tenv in Hadd.
  destruct (canonical_of_kind tenv s (kind ty) Hinvariant Hkinded Hkind)
    as [Hcanonical Hkind_canonical].
  destruct (get_alias_opt ty) as [ alias | ] eqn:Halias.
  - assert (Hkind_alias : simple_of_kind tenv alias (kind ty)).
    { exact (proj2 (proj2 Hty) alias (kind ty)
               (alias_among_aliases ty alias Halias)). }
    destruct (canonical_of_kind tenv alias (kind ty) Hinvariant Hkinded
                Hkind_alias) as [Hcanonical2 Hkind_canonical2].
    exact (add_alias_between_canonicals_keeps menv menv' (kind ty) _ _ Hfits
             Hcanonical Hcanonical2 Hkind_canonical Hkind_canonical2 Hadd).
  - destruct (Expanded_type.of_non_alias_type ty) as [ expanded | ]
      eqn:Hexpanded; [ | discriminate Hadd ].
    cbv beta iota in Hadd.
    unfold Meet_env.add_concrete_equation_on_simple in Hadd.
    fold tenv in Hadd.
    destruct (of_non_alias_type_kind _ _ Hexpanded) as [Hkind1 Hkind2].
    apply (add_or_delay_concrete_equation_on_canonical_keeps menv menv'
             (Typing_env.get_canonical_simple_ignoring_name_mode tenv s)
             expanded Hfits).
    + exact (type_fits_of_non_alias _ _ _ Hexpanded Hty).
    + rewrite Hkind1, Hkind2. reflexivity.
    + rewrite Hkind2. exact Hkind_canonical.
    + exact Hadd.
Qed.

(* The equations of a list, each on a name of the kind of its type. *)
Definition equations_fit (tenv : Typing_env.t)
    (equations : list (name * flambda_type)) : Prop :=
  ∀ (n : name) (ty : flambda_type),
    (n, ty) ∈ equations ->
    type_fits tenv ty
    ∧ simple_of_kind tenv (simple_of_name n) (kind ty).

Lemma add_equations0_keeps (equations : list (name * flambda_type)) :
  ∀ menv menv' : Meet_env.t,
    typing_env_fits (Meet_env.typing_env menv) ->
    equations_fit (Meet_env.typing_env menv) equations ->
    Meet_env.add_equations0 true menv equations mh
    = Some (Or_bottom.Ok menv') ->
    meet_env_extends menv menv'
    ∧ typing_env_fits (Meet_env.typing_env menv').
Proof.
  induction equations as [ | [n ty] equations IH ];
    intros menv menv' Hfits Hequations Hadd.
  - injection Hadd as <-.
    split; [ apply meet_env_extends_refl | exact Hfits ].
  - cbn [Meet_env.add_equations0] in Hadd.
    destruct (Meet_env.add_equation0 true menv n ty mh)
      as [ [ menv1 | ] | ] eqn:Hfirst; try discriminate Hadd.
    cbv beta iota in Hadd.
    destruct (Hequations n ty (or_introl eq_refl)) as [Hty Hkind].
    destruct (add_equation_on_simple0_keeps menv menv1 (simple_of_name n) ty
                Hfits Hty Hkind Hfirst) as [Hextends1 Hfits1].
    assert (Htenv := meet_env_extends_tenv _ _ Hextends1).
    destruct (IH menv1 menv' Hfits1) as [Hextends2 Hfits2].
    + intros n' ty' Hin.
      destruct (Hequations n' ty' (or_intror Hin)) as [Hty' Hkind'].
      split.
      * exact (tenv_extends_type_fits _ _ _ Htenv Hty').
      * exact (proj1 (proj2 (proj2 (proj2 (proj2 Htenv)))) _ _ Hkind').
    + exact Hadd.
    + split; [ | exact Hfits2 ].
      exact (meet_env_extends_trans _ _ _ Hextends1 Hextends2).
Qed.

End Keeps.
