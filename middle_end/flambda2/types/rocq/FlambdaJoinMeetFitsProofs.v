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


(* The proofs of the statements of FlambdaJoinMeetFitsSpec.v. This
   file needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaMapProofs FlambdaSemanticsSpec FlambdaClosuresSpec
  FlambdaNameAbstractionSpec FlambdaNameAbstractionProofs.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeWellFormedSpec
  FlambdaTypeMeaningSpec FlambdaTypeEqualSpec FlambdaTypeEqualProofs
  FlambdaBindingTime FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs
  FlambdaTypingEnvKindedSpec FlambdaTypingEnvKindedProofs FlambdaJoinEnv
  FlambdaJoinSpec FlambdaJoinEnvSpec FlambdaJoinEnvProofs
  FlambdaJoinStateSpec FlambdaJoinStateProofs FlambdaJoinDefineSpec
  FlambdaJoinDefineProofs FlambdaJoinFitsSpec FlambdaJoinFitsProofs
  FlambdaJoinAddsSpec FlambdaJoinAddsProofs FlambdaJoinKindsSpec
  FlambdaJoinKindsProofs FlambdaJoinNamesSpec FlambdaJoinNamesProofs
  FlambdaTypeAliasKindsSpec FlambdaTypeAliasKindsProofs FlambdaJoinTypes
  FlambdaJoinTypesSpec FlambdaJoinTypesWithEnvSpec
  FlambdaJoinTypesWithEnvProofs FlambdaMeetGrammar FlambdaExpandHead
  FlambdaExpandHeadSpec FlambdaExpandHeadProofs FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec FlambdaMeetStepsSpec FlambdaMeetStepsProofs
  FlambdaMeetEnvSpec FlambdaMeetEnvProofs FlambdaJoinMeet
  FlambdaJoinMeetSpec FlambdaJoinMeetProofs FlambdaJoinWellFormedSpec
  FlambdaJoinWellFormedProofs FlambdaJoinEquationNamesSpec
  FlambdaJoinEquationNamesProofs FlambdaJoinMeetFitsSpec.
Import ListNotations.

Theorem expand_head_for_join_equations_kinded
  : expand_head_for_join_equations_kinded_statement.
Proof.
  intros tenv ty expanded Hexpand Htypes Hty.
  unfold expand_head_for_join in Hexpand.
  destruct (FlambdaExpandHead.expand_head tenv ty) as [expanded0 | ] eqn:He;
    [ | discriminate ].
  injection Hexpand as <-.
  rewrite (proj1 (join_expanded_to_type expanded0)).
  exact (FlambdaExpandHeadProofs.expand_head_equations_kinded tenv ty
           expanded0 Htypes Hty He).
Qed.

Theorem last_phase_equation_names_known
  : last_phase_equation_names_known_statement.
Proof.
  intros tenv fuel source s relations menv kept equations relation_equations
    definitions Htrue Hrelations Hnonempty Hscoped Hstate Hinvariant Henvs
    Hsymbols HN Hsource Hfits Hadds menv' n ty Hin.
  destruct (last_phase_adds_kept tenv fuel s relations kept equations
              relation_equations definitions Hadds) as [Hdistinct Hkept].
  destruct (last_phase_adds_in_scope tenv fuel source s relations kept
              equations relation_equations definitions Htrue Hrelations
              Hnonempty (proj1 Hscoped)
              (scoped_aliases_not_made s (proj1 Htrue) (proj2 Hscoped)) Hadds)
    as [Hscope1 Hscope2].
  assert (Hsource' : Meet_env.typing_env menv = Join_env.source_env s).
  { rewrite (proj2 (proj2 Htrue)). exact Hsource. }
  destruct (target_variables_defined s menv kept (proj1 Htrue) Hsource' Hfits
              Hkept Hdistinct) as [Hkept' [_ [Hkinds _]]].
  fold menv' in Hkept', Hkinds.
  pose proof (scoped_equation_names s (proj1 Htrue) Hstate Hinvariant Henvs
                (proj1 Hscoped) HN) as Hnamed.
  pose proof (last_phase_adds_equation_names tenv fuel s relations kept
                equations relation_equations definitions Hnamed Hadds n ty
                Hin) as Hty.
  assert (Hfree :
            ∀ y : variable,
              y ∈ free_variables ty -> in_final_target s kept y).
  { apply in_app_or in Hin. destruct Hin as [Hin | Hin];
      [ exact (proj2 (Hscope1 _ _ Hin)) | exact (proj2 (Hscope2 _ _ Hin)) ]. }
  intros n0 k Hmember.
  pose proof (Hty n0 k Hmember) as HK.
  destruct n0 as [y | sym]; cbn [simple_of_name] in HK |- *.
  - apply (Hkinds y k); [ | exact HK ].
    apply Hfree.
    exact (proj1 equation_names_free_variables ty (Name_var y) k y Hmember
             (or_introl eq_refl)).
  - destruct HK as [-> [index [use [Huse Hmem]]]].
    assert (Hknown :
              Typing_env.mem None (Meet_env.typing_env menv')
                (Name_symbol sym)
              = true).
    { apply (tenv_extends_mem _ _ _
               (meet_env_extends_tenv _ _ (proj1 Hkept'))).
      rewrite Hsource. exact (Hsymbols index use sym Huse Hmem). }
    destruct (bound_has_kind _ _ Hknown) as [k' Hk'].
    cbn [simple_of_name] in Hk'.
    rewrite (symbol_kinded _ _ _ (proj1 (proj2 (proj2 (proj2 Hkept'))))
               Hk') in Hk'.
    exact Hk'.
Qed.

Theorem model_join_adds_types_that_fit_otherwise
  : model_join_adds_types_that_fit_otherwise_statement.
Proof.
  intros join_choices join_depth fuel initial_env scoped_envs envs s1 s2 s3
    relations2 relations3 tenv kept equations relation_equations definitions
    initial_tenv p jt avoid s0 Hfits Hscoped Hagree Hcut Haliases Hdelayed
    Hloop Hadds.
  (* The environments joined. *)
  assert (Hfound :
            ∀ (index : Index.t) (use : Typing_env.t),
              Joined_envs.get_nth_joined_env envs index = Some use ->
              use ∈ scoped_envs).
  { intros index use Huse. apply get_nth_lookup in Huse.
    destruct Huse as [equations0 Hlookup].
    destruct (cut_for_joins_found _ _ _ Hcut _ _ _ Hlookup) as [Hin _].
    apply number_in in Hin. exact (nth_error_In _ _ Hin). }
  assert (Hsource : ∀ x : variable, knows initial_tenv x -> x ∈ avoid).
  { intros x Hx. apply in_or_app. right. apply in_or_app. left.
    apply variables_of_env_knows. exact Hx. }
  assert (Huses :
            ∀ (index : Index.t) (use : Typing_env.t) (x : variable),
              Joined_envs.get_nth_joined_env envs index = Some use ->
              knows use x ->
              x ∈ avoid).
  { intros index use x Huse Hx. apply in_or_app. right. apply in_or_app.
    right. apply in_flat_map. exists use.
    split; [ exact (Hfound index use Huse)
           | apply variables_of_env_knows; exact Hx ]. }
  destruct (join_parameters_sound join_depth)
    as [Hfresh [Heqb [Hextension Hconst]]].
  fold p in Hfresh, Heqb, Hextension, Hconst.
  assert (Hreduce :
            FlambdaJoinTypesSpec.reduce_head_of_kind_naked_immediate_sound
              reduce_head_of_kind_naked_immediate).
  { intros tenv0 statics valuation v head Hsat Hhead.
    exact (FlambdaMeetStepsProofs.reduce_head_of_kind_naked_immediate_sound
             statics valuation tenv0 head v Hsat Hhead). }
  pose proof (n_way_join_of_types_true initial_tenv p (fuel_of_env fuel)
                expand_head_for_join reduce_head_of_kind_naked_immediate
                (fuel_of_types fuel) Hfresh Heqb Hextension
                expand_head_for_join_sound Hreduce) as Hjt.
  assert (Hinvariant :
            ∀ (index : Index.t) (use : Typing_env.t),
              Joined_envs.get_nth_joined_env envs index = Some use ->
              typing_env_invariant use).
  { intros index use Huse.
    exact (proj1 (proj1 (Hscoped use (Hfound index use Huse)))). }
  assert (Hwf_envs :
            ∀ (index : Index.t) (use : Typing_env.t),
              Joined_envs.get_nth_joined_env envs index = Some use ->
              types_well_formed use).
  { intros index use Huse.
    exact (proj1 (proj2 (proj1 (Hscoped use (Hfound index use Huse))))). }
  assert (Hkinded_envs :
            ∀ (index : Index.t) (use : Typing_env.t),
              Joined_envs.get_nth_joined_env envs index = Some use ->
              typing_env_kinded use).
  { intros index use Huse.
    exact (proj1 (proj2 (proj2 (proj1 (Hscoped use
                                         (Hfound index use Huse)))))). }
  assert (Hnames_envs :
            ∀ (index : Index.t) (use : Typing_env.t),
              Joined_envs.get_nth_joined_env envs index = Some use ->
              types_equations_kinded use).
  { intros index use Huse.
    exact (proj1 (proj2 (proj2 (proj2 (proj1 (Hscoped use
                                                (Hfound index use
                                                   Huse))))))). }
  assert (Hlevels : levels_found envs).
  { intros index use equations0 n ty Hlookup Hn.
    destruct (cut_for_joins_found _ _ _ Hcut _ _ _ Hlookup)
      as [Hin [_ [level [Hlevel ->]]]].
    apply number_in in Hin. apply nth_error_In in Hin.
    exact (cut_equations_found use (Typing_env.current_scope initial_tenv)
             level n ty (proj2 (proj1 (proj1 (Hscoped use Hin)))) Hlevel
             Hn). }
  assert (Hkinds :
            ∀ (index : Index.t) (use : Typing_env.t) (x : variable)
              (kind : flambda_kind) (ty : flambda_type)
              (binding_time_and_mode : Binding_time.With_name_mode.t),
              Joined_envs.get_nth_joined_env envs index = Some use ->
              simple_of_kind use (Var x) kind ->
              Keyed.lookup name_eqb (Name_var x)
                (Typing_env.names_to_types initial_tenv)
              = Some (ty, binding_time_and_mode) ->
              FlambdaTypeGrammar.kind ty = kind).
  { intros index use x kind ty btm Huse Hk Hx.
    assert (Hknown : Typing_env.mem_simple None initial_tenv (Var x) = true).
    { apply (proj2 (mem_var_lookup initial_tenv x)). exists ty, btm.
      exact Hx. }
    pose proof (scoped_env_of_kind initial_tenv use (Var x) kind
                  (Hscoped use (Hfound index use Huse)) Hknown Hk) as Hk0.
    apply (simple_of_kind_unique initial_tenv (Var x)); [ | exact Hk0 ].
    change (Var x) with (simple_of_name (Name_var x)).
    apply simple_of_kind_name_iff. left. exists ty, btm.
    split; [ exact Hx | reflexivity ]. }
  (* The first phases. *)
  destruct (first_phases_true initial_tenv jt join_choices p (fuel_of_env fuel)
              avoid envs s1 s2 s3 relations2 relations3 Hjt Hfresh Heqb Hconst
              Hsource Huses Hinvariant Hkinded_envs Hlevels Hkinds Haliases
              Hdelayed Hloop) as [Htrue3 [Hrelations3 Hgrows3]].
  pose proof (first_phases_kinded initial_tenv jt join_choices p
                (fuel_of_env fuel) avoid envs s1 s2 s3 relations2 relations3
                Hjt Hfresh Heqb Hconst Hsource Huses Hinvariant Hkinded_envs
                Hlevels Hkinds Haliases Hdelayed Hloop) as Hstate3.
  assert (Hnonempty1 : relations_nonempty []).
  { intros r names' Hr. discriminate Hr. }
  pose proof (loop_relations_nonempty _ _ _ _ _ _ _ _ _ _
                (delayed_equations_relations_nonempty _ _ _ _ _ _ _ _
                   Hnonempty1 Hdelayed)
                Hloop) as Hnonempty3.
  pose proof (first_phases_scoped initial_tenv jt join_choices p
                (fuel_of_env fuel) avoid envs s1 s2 s3 relations2 relations3
                Hjt
                (n_way_join_keeps_scoped p (fuel_of_env fuel)
                   (fuel_of_types fuel) expand_head_for_join
                   reduce_head_of_kind_naked_immediate type_eqb
                   block_shape_eqb)
                Hfresh Heqb Hconst Hsource Huses Hinvariant Hkinded_envs
                Hlevels Hkinds Haliases Hdelayed Hloop) as Hscoped3.
  pose proof (first_phases_well_formed initial_tenv jt join_choices p
                (fuel_of_env fuel) avoid envs s1 s2 s3 relations2 relations3
                Hjt
                (n_way_join_of_types_well_formed p (fuel_of_env fuel)
                   expand_head_for_join reduce_head_of_kind_naked_immediate
                   (fuel_of_types fuel) Hfresh Hextension
                   expand_head_for_join_sound expand_head_for_join_well_formed
                   Hreduce)
                (n_way_join_of_types_keeps_well_formed p (fuel_of_env fuel)
                   expand_head_for_join reduce_head_of_kind_naked_immediate
                   (fuel_of_types fuel))
                Hfresh Heqb Hconst (join_parameters_well_formed join_depth)
                Hsource Huses Hinvariant Hkinded_envs Hwf_envs Hlevels Hkinds
                Haliases Hdelayed Hloop) as HW.
  pose proof (first_phases_equation_names initial_tenv jt join_choices p
                (fuel_of_env fuel) avoid envs s1 s2 s3 relations2 relations3
                Hjt
                (n_way_join_of_types_equations_kinded p (fuel_of_env fuel)
                   expand_head_for_join reduce_head_of_kind_naked_immediate
                   (fuel_of_types fuel) Hfresh Hextension
                   expand_head_for_join_sound
                   expand_head_for_join_equations_kinded Hreduce)
                (n_way_join_of_types_keeps_equation_names p (fuel_of_env fuel)
                   expand_head_for_join reduce_head_of_kind_naked_immediate
                   (fuel_of_types fuel) Hfresh)
                Hfresh Heqb Hconst (join_parameters_no_equations join_depth)
                Hsource Huses Hinvariant Hkinded_envs Hnames_envs Hlevels
                Hkinds Haliases Hdelayed Hloop) as HN.
  assert (Hinvariant3 : joined_envs_are typing_env_invariant s3).
  { intros index use Huse. rewrite (proj1 Hgrows3) in Huse.
    exact (Hinvariant index use Huse). }
  assert (Hkinded3 : joined_envs_are typing_env_kinded s3).
  { intros index use Huse. rewrite (proj1 Hgrows3) in Huse.
    exact (Hkinded_envs index use Huse). }
  assert (Hsymbols3 : symbols_of_joined_envs_in_source initial_tenv s3).
  { intros index use sym Huse Hmem. rewrite (proj1 Hgrows3) in Huse.
    exact (proj2 (proj2 (proj2 (Hscoped use (Hfound index use Huse)))) sym
             Hmem). }
  (* The last phase. *)
  intros n ty Hin. split.
  - exact (last_phase_adds_well_formed tenv (fuel_of_env fuel) s3 relations3
             kept equations relation_equations definitions (proj1 HW) Hadds n
             ty Hin).
  - exact (last_phase_equation_names_known tenv (fuel_of_env fuel)
             initial_tenv s3 relations3
             (Meet_env.with_names_to_avoid initial_env
                (Bindings_in_target_env.names_to_avoid (Join_env.bindings s3)))
             kept equations relation_equations definitions Htrue3 Hrelations3
             Hnonempty3 Hscoped3 Hstate3 Hinvariant3 Hkinded3 Hsymbols3 HN
             eq_refl Hfits Hadds n ty Hin).
Qed.

Theorem model_join_scoped_envs_keeps_outright
  : model_join_scoped_envs_keeps_outright_statement.
Proof.
  intros join_choices join_depth fuel.
  exact (model_join_scoped_envs_keeps join_choices join_depth fuel
           (model_join_adds_types_that_fit_otherwise join_choices join_depth
              fuel)).
Qed.

Theorem model_join_scoped_envs_satisfied_outright
  : model_join_scoped_envs_satisfied_outright_statement.
Proof.
  intros join_choices join_depth fuel.
  exact (model_join_scoped_envs_satisfied join_choices join_depth fuel
           (model_join_adds_types_that_fit_otherwise join_choices join_depth
              fuel)).
Qed.
