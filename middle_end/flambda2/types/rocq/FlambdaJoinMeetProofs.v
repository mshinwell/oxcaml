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


(* The proofs of the statements of FlambdaJoinMeetSpec.v. This file
   needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaMapProofs FlambdaSemanticsSpec
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
  FlambdaJoinKindsProofs FlambdaTypeAliasKindsSpec
  FlambdaTypeAliasKindsProofs FlambdaJoinTypes
  FlambdaJoinTypesSpec FlambdaJoinTypesWithEnvSpec
  FlambdaJoinTypesWithEnvProofs FlambdaMeetGrammar FlambdaExpandHead
  FlambdaExpandHeadSpec FlambdaExpandHeadProofs FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec FlambdaMeetStepsSpec FlambdaMeetStepsProofs
  FlambdaMeetEnvSpec FlambdaMeetEnvProofs FlambdaJoinMeet
  FlambdaJoinMeetSpec.
Import ListNotations.

Theorem join_expanded_to_type : join_expanded_to_type_statement.
Proof.
  intros [k [ | [head | head | k' head | head | head] | ]];
    split; reflexivity.
Qed.

Theorem join_parameters_sound : join_parameters_sound_statement.
Proof.
  intros join_depth. split; [ | split; [ | split ] ].
  - intros names Hin. cbn [Join_env.fresh join_parameters] in Hin.
    pose proof (fresh_name_fresh names) as Hfresh.
    apply (proj2 (among_In _ _)) in Hin. congruence.
  - intros t t' statics valuation v Heqb Hsat.
    exact (proj2 (type_equal_satisfied statics valuation v t t' Heqb) Hsat).
  - intros extension extension' statics valuation Heqb Hsat.
    exact (proj1 (env_extension_equal_satisfied statics valuation extension
                    extension' Heqb) Hsat).
  - intros c. cbn [Join_env.expand_const join_parameters].
    split; [ exact (create_const_free_variables c) | ].
    split; [ intros tenv; exact (create_const_kinded tenv c) | ].
    intros statics valuation. exact (create_const_sound statics valuation c).
Qed.

Theorem expand_head_for_join_sound : expand_head_for_join_sound_statement.
Proof.
  intros tenv ty expanded Hexpand. unfold expand_head_for_join in Hexpand.
  destruct (FlambdaExpandHead.expand_head tenv ty) as [expanded0 | ] eqn:H0;
    [ | discriminate ].
  injection Hexpand as <-.
  destruct (join_expanded_to_type expanded0) as [Htype Hkind].
  rewrite Htype, Hkind.
  split; [ | split; [ | split ] ].
  - intros statics valuation v Hsat Hty.
    exact (FlambdaExpandHeadProofs.expand_head_sound statics valuation tenv
             ty expanded0 v Hsat Hty H0).
  - intros Hinvariant Hscope x Hx.
    exact (expand_head_closed tenv ty expanded0
             (invariant_types_closed tenv Hinvariant) Hscope H0 x Hx).
  - intros Hkinded Hty.
    exact (expand_head_kinded tenv ty expanded0 (proj1 Hkinded) Hty H0).
  - intros Hconstants Hty.
    exact (expand_head_kind tenv ty expanded0 Hconstants Hty H0).
Qed.

Theorem model_join_true : model_join_true_statement.
Proof.
  intros A join_choices meet_choices join_depth fuel avoid inputs target
    analysis Hinputs Hkinded Hagree Hsome Hjoin.
  destruct (join_parameters_sound join_depth)
    as [Hfresh [Heqb [Hextension Hconst]]].
  assert (Hreduce :
            FlambdaJoinTypesSpec.reduce_head_of_kind_naked_immediate_sound
              reduce_head_of_kind_naked_immediate).
  { intros tenv statics valuation v head Hsat Hhead.
    exact (FlambdaMeetStepsProofs.reduce_head_of_kind_naked_immediate_sound
             statics valuation tenv head v Hsat Hhead). }
  exact (join_with_true A Meet_env.t meet_expanded_head meet_env_functions
           (join_parameters join_depth) (fuel_of_env fuel) join_choices
           (model_join_of_types join_depth fuel)
           (model_meet_expanded_head join_choices meet_choices join_depth
              fuel)
           avoid inputs target analysis
           (n_way_join_of_types_true (source inputs)
              (join_parameters join_depth) (fuel_of_env fuel)
              expand_head_for_join reduce_head_of_kind_naked_immediate
              (fuel_of_types fuel) Hfresh Heqb Hextension
              expand_head_for_join_sound Hreduce)
           (n_way_join_keeps_envs (join_parameters join_depth)
              (fuel_of_env fuel) (fuel_of_types fuel) expand_head_for_join
              reduce_head_of_kind_naked_immediate type_eqb block_shape_eqb)
           Hfresh Heqb Hconst Hinputs Hkinded Hagree Hsome Hjoin).
Qed.

(* ---------------------------------------------------------------------- *)
(* The variables that the join defines, in the environment of the meet     *)
(* ---------------------------------------------------------------------- *)

Theorem variables_defined_kept : variables_defined_kept_statement.
Proof.
  intros vars.
  induction vars as [ | [x k] vars IH]; intros menv Hfits Hdistinct Hfresh.
  - cbn. split; [ split; [ apply meet_env_extends_refl | exact Hfits ] | ].
    split; [ intros x kind [] | ].
    split; [ | reflexivity ].
    intros x. split; [ intros H; left; exact H | intros [H | []]; exact H ].
  - change (variables_defined meet_env_functions menv ((x, k) :: vars))
      with (variables_defined meet_env_functions
              (Meet_env.add_variable_definition menv x k Name_mode.in_types)
              vars).
    set (menv1 := Meet_env.add_variable_definition menv x k Name_mode.in_types).
    assert (Hx : Typing_env.mem None (Meet_env.typing_env menv) (Name_var x)
                 = false).
    { apply Hfresh. left. reflexivity. }
    destruct (add_variable_definition_keeps menv x k Name_mode.in_types Hfits
                Hx) as [Hextends1 Hfits1].
    fold menv1 in Hextends1, Hfits1.
    cbn [map fst] in Hdistinct. apply NoDup_cons_iff in Hdistinct.
    destruct Hdistinct as [Hnotin Hdistinct].
    assert (Hother :
              ∀ y : variable,
                y <> x ->
                Typing_env.mem None (Meet_env.typing_env menv1) (Name_var y)
                = Typing_env.mem None (Meet_env.typing_env menv) (Name_var y)).
    { intros y Hne.
      exact (mem_add_variable_definition (Meet_env.typing_env menv) x k
               Name_mode.in_types y Hne). }
    assert (Hkind1 : simple_of_kind (Meet_env.typing_env menv1) (Var x) k).
    { apply (proj2 (add_variable_definition_simple_of_kind
                      (Meet_env.typing_env menv) x k Name_mode.in_types
                      (Var x) k)).
      left. split; reflexivity. }
    assert (Hmem1 : Typing_env.mem None (Meet_env.typing_env menv1)
                      (Name_var x)
                    = true).
    { exact (simple_of_kind_mem (Meet_env.typing_env menv1) (Name_var x) k
               (proj1 Hfits1) Hkind1). }
    assert (Hfresh1 :
              ∀ y : variable,
                y ∈ map fst vars ->
                Typing_env.mem None (Meet_env.typing_env menv1) (Name_var y)
                = false).
    { intros y Hy. rewrite Hother.
      - apply Hfresh. right. exact Hy.
      - intros ->. exact (Hnotin Hy). }
    destruct (IH menv1 Hfits1 Hdistinct Hfresh1)
      as [[Hextends Hfits'] [Hkinds [Hmem Hnames]]].
    split.
    { split; [ exact (meet_env_extends_trans _ _ _ Hextends1 Hextends)
             | exact Hfits' ]. }
    split.
    { intros y kind [Heq | Hin].
      - injection Heq as <- <-.
        destruct Hextends as (_ & _ & _ & _ & Hkind & _).
        exact (Hkind _ _ Hkind1).
      - exact (Hkinds y kind Hin). }
    split; [ | rewrite Hnames; reflexivity ].
    intros y. rewrite Hmem. cbn [map fst].
    destruct (Pos.eq_dec y x) as [-> | Hne].
    + split; [ intros _; right; left; reflexivity | ].
      intros _. left. exact Hmem1.
    + rewrite (Hother y Hne). split.
      * intros [H | H]; [ left; exact H | right; right; exact H ].
      * intros [H | [Heq | H]];
          [ left; exact H | congruence | right; exact H ].
Qed.

Lemma in_order_keys {A : Type} (m : finite_map A) (x : variable) :
  x ∈ map fst (rev (compact m)) <-> is_bound x m = true.
Proof.
  rewrite map_rev, <- in_rev. split.
  - intros Hx. apply in_map_iff in Hx. destruct Hx as [[y a] [Heq Hin]].
    cbn in Heq. subst y. apply is_bound_lookup. exists a.
    apply in_compact. exact Hin.
  - intros Hx. apply is_bound_lookup in Hx. destruct Hx as [a Ha].
    apply in_map_iff. exists (x, a).
    split; [ reflexivity | apply in_compact; exact Ha ].
Qed.

Theorem target_variables_defined : target_variables_defined_statement.
Proof.
  intros s menv kept Hvalid Hsource Hfits Hkept Hdistinct menv'.
  destruct Hvalid as [_ [Hnew [_ [_ Himports]]]].
  set (imported :=
         Bindings_in_target_env.imported_variables_in_order
           (Join_env.bindings s)) in *.
  assert (Himported_keys :
            ∀ x : variable, x ∈ map fst imported <-> is_imported s x).
  { intros x. exact (in_order_keys _ x). }
  assert (Hkept_existential :
            ∀ x : variable, x ∈ map fst kept -> is_existential s x).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as [[y k] [Heq Hin]].
    cbn in Heq. subst y. apply is_bound_lookup. exists k.
    exact (in_order_lookup _ _ _ (Hkept _ Hin)). }
  assert (Hapart :
            ∀ x : variable, is_imported s x -> is_existential s x -> False).
  { intros x Hi He. destruct (Hnew x He) as [_ Huses].
    destruct (Himports x Hi) as [_ [index [use [Huse Hknows]]]].
    exact (Huses index use Huse Hknows). }
  assert (Hnodup : NoDup (map fst (imported ++ kept))).
  { rewrite map_app. apply NoDup_app.
    - apply in_order_distinct.
    - exact Hdistinct.
    - intros x Hi Hk.
      exact (Hapart x (proj1 (Himported_keys x) Hi)
               (Hkept_existential x Hk)). }
  assert (Hfresh :
            ∀ x : variable,
              x ∈ map fst (imported ++ kept) ->
              Typing_env.mem None (Meet_env.typing_env menv) (Name_var x)
              = false).
  { intros x Hx. rewrite Hsource. rewrite map_app in Hx.
    apply in_app_or in Hx.
    destruct (Typing_env.mem None (Join_env.source_env s) (Name_var x))
      eqn:Hmem; [ exfalso | reflexivity ].
    destruct Hx as [Hx | Hx].
    - exact (proj1 (Himports x (proj1 (Himported_keys x) Hx)) Hmem).
    - exact (proj1 (Hnew x (Hkept_existential x Hx)) Hmem). }
  destruct (variables_defined_kept (imported ++ kept) menv Hfits Hnodup
              Hfresh) as [Hkept' [Hkinds [Hmem Hnames]]].
  fold menv' in Hkept', Hkinds, Hmem, Hnames.
  split; [ exact Hkept' | ]. split.
  { intros x. rewrite Hmem, Hsource, map_app.
    unfold in_final_target, knows. split.
    - intros [H | [H | H]];
        [ left; exact H
        | right; apply in_or_app; left; exact (proj2 (Himported_keys x) H)
        | right; apply in_or_app; right; exact H ].
    - intros [H | H]; [ left; exact H | ]. apply in_app_or in H.
      destruct H as [H | H];
        [ right; left; exact (proj1 (Himported_keys x) H)
        | right; right; exact H ]. }
  split; [ | exact Hnames ].
  intros x kind Hin Hkind. unfold kind_in_target_env in Hkind.
  destruct (Keyed.lookup name_eqb (Name_var x)
              (Typing_env.names_to_types
                 (Bindings_in_target_env.source_env (Join_env.bindings s))))
    as [[ty btm] | ] eqn:Hlookup.
  - injection Hkind as <-.
    destruct Hkept' as [Hextends _].
    destruct Hextends as (_ & _ & _ & _ & Hkind_kept & _).
    apply Hkind_kept. rewrite Hsource.
    change (Var x) with (simple_of_name (Name_var x)).
    apply simple_of_kind_name_iff. left. exists ty, btm.
    split; [ exact Hlookup | reflexivity ].
  - assert (Hunknown : ~ knows (Join_env.source_env s) x).
    { intros Hknows. apply mem_var_lookup in Hknows.
      destruct Hknows as [ty [btm H]]. unfold Join_env.source_env in H.
      rewrite Hlookup in H. discriminate. }
    destruct (lookup x
                (Bindings_in_target_env.existential_variables
                   (Join_env.bindings s))) as [k | ] eqn:Hexistential.
    + injection Hkind as <-.
      assert (Hex : is_existential s x).
      { apply is_bound_lookup. exists k. exact Hexistential. }
      destruct Hin as [H | [H | H]];
        [ exfalso; exact (Hunknown H) | exfalso; exact (Hapart x H Hex) | ].
      apply in_map_iff in H. destruct H as [[y k'] [Heq Hin']].
      cbn in Heq. subst y.
      pose proof (in_order_lookup _ _ _ (Hkept _ Hin')) as Hk'.
      rewrite Hexistential in Hk'. injection Hk' as <-.
      apply Hkinds. apply in_or_app. right. exact Hin'.
    + apply Hkinds. apply in_or_app. left.
      unfold imported, Bindings_in_target_env.imported_variables_in_order.
      apply in_rev. rewrite rev_involutive. apply in_compact. exact Hkind.
Qed.

Theorem last_phase_names_known : last_phase_names_known_statement.
Proof.
  intros tenv fuel source s relations menv kept equations relation_equations
    definitions Htrue Hrelations Hnonempty Hscoped Hsource Hfits Hadds menv'.
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
              Hkept Hdistinct) as [Hkept' [Hmem _]].
  split; [ exact Hkept' | ].
  intros n ty Hin.
  destruct (last_phase_adds_on_variables tenv fuel s relations kept equations
              relation_equations definitions Hadds n ty Hin) as [x ->].
  assert (Hboth :
            (∀ y : variable,
               y ∈ free_variables_of_name (Name_var x) ->
               in_final_target s kept y)
            ∧ ∀ y : variable,
                y ∈ free_variables ty -> in_final_target s kept y).
  { apply in_app_or in Hin. destruct Hin as [Hin | Hin];
      [ exact (Hscope1 _ _ Hin) | exact (Hscope2 _ _ Hin) ]. }
  split.
  - apply Hmem. apply (proj1 Hboth). left. reflexivity.
  - intros y Hy. apply Hmem. exact (proj2 Hboth y Hy).
Qed.

Theorem last_phase_kinds_known : last_phase_kinds_known_statement.
Proof.
  intros tenv fuel source s relations menv kept equations relation_equations
    definitions Htrue Hrelations Hnonempty Hscoped Hstate Henvs HX HR Hsource
    Hfits Hadds menv' n ty Hin.
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
  destruct HX as [H1 [H4 [_ [H5 _]]]].
  pose proof (scoped_equations_kinded s (proj1 Htrue) Hstate Henvs
                (proj1 Hscoped) H1) as Hkinded.
  destruct (last_phase_adds_kinded tenv fuel s relations kept equations
              relation_equations definitions (proj1 Htrue) Hkinded H4 H5 HR
              Hadds n ty Hin) as [Haliases [x [-> Hx]]].
  assert (Hboth :
            (∀ y : variable,
               y ∈ free_variables_of_name (Name_var x) ->
               in_final_target s kept y)
            ∧ ∀ y : variable,
                y ∈ free_variables ty -> in_final_target s kept y).
  { apply in_app_or in Hin. destruct Hin as [Hin | Hin];
      [ exact (Hscope1 _ _ Hin) | exact (Hscope2 _ _ Hin) ]. }
  split.
  - exact (Hkinds x (kind ty) (proj1 Hboth x (or_introl eq_refl)) Hx).
  - intros simple k Hmember Hsymbol.
    pose proof (Haliases simple k Hmember) as HK.
    destruct simple as [y | sym | c].
    + apply (Hkinds y k); [ | exact HK ].
      apply (proj2 Hboth).
      exact (proj1 aliases_free_variables ty (Var y) k y Hmember
               (or_introl eq_refl)).
    + cbn in HK. subst k.
      destruct (bound_has_kind _ _ (Hsymbol sym eq_refl)) as [k' Hk'].
      cbn [simple_of_name] in Hk'.
      rewrite (symbol_kinded _ _ _ (proj1 (proj2 (proj2 (proj2 Hkept'))))
                 Hk') in Hk'.
      exact Hk'.
    + exact HK.
Qed.

(* An equation that is found is one of the list. *)
Lemma lookup_among (n : name) (ty : flambda_type)
    (equations : list (name * flambda_type)) :
  Keyed.lookup name_eqb n equations = Some ty -> (n, ty) ∈ equations.
Proof. exact (keyed_lookup_in name_eqb name_eqb_eq n ty equations). Qed.

Theorem last_phase_kept : last_phase_kept_statement.
Proof.
  intros tenv fuel source s relations mh menv menv1 target kept equations
    relation_equations definitions Htrue Hrelations Hnonempty Hscoped Hstate
    Henvs HX HR Hsource Hfits Hadds menv0 Hrest Hmh Hadd1 Hadd2.
  destruct (last_phase_names_known tenv fuel source s relations menv kept
              equations relation_equations definitions Htrue Hrelations
              Hnonempty Hscoped Hsource Hfits Hadds) as [Hkept0 Hnames].
  fold menv0 in Hkept0, Hnames.
  pose proof (last_phase_kinds_known tenv fuel source s relations menv kept
                equations relation_equations definitions Htrue Hrelations
                Hnonempty Hscoped Hstate Henvs HX HR Hsource Hfits Hadds)
    as Hkinds.
  cbv zeta in Hkinds. fold menv0 in Hkinds.
  assert (Hall :
            ∀ (n : name) (ty : flambda_type),
              (n, ty) ∈ equations ++ relation_equations ->
              Typing_env.mem None (Meet_env.typing_env menv0) n = true
              ∧ type_fits (Meet_env.typing_env menv0) ty
              ∧ simple_of_kind (Meet_env.typing_env menv0) (simple_of_name n)
                  (kind ty)).
  { intros n ty Hin.
    destruct (Hnames n ty Hin) as [Hn Hvars].
    destruct (Hkinds n ty Hin) as [Hkind Haliases].
    destruct (Hrest n ty Hin) as [Hwf [Heqs Hsyms]].
    split; [ exact Hn | ]. split; [ | exact Hkind ].
    split; [ exact Hwf | ]. split; [ exact Hvars | ].
    split; [ | exact Heqs ].
    intros simple k Hmember. apply (Haliases simple k Hmember).
    intros sym ->. exact (Hsyms sym k Hmember). }
  split; [ exact Hkept0 | ].
  assert (Hstep1 : meet_env_kept_by_meet menv0 menv1).
  { apply (add_env_extension_keeps mh menv0 menv1 (Env_extension equations)
             Hmh (proj2 Hkept0)); [ | | exact Hadd1 ].
    - intros n ty Hlookup.
      destruct (Hall n ty
                  (in_or_app _ _ _ (or_introl (lookup_among _ _ _ Hlookup))))
        as [Hn [Hty _]].
      split; assumption.
    - intros n ty Hlookup.
      exact (proj2 (proj2 (Hall n ty
                             (in_or_app _ _ _
                                (or_introl (lookup_among _ _ _ Hlookup)))))). }
  split; [ exact Hstep1 | ].
  pose proof (meet_env_extends_tenv _ _ (proj1 (proj1 Hstep1))) as Hextends.
  apply (add_env_extension_keeps mh menv1 target
           (Env_extension relation_equations) Hmh (proj2 (proj1 Hstep1)));
    [ | | exact Hadd2 ].
  - intros n ty Hlookup.
    destruct (Hall n ty
                (in_or_app _ _ _ (or_intror (lookup_among _ _ _ Hlookup))))
      as [Hn [Hty _]].
    split.
    + exact (tenv_extends_mem _ _ _ Hextends Hn).
    + exact (tenv_extends_type_fits _ _ _ Hextends Hty).
  - intros n ty Hlookup.
    apply (proj1 (proj2 (proj2 (proj2 (proj2 Hextends))))).
    exact (proj2 (proj2 (Hall n ty
                           (in_or_app _ _ _
                              (or_intror (lookup_among _ _ _ Hlookup)))))).
Qed.
