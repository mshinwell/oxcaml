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


(* Proofs of the statements of FlambdaTypingEnvRefinementSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaWellFormedSpec FlambdaWellFormedProofs FlambdaContextSpec
  FlambdaContextProofs.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaEnvAliasesSpec
  FlambdaEnvAliasesProofs FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvProofs FlambdaTypingEnvInvariantSpec
  FlambdaTypingEnvInvariantProofs FlambdaTypingEnvOperationsSpec
  FlambdaTypingEnvOperationsProofs FlambdaTypingEnvRefinementSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* Refinement relative to a typing environment                              *)
(* ======================================================================== *)

Theorem expr_refines_under_weaken : expr_refines_under_weaken_statement.
Proof.
  intros tenv source target Hrefines vars conts statics _. apply Hrefines.
Qed.

Theorem expr_equivalent_under_refines
    : expr_equivalent_under_refines_statement.
Proof.
  intros tenv e e' Hequivalent vars conts statics Hsat.
  apply equivalent_refines, Hequivalent, Hsat.
Qed.

Theorem expr_refines_under_trans : expr_refines_under_trans_statement.
Proof.
  intros tenv e e' e'' Hfirst Hsecond vars conts statics Hsat.
  exact (refines_trans _ _ _ (Hfirst vars conts statics Hsat)
           (Hsecond vars conts statics Hsat)).
Qed.

Theorem bottom_refines_under : bottom_refines_under_statement.
Proof.
  intros tenv e e' Hbottom vars conts statics Hsat. exfalso.
  apply (bottom_not_satisfied tenv statics vars Hbottom).
  apply env_satisfies_strictly_env_satisfies. exact Hsat.
Qed.

(* ======================================================================== *)
(* Canonical elements                                                       *)
(* ======================================================================== *)

Lemma canonical_in_terms_sound (tenv : Typing_env.t) (statics : static_env)
    (vars : env) (s canonical : simple) :
  env_satisfies_strictly tenv statics vars ->
  canonical_in_terms tenv s canonical ->
  eval_simple vars canonical = eval_simple vars s.
Proof.
  intros Hsat [Hmem [ty Hcanonical]].
  apply (type_simple_in_term_canonical tenv statics vars s canonical ty);
    [ | exact Hmem | exact Hcanonical ].
  apply env_satisfies_strictly_env_satisfies. exact Hsat.
Qed.

Lemma canonical_in_terms_simples (tenv : Typing_env.t) (statics : static_env)
    (vars : env) (args args' : list simple) :
  env_satisfies_strictly tenv statics vars ->
  Forall2 (canonical_in_terms tenv) args args' ->
  eval_simples vars args' = eval_simples vars args.
Proof.
  intros Hsat Hargs.
  induction Hargs as [ | s s' args args' Hs Hargs IH]; [ reflexivity | ].
  simpl. rewrite (canonical_in_terms_sound tenv statics vars s s' Hsat Hs), IH.
  reflexivity.
Qed.

Theorem apply_cont_canonical : apply_cont_canonical_statement.
Proof.
  intros tenv k args args' Hargs vars conts statics Hsat.
  apply step_eq_equivalent. rewrite !step_apply_cont. simpl.
  rewrite (canonical_in_terms_simples tenv statics vars args args' Hsat
             Hargs).
  reflexivity.
Qed.

Theorem let_simple_canonical : let_simple_canonical_statement.
Proof.
  intros tenv x kind s canonical body Hcanonical vars conts statics Hsat.
  apply let_equivalent_step; [ | intros v _; apply equivalent_refl ].
  exact (canonical_in_terms_sound tenv statics vars s canonical Hsat
           Hcanonical).
Qed.

Theorem switch_known : switch_known_statement.
Proof.
  intros tenv scrutinee i arms ac Hknown Hfind vars conts statics Hsat.
  apply step_equivalent. rewrite step_switch.
  rewrite <- (canonical_in_terms_sound tenv statics vars scrutinee _ Hsat
                Hknown).
  simpl. rewrite Hfind. reflexivity.
Qed.

(* ======================================================================== *)
(* The environment follows the term                                         *)
(* ======================================================================== *)

(* The variables in scope once a variable is defined at the normal name
   mode. *)
Lemma add_variable_definition_in_scope (tenv : Typing_env.t) (x : variable)
    (kind : flambda_kind) (y : variable) :
  typing_env_well_formed tenv = true ->
  (in_scope_in_terms
     (Typing_env.add_variable_definition tenv x kind Name_mode.normal) y
   <-> y = x ∨ (y <> x ∧ in_scope_in_terms tenv y)).
Proof.
  intros Hwf.
  pose proof (proj1 (typing_env_well_formed_iff tenv) Hwf) as Hconditions.
  destruct Hconditions as [[[_ Hmin] _] _].
  rewrite !in_scope_in_terms_lookup, add_variable_definition_lookup.
  change (Typing_env.min_binding_time
            (Typing_env.add_variable_definition tenv x kind Name_mode.normal))
    with (Typing_env.min_binding_time tenv).
  destruct (keyed_eqb_spec name_eqb name_eqb_eq (Name_var y) (Name_var x))
    as [Heq | Hne].
  - injection Heq as ->. split; [ intros _; left; reflexivity | ].
    intros _. eexists. eexists. split; [ reflexivity | ].
    unfold Binding_time.With_name_mode.scoped_name_mode. simpl.
    destruct (Typing_env.min_binding_time tenv
              <=? Typing_env.next_binding_time tenv) eqn:Hle;
      [ rewrite orb_true_r; reflexivity | ].
    apply Z.leb_gt in Hle. lia.
  - split.
    + intros Hscope. right. split; [ congruence | exact Hscope ].
    + intros [-> | [_ Hscope]]; [ congruence | exact Hscope ].
Qed.

Theorem add_variable_definition_env_satisfies_strictly
    : add_variable_definition_env_satisfies_strictly_statement.
Proof.
  intros tenv statics vars x kind v Hwf Hfresh Hkind
    [Hbound [valuation [Hsatisfied Hagrees]]].
  split.
  - intros y Hy.
    apply (add_variable_definition_in_scope tenv x kind y Hwf) in Hy.
    destruct Hy as [-> | [Hne Hy]].
    + exists v. apply lookup_head.
    + destruct (Hbound y Hy) as [w Hw]. exists w.
      exact (eq_trans (lookup_other y x v vars Hne) Hw).
  - exists ((x, v) :: valuation). split.
    + apply add_variable_definition_satisfied_bind;
        [ exact Hsatisfied | | exact Hkind ].
      exact (well_formed_not_mentioned tenv x Hwf Hfresh).
    + intros y Hy.
      apply (add_variable_definition_in_scope tenv x kind y Hwf) in Hy.
      destruct Hy as [-> | [Hne Hy]].
      * exact (eq_trans (lookup_head x v valuation)
                 (eq_sym (lookup_head x v vars))).
      * exact (eq_trans (lookup_other y x v valuation Hne)
                 (eq_trans (Hagrees y Hy)
                    (eq_sym (lookup_other y x v vars Hne)))).
Qed.

Theorem add_definitions_of_params_env_satisfies_strictly
    : add_definitions_of_params_env_satisfies_strictly_statement.
Proof.
  intros tenv statics vars vars' params. revert tenv vars.
  induction params as [ | [x kind] params IH];
    intros tenv vars vs Hinvariant Hdistinct Hfresh Hkinds Hbind Hsat.
  - inversion Hkinds; subst. simpl in Hbind. injection Hbind as <-.
    exact Hsat.
  - inversion Hkinds as [ | param v params' vs' Hkind Hrest]; subst.
    simpl in Hbind.
    change (negb (among x (map fst params)) && distinct (map fst params)
            = true) in Hdistinct.
    apply andb_true_iff in Hdistinct. destruct Hdistinct as [Hx Hdistinct].
    apply negb_true_iff in Hx.
    assert (Hfresh_x : Typing_env.mem None tenv (Name_var x) = false).
    { apply Hfresh. left. reflexivity. }
    apply (IH (Typing_env.add_variable_definition tenv x kind
                 Name_mode.normal) ((x, v) :: vars) vs').
    + apply add_variable_definition_invariant; assumption.
    + exact Hdistinct.
    + intros y Hin. rewrite mem_add_variable_definition.
      * apply Hfresh. right. exact Hin.
      * intros ->. apply among_In in Hin. congruence.
    + exact Hrest.
    + exact Hbind.
    + apply add_variable_definition_env_satisfies_strictly;
        [ exact (proj1 Hinvariant) | exact Hfresh_x | exact Hkind
        | exact Hsat ].
Qed.

(* The variables in scope once a variable is given a type. *)
Lemma replace_equation_in_scope (tenv : Typing_env.t) (x : variable)
    (ty : flambda_type) (y : variable) :
  in_scope_in_terms (Typing_env.replace_equation tenv (Name_var x) ty) y
  <-> in_scope_in_terms tenv y.
Proof.
  rewrite !in_scope_in_terms_lookup.
  change (Typing_env.min_binding_time
            (Typing_env.replace_equation tenv (Name_var x) ty))
    with (Typing_env.min_binding_time tenv).
  destruct (Pos.eq_dec y x) as [-> | Hne].
  - rewrite (replace_equation_lookup tenv (Name_var x) ty).
    destruct (Keyed.lookup name_eqb (Name_var x)
                (Typing_env.names_to_types tenv)) as [[ty0 btm0] | ]; simpl.
    + split.
      * intros [ty1 [btm1 [[= <- <-] Hmode]]]. exists ty0, btm0.
        split; [ reflexivity | exact Hmode ].
      * intros [ty1 [btm1 [[= <- <-] Hmode]]]. exists ty, btm0.
        split; [ reflexivity | exact Hmode ].
    + reflexivity.
  - rewrite (replace_equation_lookup_other tenv (Name_var x) (Name_var y) ty);
      [ reflexivity | congruence ].
Qed.

Theorem replace_equation_env_satisfies_strictly
    : replace_equation_env_satisfies_strictly_statement.
Proof.
  intros tenv statics vars x ty Hx Hfree Htype
    [Hbound [valuation [Hsatisfied Hagrees]]].
  split.
  - intros y Hy. apply Hbound. apply (replace_equation_in_scope tenv x ty y).
    exact Hy.
  - exists valuation. split.
    + apply replace_equation_satisfied; [ exact Hsatisfied | ].
      intros v Hv. right. rewrite value_of_name_var in Hv.
      rewrite (Hagrees x Hx) in Hv.
      apply (type_satisfied_coincide statics vars valuation v ty);
        [ | exact (Htype v Hv) ].
      intros y Hin. symmetry. exact (Hagrees y (Hfree y Hin)).
    + intros y Hy. apply Hagrees.
      apply (replace_equation_in_scope tenv x ty y). exact Hy.
Qed.

(* ======================================================================== *)
(* Going under binders                                                      *)
(* ======================================================================== *)

Theorem let_refines_under : let_refines_under_statement.
Proof.
  intros tenv x declared d body body' kind Hwf Hfresh Hkind Hbody vars conts
    statics Hsat.
  apply let_refines_step; [ reflexivity | intros v Hv ].
  apply Hbody. apply add_variable_definition_env_satisfies_strictly;
    [ exact Hwf | exact Hfresh | exact (Hkind statics vars v Hsat Hv)
    | exact Hsat ].
Qed.

Theorem let_typed_refines_under : let_typed_refines_under_statement.
Proof.
  intros tenv x declared d body body' ty Hwf Hfresh Hfree Htype Hbody vars
    conts statics Hsat.
  apply let_refines_step; [ reflexivity | intros v Hv ].
  pose proof (Htype statics vars v Hsat Hv) as Hty.
  apply Hbody. apply replace_equation_env_satisfies_strictly.
  - apply (add_variable_definition_in_scope tenv x _ x Hwf). left.
    reflexivity.
  - intros y Hin. apply (add_variable_definition_in_scope tenv x _ y Hwf).
    right. split; [ | exact (Hfree y Hin) ].
    exact (not_bound_not_in_scope tenv x y Hfresh (Hfree y Hin)).
  - intros v' Hlookup.
    pose proof (eq_trans (eq_sym Hlookup) (lookup_head x v vars)) as Heq.
    injection Heq as ->.
    apply (type_satisfied_coincide statics vars ((x, v) :: vars) v ty);
      [ | exact Hty ].
    intros y Hin. symmetry. apply lookup_other.
    exact (not_bound_not_in_scope tenv x y Hfresh (Hfree y Hin)).
  - apply add_variable_definition_env_satisfies_strictly;
      [ exact Hwf | exact Hfresh | | exact Hsat ].
    exact (type_satisfied_kind statics vars v ty Hty).
Qed.

Theorem let_cont_body_refines_under : let_cont_body_refines_under_statement.
Proof.
  intros tenv k h body body' Hbody vars conts statics Hsat.
  apply let_cont_non_recursive_refines_step, Hbody, Hsat.
Qed.

Theorem let_cont_recursive_body_refines_under
    : let_cont_recursive_body_refines_under_statement.
Proof.
  intros tenv handlers body body' Hbody vars conts statics Hsat.
  apply let_cont_recursive_refines_step; [ reflexivity | intros _ ].
  apply Hbody, Hsat.
Qed.

Lemma bind_params_length (params : list variable) :
  ∀ (vs : list value) (vars vars' : env),
    bind_params params vs vars = Some vars' -> length vs = length params.
Proof.
  induction params as [ | x params IH]; intros [ | v vs] vars vars' Hbind;
    simpl in Hbind; try discriminate; [ reflexivity | ].
  simpl. f_equal. exact (IH vs _ vars' Hbind).
Qed.

Lemma map_fst_combine {A B : Type} (l : list A) :
  ∀ l' : list B, length l' = length l -> map fst (combine l l') = l.
Proof.
  induction l as [ | a l IH]; intros [ | b l'] Hlength; simpl in *;
    try discriminate; [ reflexivity | ].
  f_equal. apply IH. congruence.
Qed.

Lemma kinds_of_values (params : list variable) :
  ∀ vs : list value,
    length vs = length params ->
    Forall2 (fun param v => kind_of_value v = snd param)
      (combine params (map kind_of_value vs)) vs.
Proof.
  induction params as [ | x params IH]; intros [ | v vs] Hlength;
    simpl in *; try discriminate; [ apply Forall2_nil | ].
  apply Forall2_cons; [ reflexivity | ]. apply IH. congruence.
Qed.

Theorem let_cont_handler_refines_under
    : let_cont_handler_refines_under_statement.
Proof.
  intros tenv k params metadata handler handler' body Hinvariant Hdistinct
    Hfresh Hhandler vars conts statics Hsat.
  apply (let_cont_handler_refines_where (statics_extend statics)
           (fun s s' Hs Hs' => statics_extend_trans statics s s' Hs Hs'));
    [ apply statics_extend_refl | ].
  intros vs handler_vars conts' statics' Hextend Hbind.
  pose proof (bind_params_length params vs vars handler_vars Hbind)
    as Hlength.
  assert (Hkinds : length (map kind_of_value vs) = length params).
  { rewrite length_map. exact Hlength. }
  apply (Hhandler (map kind_of_value vs) Hkinds).
  apply (add_definitions_of_params_env_satisfies_strictly tenv statics' vars
           handler_vars (combine params (map kind_of_value vs)) vs
           Hinvariant).
  - rewrite (map_fst_combine params _ Hkinds). exact Hdistinct.
  - rewrite (map_fst_combine params _ Hkinds). exact Hfresh.
  - exact (kinds_of_values params vs Hlength).
  - rewrite (map_fst_combine params _ Hkinds). exact Hbind.
  - exact (env_satisfies_strictly_statics_extend tenv statics statics' vars
             Hextend Hsat).
Qed.
