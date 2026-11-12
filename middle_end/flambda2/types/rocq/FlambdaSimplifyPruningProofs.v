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


(* Proofs of the statements of FlambdaSimplifyPruningSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaMapProofs FlambdaValueSpec FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaWellFormedSpec FlambdaWellFormedProofs
  FlambdaClosuresSpec FlambdaClosuresProofs FlambdaContextWhereSpec
  FlambdaContextWhereProofs FlambdaUnusedStaticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaTypeWellFormedSpec FlambdaTypeWellFormedProofs FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesProofs
  FlambdaEnvAliasesInvariantSpec FlambdaEnvAliasesInvariantProofs
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvProofs
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs
  FlambdaTypingEnvOperationsSpec FlambdaTypingEnvOperationsProofs
  FlambdaTypingEnvKindedSpec FlambdaTypingEnvKindedProofs
  FlambdaTypingEnvExamplesSpec FlambdaTypingEnvRefinementSpec
  FlambdaTypingEnvRefinementProofs FlambdaMeet FlambdaMeetSpec
  FlambdaSimplifyPrimitivesSpec FlambdaSimplifyPrimitivesProofs
  FlambdaSimplifyPassSpec FlambdaSimplifyPassProofs
  FlambdaSimplifyPruningSpec.
From OxCamlFlambda2Types Require FlambdaMeetExamplesSpec
  FlambdaMeetExamplesProofs FlambdaSimplifySwitchSpec
  FlambdaSimplifySwitchProofs.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The states of the run of a unit whose sets are well formed               *)
(* ======================================================================== *)

(* The copies of FlambdaSimplifyPruningSpec.v are the definitions of
   ../../rocq/FlambdaClosuresProofs.v that they copy. *)
Lemma run_valid_iff (s : state) : run_valid s <-> sets_inv s ∧ state_valid s.
Proof. reflexivity. Qed.

Theorem run_valid_kept : run_valid_kept_statement.
Proof.
  intros s s' Hvalid Hstep. apply run_valid_iff in Hvalid.
  destruct Hvalid as [Hsets Hvalid]. apply run_valid_iff. split.
  - exact (sets_inv_step s s' Hsets Hstep).
  - pose proof (state_valid_step s Hsets Hvalid) as H.
    rewrite Hstep in H. exact H.
Qed.

Theorem run_valid_initial : run_valid_initial_statement.
Proof.
  intros e Hsets. split; [ | exact (initial_state_valid e) ].
  refine (conj Hsets (conj I (conj _ _))).
  - intros id c H. discriminate H.
  - intros sym slot symbols decls slot_values H. discriminate H.
Qed.

Theorem run_valid_statics : run_valid_statics_statement.
Proof. intros s [_ (_ & _ & Hstatics)]. exact Hstatics. Qed.

Theorem run_valid_expr : run_valid_expr_statement.
Proof.
  intros e e' vars conts statics Hsets [(_ & C & S & B) Hvalid].
  exact (conj (conj Hsets (conj C (conj S B))) Hvalid).
Qed.

(* ======================================================================== *)
(* Refinement from those states                                             *)
(* ======================================================================== *)

(* What [run_valid] says of a state apart from its expression. *)
Definition rest_valid (vars : env) (conts : cont_env) (statics : static_env)
    : Prop :=
  run_valid (State Invalid vars conts statics).

Lemma run_valid_rest (e : expr) (vars : env) (conts : cont_env)
    (statics : static_env) :
  run_valid (State e vars conts statics) -> rest_valid vars conts statics.
Proof. apply run_valid_expr. reflexivity. Qed.

Lemma rest_valid_run (e : expr) (vars : env) (conts : cont_env)
    (statics : static_env) :
  sets_well_formed e = true ->
  rest_valid vars conts statics ->
  run_valid (State e vars conts statics).
Proof. intros Hsets. apply run_valid_expr. exact Hsets. Qed.

(* A step from a state whose expression has well-formed sets. *)
Lemma rest_valid_step (e e' : expr) (vars vars' : env)
    (conts conts' : cont_env) (statics statics' : static_env) :
  sets_well_formed e = true ->
  rest_valid vars conts statics ->
  step (State e vars conts statics) = Step (State e' vars' conts' statics') ->
  rest_valid vars' conts' statics'.
Proof.
  intros Hsets Hvalid Hstep. apply (run_valid_rest e').
  exact (run_valid_kept _ _ (rest_valid_run e vars conts statics Hsets Hvalid)
           Hstep).
Qed.

(* Refinement from the states that have [run_valid] but for the test of
   the expression: the form in which two steps make one with nothing
   asked of the term between. *)
Definition refines_valid (tenv : Typing_env.t) (source target : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env) (statics : static_env),
    rest_valid vars conts statics ->
    env_satisfies_strictly tenv statics vars ->
    refines (State source vars conts statics)
      (State target vars conts statics).

Lemma refines_valid_from (tenv : Typing_env.t) (source target : expr) :
  refines_valid tenv source target ->
  expr_refines_from_valid tenv source target.
Proof.
  intros H vars conts statics Hvalid. apply H.
  exact (run_valid_rest source vars conts statics Hvalid).
Qed.

Lemma from_valid_refines_valid (tenv : Typing_env.t) (source target : expr) :
  sets_well_formed source = true ->
  expr_refines_from_valid tenv source target ->
  refines_valid tenv source target.
Proof.
  intros Hsets H vars conts statics Hvalid. apply H.
  exact (rest_valid_run source vars conts statics Hsets Hvalid).
Qed.

Lemma refines_valid_trans (tenv : Typing_env.t) (e e' e'' : expr) :
  refines_valid tenv e e' -> refines_valid tenv e' e'' ->
  refines_valid tenv e e''.
Proof.
  intros H H' vars conts statics Hvalid Hsat.
  exact (refines_trans _ _ _ (H vars conts statics Hvalid Hsat)
           (H' vars conts statics Hvalid Hsat)).
Qed.

Lemma refines_under_valid (tenv : Typing_env.t) (e e' : expr) :
  expr_refines_under tenv e e' -> refines_valid tenv e e'.
Proof.
  intros H vars conts statics _ Hsat. exact (H vars conts statics Hsat).
Qed.

Lemma refines_valid_of_under_valid (tenv : Typing_env.t) (e e' : expr) :
  FlambdaSimplifySwitchSpec.expr_refines_under_valid tenv e e' ->
  refines_valid tenv e e'.
Proof.
  intros H vars conts statics Hvalid Hsat. apply H; [ | exact Hsat ].
  exact (run_valid_statics _ Hvalid).
Qed.

Theorem from_valid_weaken : from_valid_weaken_statement.
Proof.
  intros tenv e e'. split; intros H.
  - apply refines_valid_from, refines_under_valid, H.
  - apply refines_valid_from, refines_valid_of_under_valid, H.
Qed.

Theorem expr_refines_from_valid_trans
    : expr_refines_from_valid_trans_statement.
Proof.
  intros tenv e e' e'' Hsets H H' vars conts statics Hvalid Hsat.
  refine (refines_trans _ _ _ (H vars conts statics Hvalid Hsat) _).
  apply H'; [ | exact Hsat ].
  exact (run_valid_expr e e' vars conts statics Hsets Hvalid).
Qed.

Theorem from_valid_program : from_valid_program_statement.
Proof.
  intros e e' Hsets H. apply H; [ exact (run_valid_initial e Hsets) | ].
  apply create_satisfied.
Qed.

(* ======================================================================== *)
(* The sets of static bindings whose code is rewritten                      *)
(* ======================================================================== *)

(* A binding without the body of its code. The tests of the sets of a
   group that are not about the bodies of code read no more of it. *)
Definition forget_code_body (binding : static_binding) : static_binding :=
  match binding with
  | Bind_code id (Code params my_closure ret exn metadata _) =>
    Bind_code id (Code params my_closure ret exn metadata Invalid)
  | Bind_deleted_code _ | Bind_symbol _ _ => binding
  end.

Lemma forallb_map_ext {A B : Type} (f : B -> bool) (g : A -> bool)
    (h : A -> B) (l : list A) :
  (∀ a : A, f (h a) = g a) -> forallb f (map h l) = forallb g l.
Proof.
  intros Hext. induction l as [ | a l IH]; [ reflexivity | ].
  cbn [map forallb]. rewrite Hext, IH. reflexivity.
Qed.

Lemma existsb_map_ext {A B : Type} (f : B -> bool) (g : A -> bool)
    (h : A -> B) (l : list A) :
  (∀ a : A, f (h a) = g a) -> existsb f (map h l) = existsb g l.
Proof.
  intros Hext. induction l as [ | a l IH]; [ reflexivity | ].
  cbn [map existsb]. rewrite Hext, IH. reflexivity.
Qed.

Lemma forallb_same {A : Type} (f g : A -> bool) (l : list A) :
  (∀ a : A, f a = g a) -> forallb f l = forallb g l.
Proof.
  intros Hext. rewrite <- (map_id l) at 1. apply forallb_map_ext. exact Hext.
Qed.

Lemma static_set_whole_forget (bindings : list static_binding)
    (binding : static_binding) :
  static_set_whole (map forget_code_body bindings) (forget_code_body binding)
  = static_set_whole bindings binding.
Proof.
  destruct binding as [id [params my_closure ret exn metadata body] | id
                      | s const]; try reflexivity.
  destruct const; try reflexivity. cbn [forget_code_body static_set_whole].
  f_equal. apply forallb_same. intros [slot' s']. apply existsb_map_ext.
  intros [id' [params my_closure ret exn metadata body] | id' | s'' const'];
    reflexivity.
Qed.

Lemma static_sets_code_disjoint_forget (bindings : list static_binding) :
  static_sets_code_disjoint (map forget_code_body bindings)
  = static_sets_code_disjoint bindings.
Proof.
  induction bindings as [ | binding bindings IH]; [ reflexivity | ].
  cbn [map static_sets_code_disjoint]. rewrite IH. f_equal.
  apply forallb_map_ext. intros binding'.
  destruct binding as [id [params my_closure ret exn metadata body] | id
                      | s const];
    destruct binding' as [id' [params' my_closure' ret' exn' metadata' body']
                         | id' | s' const'];
    reflexivity.
Qed.

(* Two groups that are the same but for the bodies of their code pass
   the tests that are not about those bodies together. *)
Lemma let_static_sets_alike (bindings bindings' : list static_binding)
    (body body' : expr) :
  map forget_code_body bindings' = map forget_code_body bindings ->
  forallb binding_sets_well_formed bindings' = true ->
  sets_well_formed body' = true ->
  sets_well_formed (Let_static bindings body) = true ->
  sets_well_formed (Let_static bindings' body') = true.
Proof.
  intros Halike Hcode Hbody. cbn [sets_well_formed].
  rewrite !andb_true_iff. intros [[[Hwhole Hdisjoint] _] _].
  refine (conj (conj (conj _ _) Hcode) Hbody).
  - rewrite <- Hwhole.
    rewrite <- (forallb_map_ext
                  (static_set_whole (map forget_code_body bindings'))
                  (static_set_whole bindings') forget_code_body bindings'
                  (static_set_whole_forget bindings')).
    rewrite <- (forallb_map_ext
                  (static_set_whole (map forget_code_body bindings))
                  (static_set_whole bindings) forget_code_body bindings
                  (static_set_whole_forget bindings)).
    rewrite Halike. reflexivity.
  - rewrite <- Hdisjoint, <- static_sets_code_disjoint_forget, Halike.
    apply static_sets_code_disjoint_forget.
Qed.

(* ======================================================================== *)
(* Where a meet may be made                                                 *)
(* ======================================================================== *)

Theorem types_fit_b_fits : types_fit_b_fits_statement.
Proof.
  intros tenv Hinvariant Haliases Hfit.
  assert (Hall :
    ∀ (n : name) (ty : flambda_type) (btm : Binding_time.With_name_mode.t),
      Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
      = Some (ty, btm) ->
      type_well_formed ty = true
      ∧ type_kinded tenv ty
      ∧ type_equations_kinded tenv ty
      ∧ is_obviously_bottom ty = false
      ∧ (∀ s : symbol, n = Name_symbol s -> kind ty = Value)).
  { intros n ty btm Hlookup.
    pose proof (proj1 (for_all_names_b_iff
                         (fun n entry => type_fits_b tenv n entry = true)
                         (type_fits_b tenv) _ (fun _ _ _ => iff_refl _))
                  Hfit n (ty, btm) Hlookup) as Htest.
    unfold type_fits_b in Htest. cbn [fst] in Htest.
    rewrite !andb_true_iff in Htest.
    destruct Htest as [[[[Hwf Halias] Hequation] Hnot_bottom] Hsymbol].
    split; [ exact Hwf | ].
    split.
    { intros s k Hin. rewrite forallb_forall in Halias.
      exact (simple_of_kind_b_sound tenv s k (Halias (s, k) Hin)). }
    split.
    { intros m k Hin. rewrite forallb_forall in Hequation.
      exact (simple_of_kind_b_sound tenv _ k (Hequation (m, k) Hin)). }
    split; [ apply negb_true_iff; exact Hnot_bottom | ].
    intros s ->. apply kind_eqb_eq. exact Hsymbol. }
  split; [ exact Hinvariant | ].
  split.
  { intros n ty btm Hlookup. exact (proj1 (Hall n ty btm Hlookup)). }
  split.
  { split; [ | split; [ exact Haliases | ] ].
    - intros n ty btm Hlookup. exact (proj1 (proj2 (Hall n ty btm Hlookup))).
    - intros s ty btm Hlookup.
      exact (proj2 (proj2 (proj2 (proj2 (Hall _ ty btm Hlookup)))) s
               eq_refl). }
  split.
  { intros n ty btm Hlookup.
    exact (proj1 (proj2 (proj2 (Hall n ty btm Hlookup)))). }
  intros _ n ty btm Hlookup.
  exact (proj1 (proj2 (proj2 (proj2 (Hall n ty btm Hlookup))))).
Qed.

(* The two conditions that have no test. *)
Definition carried (tenv : Typing_env.t) : Prop :=
  typing_env_invariant tenv ∧ aliases_kinded tenv.

Lemma add_variable_definition_carried (tenv : Typing_env.t) (x : variable)
    (kind : flambda_kind) :
  carried tenv ->
  Typing_env.mem None tenv (Name_var x) = false ->
  carried (Typing_env.add_variable_definition tenv x kind Name_mode.normal).
Proof.
  intros [Hinvariant Haliases] Hfresh. split.
  - exact (add_variable_definition_invariant tenv x kind Name_mode.normal
             Hinvariant Hfresh).
  - exact (add_variable_definition_aliases_kinded tenv x kind
             Name_mode.normal (proj1 Hinvariant) Hfresh Haliases).
Qed.

Lemma add_symbol_definitions_carried (tenv : Typing_env.t)
    (syms : list symbol) :
  carried tenv -> carried (Typing_env.add_symbol_definitions tenv syms).
Proof.
  intros Hcarried. induction syms as [ | sym syms IH].
  - destruct tenv. exact Hcarried.
  - destruct IH as [Hinvariant Haliases]. split.
    + exact (add_symbol_definition_invariant
               (Typing_env.add_symbol_definitions tenv syms) sym Hinvariant).
    + exact (add_symbol_definition_aliases_kinded
               (Typing_env.add_symbol_definitions tenv syms) sym
               (proj1 Hinvariant) Haliases).
Qed.

Lemma add_definitions_of_params_carried
    (params : list (variable * flambda_kind)) :
  ∀ tenv : Typing_env.t,
    carried tenv ->
    distinct (map fst params) = true ->
    (∀ x : variable,
      x ∈ map fst params -> Typing_env.mem None tenv (Name_var x) = false) ->
    carried (Typing_env.add_definitions_of_params tenv params).
Proof.
  induction params as [ | [x kind] params IH];
    intros tenv Hcarried Hdistinct Hfresh; [ exact Hcarried | ].
  change (negb (among x (map fst params)) && distinct (map fst params)
          = true) in Hdistinct.
  apply andb_true_iff in Hdistinct. destruct Hdistinct as [Hx Hdistinct].
  apply negb_true_iff in Hx.
  apply (IH (Typing_env.add_variable_definition tenv x kind
               Name_mode.normal)).
  - apply add_variable_definition_carried; [ exact Hcarried | ].
    apply Hfresh. left. reflexivity.
  - exact Hdistinct.
  - intros y Hin. rewrite mem_add_variable_definition.
    + apply Hfresh. right. exact Hin.
    + intros ->. apply among_In in Hin. congruence.
Qed.

Theorem code_env_known_to_fit : code_env_known_to_fit_statement.
Proof.
  intros syms params my_closure metadata tenv Henv _. revert Henv.
  unfold code_env.
  set (symbols := Typing_env.add_symbol_definitions Typing_env.create syms).
  set (closure :=
         Typing_env.add_variable_definition symbols my_closure Value
           Name_mode.normal).
  match goal with
  | |- (if ?tests then _ else _) = _ -> _ =>
    destruct tests eqn:Htests; [ | discriminate ]
  end.
  intros [= <-].
  apply andb_prop in Htests as [Htests Hfresh].
  apply andb_prop in Htests as [Hlength Hdistinct].
  apply Nat.eqb_eq in Hlength.
  assert (Hsymbols : carried symbols).
  { apply add_symbol_definitions_carried.
    exact (conj create_invariant create_aliases_kinded). }
  assert (Hmem : Typing_env.mem None symbols (Name_var my_closure) = false).
  { reflexivity. }
  apply add_definitions_of_params_carried.
  - exact (add_variable_definition_carried symbols my_closure Value Hsymbols
             Hmem).
  - rewrite (map_fst_combine params _ Hlength). exact Hdistinct.
  - rewrite (map_fst_combine params _ Hlength). intros x Hin.
    rewrite forallb_forall in Hfresh. apply negb_true_iff.
    exact (Hfresh x Hin).
Qed.

Theorem let_keeps_fit_sound : let_keeps_fit_sound_statement.
Proof.
  intros tenv tenv' fit x d d' Hknown Hlet Hfit.
  apply andb_true_iff in Hfit. destruct Hfit as [Hfit Hkeeps].
  pose proof (Hknown Hfit) as Hcarried. revert Hlet Hkeeps.
  unfold simplify_let, let_keeps_fit.
  destruct (typing_env_well_formed tenv
            && negb (Typing_env.mem None tenv (Name_var x))) eqn:Htests;
    [ | discriminate ].
  apply andb_true_iff in Htests. destruct Htests as [_ Hfresh].
  apply negb_true_iff in Hfresh.
  destruct (simplify_named tenv d) as [ | s | ty | kind | ]; try discriminate.
  - unfold bind_simple.
    destruct (simplify_simple tenv s) as [[ty canonical] | ];
      [ | discriminate ].
    destruct (simple_in_terms_b tenv canonical
              && simple_of_kind_b tenv canonical (FlambdaTypeGrammar.kind ty));
      [ | discriminate ].
    pose proof (add_variable_definition_carried tenv x
                  (FlambdaTypeGrammar.kind ty) Hcarried Hfresh) as Hcarried1.
    set (tenv1 :=
           Typing_env.add_variable_definition tenv x
             (FlambdaTypeGrammar.kind ty) Name_mode.normal) in *.
    destruct (Typing_env.add_alias tenv1 (Var x) canonical)
      as [[ | result | ] | ] eqn:Hadd; try discriminate.
    intros [= _ <-] Hkeeps. unfold alias_keeps_fit in Hkeeps.
    rewrite !andb_true_iff in Hkeeps.
    destruct Hkeeps as [[[[[Hc1 Hc2] Hm1] Hm2] Hk1] Hk2].
    destruct Hcarried1 as [Hinvariant1 Haliases1].
    apply is_canonical_b_iff in Hc1. apply is_canonical_b_iff in Hc2.
    pose proof (proj1 (typing_env_well_formed_iff _) (proj1 Hinvariant1))
      as Hconditions.
    destruct Hconditions as [_ [_ [Hconsistent _]]].
    split.
    + exact (add_alias_invariant tenv1 (Var x) canonical result Hinvariant1
               Hc1 Hc2 Hm1 Hm2 Hadd).
    + exact (add_alias_aliases_kinded tenv1 (Var x) canonical result
               (FlambdaTypeGrammar.kind ty) Hconsistent Hc1 Hc2
               (simple_of_kind_b_sound tenv1 _ _ Hk1)
               (simple_of_kind_b_sound tenv1 _ _ Hk2) Hadd Haliases1).
  - destruct (type_in_scope_b tenv ty); [ | discriminate ].
    pose proof (add_variable_definition_carried tenv x
                  (FlambdaTypeGrammar.kind ty) Hcarried Hfresh) as Hcarried1.
    set (tenv1 :=
           Typing_env.add_variable_definition tenv x
             (FlambdaTypeGrammar.kind ty) Name_mode.normal) in *.
    intros [= _ <-] Hkeeps. unfold equation_keeps_fit in Hkeeps.
    rewrite !andb_true_iff in Hkeeps.
    destruct Hkeeps as [[[[[Hmem Hfree] Hkind] Halias] Hunknown] Hof_kind].
    destruct Hcarried1 as [Hinvariant1 Haliases1].
    split.
    + apply (replace_equation_invariant tenv1 (Name_var x) ty Hinvariant1
               Hmem).
      * intros y Hin. rewrite forallb_forall in Hfree. exact (Hfree y Hin).
      * intros ty' btm Hlookup. rewrite Hlookup in Hkind.
        apply kind_eqb_eq. exact Hkind.
      * intros alias Halias' Hcanonical. rewrite Halias' in Halias.
        apply is_canonical_b_iff in Hcanonical. rewrite Hcanonical in Halias.
        discriminate.
      * apply orb_true_iff in Hunknown. destruct Hunknown as [H | H].
        -- left. apply negb_true_iff. exact H.
        -- right.
           match goal with
           | |- ?found = None =>
             destruct found eqn:Hlookup;
               [ try rewrite Hlookup in H; cbn in H; discriminate H
               | reflexivity ]
           end.
    + exact (replace_equation_aliases_kinded tenv1 (Name_var x) ty
               (simple_of_kind_b_sound tenv1 _ _ Hof_kind) Haliases1).
  - intros [= _ <-] _.
    exact (add_variable_definition_carried tenv x kind Hcarried Hfresh).
Qed.

(* ======================================================================== *)
(* A [Let]                                                                  *)
(* ======================================================================== *)

(* After the step of a [Let] the second environment is satisfied: what
   the statements of FlambdaTypingEnvRefinementSpec.v about a [Let]
   show on their way, as they show it. *)
Definition let_establishes (tenv : Typing_env.t) (x : variable) (d : named)
    (tenv' : Typing_env.t) : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value),
    env_satisfies_strictly tenv statics vars ->
    eval_named statics vars d = Some v ->
    env_satisfies_strictly tenv' statics ((x, v) :: vars).

Lemma let_establishes_kind (tenv : Typing_env.t) (x : variable) (d : named)
    (kind : flambda_kind) :
  typing_env_well_formed tenv = true ->
  Typing_env.mem None tenv (Name_var x) = false ->
  (∀ (statics : static_env) (vars : env) (v : value),
    env_satisfies_strictly tenv statics vars ->
    eval_named statics vars d = Some v ->
    kind_of_value v = kind) ->
  let_establishes tenv x d
    (Typing_env.add_variable_definition tenv x kind Name_mode.normal).
Proof.
  intros Hwf Hfresh Hkind statics vars v Hsat Hv.
  apply add_variable_definition_env_satisfies_strictly;
    [ exact Hwf | exact Hfresh | exact (Hkind statics vars v Hsat Hv)
    | exact Hsat ].
Qed.

Lemma let_establishes_typed (tenv : Typing_env.t) (x : variable) (d : named)
    (ty : flambda_type) :
  typing_env_well_formed tenv = true ->
  Typing_env.mem None tenv (Name_var x) = false ->
  (∀ y : variable, y ∈ free_variables ty -> in_scope_in_terms tenv y) ->
  (∀ (statics : static_env) (vars : env) (v : value),
    env_satisfies_strictly tenv statics vars ->
    eval_named statics vars d = Some v ->
    type_satisfied statics vars v ty) ->
  let_establishes tenv x d
    (Typing_env.replace_equation
       (Typing_env.add_variable_definition tenv x
          (FlambdaTypeGrammar.kind ty) Name_mode.normal)
       (Name_var x) ty).
Proof.
  intros Hwf Hfresh Hfree Htype statics vars v Hsat Hv.
  pose proof (Htype statics vars v Hsat Hv) as Hty.
  apply replace_equation_env_satisfies_strictly.
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

Lemma let_establishes_simple (tenv : Typing_env.t) (x : variable) (s : simple)
    (kind : flambda_kind) (result : Typing_env.add_alias_result) :
  typing_env_well_formed tenv = true ->
  Typing_env.mem None tenv (Name_var x) = false ->
  (∀ y : variable, s = Var y -> in_scope_in_terms tenv y) ->
  simple_of_kind tenv s kind ->
  Typing_env.add_alias
    (Typing_env.add_variable_definition tenv x kind Name_mode.normal) (Var x)
    s
  = Some (Ok result) ->
  let_establishes tenv x (Simple s) (Typing_env.add_alias_result_t result).
Proof.
  intros Hwf Hfresh Hscope Hkind Hadd statics vars v Hsat Hv. simpl in Hv.
  assert (Hother :
    eval_simple ((x, v) :: vars) s = eval_simple vars s).
  { destruct s as [y | sym | c]; [ | reflexivity.. ]. simpl.
    apply lookup_other.
    exact (not_bound_not_in_scope tenv x y Hfresh (Hscope y eq_refl)). }
  apply (add_alias_env_satisfies_strictly
           (Typing_env.add_variable_definition tenv x kind Name_mode.normal)
           statics ((x, v) :: vars) (Var x) s result).
  - intros y [[= <-] | ->];
      apply (add_variable_definition_in_scope tenv x kind _ Hwf);
      [ left; reflexivity | right ].
    split; [ | exact (Hscope y eq_refl) ].
    exact (not_bound_not_in_scope tenv x y Hfresh (Hscope y eq_refl)).
  - exact Hadd.
  - rewrite Hother, Hv. simpl. apply lookup_head.
  - apply add_variable_definition_env_satisfies_strictly;
      [ exact Hwf | exact Hfresh | | exact Hsat ].
    apply (simple_of_kind_value tenv statics vars s kind v);
      [ | exact Hscope | exact Hkind | exact Hv ].
    apply env_satisfies_strictly_env_satisfies. exact Hsat.
Qed.

(* The body of a [Let] runs in a state that has [run_valid] and
   satisfies the second environment. *)
Lemma let_body_refines_valid (tenv tenv' : Typing_env.t) (x : variable)
    (declared : flambda_kind) (d : named) (body body' : expr) :
  named_sets_well_formed d = true ->
  sets_well_formed body = true ->
  let_establishes tenv x d tenv' ->
  refines_valid tenv' body body' ->
  refines_valid tenv (Let x declared d body) (Let x declared d body').
Proof.
  intros Hd Hbody Hestablishes Hrefines vars conts statics Hvalid Hsat.
  apply let_refines_step; [ reflexivity | intros v Hv Hkind ].
  apply Hrefines; [ | exact (Hestablishes statics vars v Hsat Hv) ].
  apply (rest_valid_step (Let x declared d body) body vars _ conts _ statics
           _);
    [ | exact Hvalid | ].
  - cbn [sets_well_formed]. rewrite Hd, Hbody. reflexivity.
  - rewrite step_let, Hv, (proj2 (kind_eqb_eq _ _) Hkind). reflexivity.
Qed.

Lemma canonical_named_sets (tenv : Typing_env.t) (d : named) :
  named_sets_well_formed d = true ->
  named_sets_well_formed (canonical_named tenv d) = true.
Proof.
  destruct d; cbn [canonical_named]; try (intros H; exact H).
  intros _. destruct (simplify_simples tenv _); reflexivity.
Qed.

(* A [Let] that the function goes under: its new defining expression
   has well-formed sets, and the [Let] refines the new [Let] where the
   body refines the new body under the new environment. *)
Lemma simplify_let_valid (tenv tenv' : Typing_env.t) (x : variable)
    (d d' : named) :
  simplify_let tenv x d = Step_let d' tenv' ->
  named_sets_well_formed d = true ->
  named_sets_well_formed d' = true
  ∧ ∀ (declared : flambda_kind) (body body' : expr),
      sets_well_formed body = true ->
      refines_valid tenv' body body' ->
      refines_valid tenv (Let x declared d body) (Let x declared d' body').
Proof.
  intros Hlet Hd. revert Hlet. unfold simplify_let.
  destruct (typing_env_well_formed tenv
            && negb (Typing_env.mem None tenv (Name_var x))) eqn:Htests;
    [ | discriminate ].
  apply andb_true_iff in Htests. destruct Htests as [Hwf Hfresh].
  apply negb_true_iff in Hfresh.
  pose proof (simplify_named_sound tenv d) as Hnamed.
  destruct (simplify_named tenv d) as [ | s | ty | kind | ]; simpl in Hnamed;
    try discriminate.
  - unfold bind_simple.
    destruct (simplify_simple tenv s) as [[ty canonical] | ] eqn:Hs;
      [ | discriminate ].
    destruct (simplify_simple_answer tenv s canonical ty Hs)
      as [_ Hcanonical].
    destruct (simple_in_terms_b tenv canonical
              && simple_of_kind_b tenv canonical (FlambdaTypeGrammar.kind ty))
      eqn:Htests; [ | discriminate ].
    apply andb_true_iff in Htests. destruct Htests as [Hterms Hkind].
    destruct (Typing_env.add_alias _ _ _) as [[ | result | ] | ] eqn:Hadd;
      try discriminate.
    intros [= <- <-]. split; [ reflexivity | ].
    intros declared body body' Hbody Hrefines.
    apply (refines_valid_trans tenv _
             (Let x declared (Simple canonical) body)).
    + apply refines_under_valid.
      eapply expr_refines_under_trans; [ exact (Hnamed x declared body) | ].
      apply expr_equivalent_under_refines.
      exact (let_simple_canonical tenv x declared s canonical body
               Hcanonical).
    + eapply (let_body_refines_valid tenv _ x declared (Simple canonical) body
               body' eq_refl Hbody);
        [ | exact Hrefines ].
      exact (let_establishes_simple tenv x canonical
               (FlambdaTypeGrammar.kind ty) result Hwf Hfresh
               (simple_in_terms_b_sound tenv canonical Hterms)
               (simple_of_kind_b_sound tenv canonical _ Hkind) Hadd).
  - destruct (type_in_scope_b tenv ty) eqn:Hscope; [ | discriminate ].
    intros [= <- <-]. split; [ exact (canonical_named_sets tenv d Hd) | ].
    intros declared body body' Hbody Hrefines.
    apply (refines_valid_trans tenv _ (Let x declared d body')).
    + eapply (let_body_refines_valid tenv _ x declared d body body' Hd Hbody);
        [ | exact Hrefines ].
      apply (let_establishes_typed tenv x d ty Hwf Hfresh);
        [ | exact Hnamed ].
      intros y Hy. unfold type_in_scope_b in Hscope.
      rewrite forallb_forall in Hscope. exact (Hscope y Hy).
    + apply refines_under_valid, expr_equivalent_under_refines.
      exact (canonical_named_equivalent tenv x declared d body').
  - intros [= <- <-]. split; [ exact (canonical_named_sets tenv d Hd) | ].
    intros declared body body' Hbody Hrefines.
    apply (refines_valid_trans tenv _ (Let x declared d body')).
    + eapply (let_body_refines_valid tenv _ x declared d body body' Hd Hbody);
        [ | exact Hrefines ].
      exact (let_establishes_kind tenv x d kind Hwf Hfresh Hnamed).
    + apply refines_under_valid, expr_equivalent_under_refines.
      exact (canonical_named_equivalent tenv x declared d body').
Qed.

(* ======================================================================== *)
(* A [Switch]                                                               *)
(* ======================================================================== *)

Theorem simplify_switch_rewrite_sound
    : simplify_switch_rewrite_sound_statement.
Proof.
  intros meet Hmeet tenv s arms e He. split.
  - revert He. unfold FlambdaSimplifySwitchSpec.simplify_switch.
    destruct (Typing_env.type_simple_in_term_exn tenv
                (Some Name_mode.normal) s)
      as [[[ty canonical] | ] | ]; try discriminate.
    cbn.
    destruct (FlambdaSimplifySwitchSpec.prune_arms meet tenv ty arms)
      as [arms' | ]; [ | discriminate ].
    intros [= <-]. destruct arms' as [ | [i ac] [ | arm arms']]; reflexivity.
  - intros Hfits Hmem.
    exact (FlambdaSimplifySwitchProofs.simplify_switch_refines meet tenv s
             arms e Hmeet Hfits Hmem He).
Qed.

Lemma simplify_switch_sets (tenv : Typing_env.t) (scrutinee : simple)
    (arms : list (Z * apply_cont)) :
  sets_well_formed (simplify_switch tenv scrutinee arms) = true.
Proof.
  unfold simplify_switch.
  repeat match goal with
         | |- context [match ?e with _ => _ end] => destruct e
         end;
    reflexivity.
Qed.

Lemma after_pruning_sound (tenv : Typing_env.t) (e : expr) :
  sets_well_formed e = true ->
  sets_well_formed (after_pruning tenv e) = true
  ∧ expr_refines_under tenv e (after_pruning tenv e).
Proof.
  intros Hsets.
  destruct e
    as [x declared d body | bindings body | k handler body
        | handlers body | ap | ac | scrutinee arms | ];
    cbn [after_pruning];
    try (split; [ exact Hsets | apply expr_refines_under_refl ]).
  - split; [ reflexivity | ].
    apply expr_equivalent_under_refines, simplify_apply_cont_equivalent.
  - split; [ apply simplify_switch_sets | apply simplify_switch_refines ].
Qed.

Lemma simplify_switch_pruning_sound (prune : switch_rewrite)
    (tenv : Typing_env.t) (fit : bool) (scrutinee : simple)
    (arms : list (Z * apply_cont)) :
  switch_rewrite_sound prune ->
  known_to_fit tenv fit ->
  sets_well_formed (simplify_switch_pruning prune tenv fit scrutinee arms)
  = true
  ∧ refines_valid tenv (Switch scrutinee arms)
      (simplify_switch_pruning prune tenv fit scrutinee arms).
Proof.
  intros Hprune Hknown.
  assert (Hfirst :
    sets_well_formed (simplify_switch tenv scrutinee arms) = true
    ∧ refines_valid tenv (Switch scrutinee arms)
        (simplify_switch tenv scrutinee arms)).
  { split; [ apply simplify_switch_sets | ].
    apply refines_under_valid, simplify_switch_refines. }
  unfold simplify_switch_pruning.
  destruct (fit && types_fit_b tenv
            && Typing_env.mem_simple (Some Name_mode.normal) tenv scrutinee)
    eqn:Htests; [ | exact Hfirst ].
  destruct (prune tenv scrutinee arms) as [e | ] eqn:He; [ | exact Hfirst ].
  apply andb_true_iff in Htests. destruct Htests as [Htests Hmem].
  apply andb_true_iff in Htests. destruct Htests as [Hfit Htypes].
  destruct (Hknown Hfit) as [Hinvariant Haliases].
  destruct (Hprune tenv scrutinee arms e He) as [Hsets Hrefines].
  destruct (after_pruning_sound tenv e Hsets) as [Hsets' Hafter].
  split; [ exact Hsets' | ].
  apply (refines_valid_trans tenv _ e).
  - apply refines_valid_of_under_valid. apply Hrefines; [ | exact Hmem ].
    exact (types_fit_b_fits tenv Hinvariant Haliases Htypes).
  - apply refines_under_valid. exact Hafter.
Qed.

(* ======================================================================== *)
(* The other binders                                                        *)
(* ======================================================================== *)

Lemma let_cont_body_refines_valid (tenv : Typing_env.t) (k : continuation)
    (h : continuation_handler) (body body' : expr) :
  sets_well_formed (Let_cont_non_recursive k h body) = true ->
  refines_valid tenv body body' ->
  refines_valid tenv (Let_cont_non_recursive k h body)
    (Let_cont_non_recursive k h body').
Proof.
  intros Hsets Hbody vars conts statics Hvalid Hsat.
  apply let_cont_non_recursive_refines_step. apply Hbody; [ | exact Hsat ].
  exact (rest_valid_step _ body vars _ conts _ statics _ Hsets Hvalid
           (step_let_cont_non_recursive k h body vars conts statics)).
Qed.

Lemma let_cont_recursive_body_refines_valid (tenv : Typing_env.t)
    (handlers : list (continuation * continuation_handler))
    (body body' : expr) :
  sets_well_formed (Let_cont_recursive handlers body) = true ->
  refines_valid tenv body body' ->
  refines_valid tenv (Let_cont_recursive handlers body)
    (Let_cont_recursive handlers body').
Proof.
  intros Hsets Hbody vars conts statics Hvalid Hsat.
  apply let_cont_recursive_refines_step; [ reflexivity | intros Hbinds ].
  apply Hbody; [ | exact Hsat ].
  apply (rest_valid_step _ body vars _ conts _ statics _ Hsets Hvalid).
  rewrite step_let_cont_recursive, Hbinds. reflexivity.
Qed.

Lemma let_static_body_refines_valid (tenv : Typing_env.t)
    (bindings : list static_binding) (body body' : expr) :
  sets_well_formed (Let_static bindings body) = true ->
  refines_valid
    (Typing_env.add_symbol_definitions tenv (bound_symbols bindings)) body
    body' ->
  refines_valid tenv (Let_static bindings body) (Let_static bindings body').
Proof.
  intros Hsets Hbody vars conts statics Hvalid Hsat.
  destruct (eval_static_bindings vars bindings statics) as [statics' | ]
    eqn:Hbindings.
  - assert (Hstep :
      ∀ b : expr,
        step (State (Let_static bindings b) vars conts statics)
        = Step (State b vars conts statics')).
    { intros b. rewrite step_let_static, Hbindings. reflexivity. }
    eapply refines_step; [ apply Hstep | apply Hstep | ].
    apply Hbody.
    + exact (rest_valid_step _ body vars _ conts _ statics _ Hsets Hvalid
               (Hstep body)).
    + apply add_symbol_definitions_env_satisfies_strictly.
      refine (env_satisfies_strictly_statics_extend tenv statics statics'
                vars _ Hsat).
      exact (step_extends_statics _ _ (Hstep body)).
  - apply step_undefined_refines. rewrite step_let_static, Hbindings.
    reflexivity.
Qed.

Lemma forget_simplify_static_binding (prune : switch_rewrite)
    (syms : list symbol) (binding : static_binding) :
  forget_code_body (simplify_static_binding_pruning prune syms binding)
  = forget_code_body binding.
Proof.
  destruct binding as [id [params my_closure ret exn metadata body] | id
                      | s const]; try reflexivity.
  cbn [simplify_static_binding_pruning simplify_code_pruning].
  destruct (code_env syms params my_closure metadata); [ | reflexivity ].
  destruct (Bool.eqb _ _); reflexivity.
Qed.

Lemma bound_symbols_simplify_pruning (prune : switch_rewrite)
    (syms : list symbol) (bindings : list static_binding) :
  bound_symbols (map (simplify_static_binding_pruning prune syms) bindings)
  = bound_symbols bindings.
Proof.
  induction bindings as [ | [id c | id | sym const] bindings IH];
    cbn [map simplify_static_binding_pruning bound_symbols]; congruence.
Qed.

(* ======================================================================== *)
(* A term                                                                   *)
(* ======================================================================== *)

(* By recursion on the term, as for the first function: the bodies of
   the code that a [Let_static] binds are rewritten one binding at a
   time, each by the statement of ../../rocq/FlambdaContextWhereSpec.v
   for the body of code at a predicate that a step keeps. The two
   whole states have [run_valid] together because the sets of the two
   groups are well formed together. *)
Fixpoint simplify_expr_pruning_sound (prune : switch_rewrite)
    (Hprune : switch_rewrite_sound prune) (e : expr) {struct e} :
  ∀ (tenv : Typing_env.t) (fit : bool),
    known_to_fit tenv fit ->
    sets_well_formed e = true ->
    sets_well_formed (simplify_expr_pruning prune tenv fit e) = true
    ∧ refines_valid tenv e (simplify_expr_pruning prune tenv fit e).
Proof.
  destruct e
    as [x declared d body | bindings body | k handler body
        | handlers body | ap | ac | scrutinee arms | ];
    intros tenv fit Hknown Hsets; cbn [simplify_expr_pruning].
  - pose proof Hsets as H. cbn [sets_well_formed] in H.
    apply andb_true_iff in H. destruct H as [Hd Hbody].
    pose proof (simplify_let_sound tenv x d) as Hsound.
    destruct (simplify_let tenv x d) as [ | d' tenv' | ] eqn:Hlet.
    + split; [ reflexivity | ].
      apply refines_under_valid, expr_equivalent_under_refines.
      exact (Hsound declared body).
    + destruct (simplify_let_valid tenv tenv' x d d' Hlet Hd) as [Hd' Hstep].
      destruct (simplify_expr_pruning_sound prune Hprune body tenv'
                  (fit && let_keeps_fit tenv x d)
                  (let_keeps_fit_sound tenv tenv' fit x d d' Hknown Hlet)
                  Hbody)
        as [Hbody' Hrefines].
      split.
      * cbn [sets_well_formed]. rewrite Hd', Hbody'. reflexivity.
      * exact (Hstep declared body _ Hbody Hrefines).
    + split; [ exact Hsets | ].
      apply refines_under_valid, expr_refines_under_refl.
  - assert (Hbody : sets_well_formed body = true).
    { pose proof Hsets as H. cbn [sets_well_formed] in H.
      apply andb_true_iff in H. exact (proj2 H). }
    generalize
      (Typing_env.defined_symbols
         (Typing_env.add_symbol_definitions tenv (bound_symbols bindings))).
    intros syms.
    assert (Hbindings :
      ∀ before : list static_binding,
        sets_well_formed (Let_static (before ++ bindings) body) = true ->
        sets_well_formed
          (Let_static
             (before
              ++ map (simplify_static_binding_pruning prune syms) bindings)
             body)
        = true
        ∧ refines_valid tenv (Let_static (before ++ bindings) body)
            (Let_static
               (before
                ++ map (simplify_static_binding_pruning prune syms) bindings)
               body)).
    { clear Hsets. induction bindings as [ | binding bindings IH];
        intros before Hsets.
      { split; [ exact Hsets | ].
        apply refines_under_valid, expr_refines_under_refl. }
      cbn [map].
      assert (Hone :
        sets_well_formed
          (Let_static
             (before
              ++ simplify_static_binding_pruning prune syms binding
                 :: bindings)
             body)
        = true
        ∧ refines_valid tenv (Let_static (before ++ binding :: bindings) body)
            (Let_static
               (before
                ++ simplify_static_binding_pruning prune syms binding
                   :: bindings)
               body)).
      { assert (Hsame :
          sets_well_formed (Let_static (before ++ binding :: bindings) body)
          = true
          ∧ refines_valid tenv
              (Let_static (before ++ binding :: bindings) body)
              (Let_static (before ++ binding :: bindings) body)).
        { split; [ exact Hsets | ].
          apply refines_under_valid, expr_refines_under_refl. }
        destruct binding as [id c | id | sym const];
          cbn [simplify_static_binding_pruning]; try exact Hsame.
        destruct c as [params my_closure ret exn metadata code_body].
        cbn [simplify_code_pruning].
        destruct (code_env syms params my_closure metadata)
          as [tenv_code | ] eqn:Henv; [ | exact Hsame ].
        destruct (Bool.eqb (binds_statics code_body)
                    (binds_statics
                       (simplify_expr_pruning prune tenv_code true
                          code_body)))
          eqn:Hbinds; [ | exact Hsame ].
        clear Hsame.
        assert (Hparts :
          forallb binding_sets_well_formed before = true
          ∧ sets_well_formed code_body = true
          ∧ forallb binding_sets_well_formed bindings = true).
        { pose proof Hsets as H. cbn [sets_well_formed] in H.
          rewrite !andb_true_iff in H. destruct H as [[_ H] _].
          rewrite forallb_app in H. apply andb_true_iff in H.
          destruct H as [Hbefore H].
          change (sets_well_formed code_body
                  && forallb binding_sets_well_formed bindings
                  = true) in H.
          apply andb_true_iff in H. exact (conj Hbefore H). }
        destruct Hparts as [Hbefore [Hcode Hrest]].
        destruct (simplify_expr_pruning_sound prune Hprune code_body
                    tenv_code true
                    (code_env_known_to_fit syms params my_closure metadata
                       tenv_code Henv)
                    Hcode)
          as [Hcode' Hcode_refines].
        assert (Hsets' :
          sets_well_formed
            (Let_static
               (before
                ++ Bind_code id
                     (Code params my_closure ret exn metadata
                        (simplify_expr_pruning prune tenv_code true
                           code_body))
                   :: bindings)
               body)
          = true).
        { apply (let_static_sets_alike
                   (before
                    ++ Bind_code id
                         (Code params my_closure ret exn metadata code_body)
                       :: bindings)
                   _ body body);
            [ rewrite !map_app; reflexivity | | exact Hbody | exact Hsets ].
          rewrite forallb_app, Hbefore.
          change (sets_well_formed
                    (simplify_expr_pruning prune tenv_code true code_body)
                  && forallb binding_sets_well_formed bindings
                  = true).
          rewrite Hcode', Hrest. reflexivity. }
        split; [ exact Hsets' | ].
        intros vars conts statics Hvalid Hsat.
        apply (FlambdaContextWhereProofs.let_static_code_refines_from
                 run_valid);
          [ exact run_valid_kept
          | exact (rest_valid_run _ vars conts statics Hsets Hvalid)
          | exact (rest_valid_run _ vars conts statics Hsets' Hvalid)
          | apply eqb_prop; exact Hbinds
          | ].
        intros vs callee callee_vars return_to exn_to statics' Hbind Hkinds
          Hcallee.
        split.
        - split; apply run_valid_expr; assumption.
        - intros Hrun. apply Hcode_refines.
          + exact (run_valid_rest _ _ _ _ Hrun).
          + exact (code_env_satisfied syms params my_closure metadata
                     tenv_code vs callee callee_vars statics' Henv Hkinds
                     Hcallee Hbind). }
      destruct Hone as [Hsets1 Hrefines1].
      specialize
        (IH (before ++ [simplify_static_binding_pruning prune syms binding])).
      rewrite <- !app_assoc in IH. cbn [app] in IH.
      destruct (IH Hsets1) as [Hsets2 Hrefines2].
      split; [ exact Hsets2 | ].
      exact (refines_valid_trans tenv _ _ _ Hrefines1 Hrefines2). }
    destruct (Hbindings [] Hsets) as [Hsets1 Hrefines1].
    cbn [app] in Hsets1, Hrefines1.
    assert (Hknown' :
      known_to_fit
        (Typing_env.add_symbol_definitions tenv (bound_symbols bindings))
        fit).
    { intros Hfit.
      exact (add_symbol_definitions_carried tenv _ (Hknown Hfit)). }
    destruct (simplify_expr_pruning_sound prune Hprune body _ fit Hknown'
                Hbody)
      as [Hbody' Hbody_refines].
    split.
    + pose proof Hsets1 as H. cbn [sets_well_formed] in H |- *.
      rewrite !andb_true_iff in H |- *. destruct H as [H _].
      exact (conj H Hbody').
    + eapply refines_valid_trans; [ exact Hrefines1 | ].
      apply let_static_body_refines_valid; [ exact Hsets1 | ].
      rewrite bound_symbols_simplify_pruning. exact Hbody_refines.
  - pose proof Hsets as H. cbn [sets_well_formed] in H.
    apply andb_true_iff in H. destruct H as [Hhandler Hbody].
    destruct (simplify_expr_pruning_sound prune Hprune body tenv fit Hknown
                Hbody)
      as [Hbody' Hrefines].
    split.
    + cbn [sets_well_formed]. rewrite Hhandler, Hbody'. reflexivity.
    + exact (let_cont_body_refines_valid tenv k handler body _ Hsets
               Hrefines).
  - pose proof Hsets as H. cbn [sets_well_formed] in H.
    apply andb_true_iff in H. destruct H as [Hhandlers Hbody].
    destruct (simplify_expr_pruning_sound prune Hprune body tenv fit Hknown
                Hbody)
      as [Hbody' Hrefines].
    split.
    + cbn [sets_well_formed]. rewrite Hhandlers, Hbody'. reflexivity.
    + exact (let_cont_recursive_body_refines_valid tenv handlers body _ Hsets
               Hrefines).
  - split; [ reflexivity | ].
    apply refines_under_valid, expr_refines_under_refl.
  - split; [ reflexivity | ].
    apply refines_under_valid, expr_equivalent_under_refines.
    apply simplify_apply_cont_equivalent.
  - exact (simplify_switch_pruning_sound prune tenv fit scrutinee arms Hprune
             Hknown).
  - split; [ reflexivity | ].
    apply refines_under_valid, expr_refines_under_refl.
Qed.

Theorem simplify_expr_pruning_sets : simplify_expr_pruning_sets_statement.
Proof.
  intros prune tenv fit e Hprune Hknown Hsets.
  exact (proj1 (simplify_expr_pruning_sound prune Hprune e tenv fit Hknown
                  Hsets)).
Qed.

Theorem simplify_expr_pruning_refines
    : simplify_expr_pruning_refines_statement.
Proof.
  intros prune tenv fit e Hprune Hknown vars conts statics Hvalid Hsat.
  assert (Hsets : sets_well_formed e = true) by exact (proj1 (proj1 Hvalid)).
  exact (proj2 (simplify_expr_pruning_sound prune Hprune e tenv fit Hknown
                  Hsets)
           vars conts statics (run_valid_rest e vars conts statics Hvalid)
           Hsat).
Qed.

Theorem simplify_by_types_pruning_refines
    : simplify_by_types_pruning_refines_statement.
Proof.
  intros prune e Hprune Hsets. apply (from_valid_program e _ Hsets).
  apply simplify_expr_pruning_refines; [ exact Hprune | ].
  intros _. exact (conj create_invariant create_aliases_kinded).
Qed.

(* With a [prune] that answers nothing, by the same recursion. *)
Fixpoint simplify_expr_no_pruning_eq (e : expr) {struct e} :
  ∀ (tenv : Typing_env.t) (fit : bool),
    simplify_expr_pruning no_pruning tenv fit e = simplify_expr tenv e.
Proof.
  destruct e
    as [x declared d body | bindings body | k handler body
        | handlers body | ap | ac | scrutinee arms | ];
    intros tenv fit; cbn [simplify_expr_pruning simplify_expr].
  - destruct (simplify_let tenv x d) as [ | d' tenv' | ]; try reflexivity.
    f_equal. apply simplify_expr_no_pruning_eq.
  - f_equal; [ | apply simplify_expr_no_pruning_eq ].
    generalize
      (Typing_env.defined_symbols
         (Typing_env.add_symbol_definitions tenv (bound_symbols bindings))).
    intros syms.
    induction bindings as [ | binding bindings IH]; [ reflexivity | ].
    cbn [map]. f_equal; [ | exact IH ].
    destruct binding as [id c | id | sym const]; try reflexivity.
    destruct c as [params my_closure ret exn metadata code_body].
    cbn [simplify_static_binding_pruning simplify_code_pruning
           simplify_static_binding simplify_code].
    destruct (code_env syms params my_closure metadata) as [tenv_code | ];
      [ | reflexivity ].
    rewrite (simplify_expr_no_pruning_eq code_body tenv_code true).
    reflexivity.
  - f_equal. apply simplify_expr_no_pruning_eq.
  - f_equal. apply simplify_expr_no_pruning_eq.
  - reflexivity.
  - reflexivity.
  - unfold simplify_switch_pruning, no_pruning.
    destruct (fit && types_fit_b tenv
              && Typing_env.mem_simple (Some Name_mode.normal) tenv
                   scrutinee);
      reflexivity.
  - reflexivity.
Qed.

Theorem simplify_expr_no_pruning : simplify_expr_no_pruning_statement.
Proof. intros tenv fit e. apply simplify_expr_no_pruning_eq. Qed.

(* ======================================================================== *)
(* With the meet that the contract is proved of                             *)
(* ======================================================================== *)

Theorem simplify_by_types_pruning_with_refines
    : simplify_by_types_pruning_with_refines_statement.
Proof.
  intros join fuel e Hjoin Hsets.
  apply simplify_by_types_pruning_refines; [ | exact Hsets ].
  apply simplify_switch_rewrite_sound.
  exact (FlambdaSimplifySwitchProofs.meet_to_prove_bottom_sound join fuel
           Hjoin).
Qed.

Theorem prune_by_types_refines : prune_by_types_refines_statement.
Proof.
  intros fuel e. unfold prune_by_types.
  destruct (sets_well_formed e) eqn:Hsets; [ | apply refines_refl ].
  apply simplify_by_types_pruning_with_refines; [ | exact Hsets ].
  exact FlambdaMeetExamplesProofs.forgetful_join_sound.
Qed.

(* ======================================================================== *)
(* An example                                                               *)
(* ======================================================================== *)

Theorem example_pruning_no_arm : example_pruning_no_arm_statement.
Proof. intros k0 k1. split; vm_compute; reflexivity. Qed.
