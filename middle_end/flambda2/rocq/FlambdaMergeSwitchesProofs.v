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

(* Proofs of the statements of FlambdaMergeSwitchesSpec.v. Nothing here
   needs review.

   The refinement is by the steps of the machine: where the [Switch]
   has a step it goes to an arm, which the test has found to be the
   merged application with a constant in place of the variable; the
   merged term binds the variable to that constant in the steps of
   its [Let]s, and then the two apply the same continuation to the
   same values. The rest is the recursion of
   FlambdaNormaliseProofs.collapse_switches_refines. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaMapSpec FlambdaValueSpec FlambdaPrimitiveModel FlambdaPrimitiveSpec
  FlambdaPrimitiveProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaContextSpec
  FlambdaContextProofs FlambdaNominalSpec FlambdaNominalProofs
  FlambdaAlphaProofs FlambdaNormaliseSpec FlambdaNormaliseProofs
  FlambdaMergeSwitchesSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The values of the merged arguments                                       *)
(* ======================================================================== *)

(* Under a binding of the variable to a constant an argument has the
   value that it has with the constant in place of the variable, in any
   environment that binds the other variables alike. *)
Lemma eval_simple_constant_for (v : variable) (c : const) (vars vars' : env)
    (s : simple) :
  (∀ x : variable, x <> v -> lookup x vars' = lookup x vars) ->
  eval_simple ((v, Value_const c) :: vars') s
  = eval_simple vars (constant_for v c s).
Proof.
  intros Hagree. destruct s as [x | sym | c']; simpl; try reflexivity.
  destruct (Pos.eqb_spec x v) as [-> | Hne]; [ reflexivity | ].
  simpl. apply Hagree, Hne.
Qed.

Lemma eval_simples_constant_for (v : variable) (c : const) (vars vars' : env)
    (args : list simple) :
  (∀ x : variable, x <> v -> lookup x vars' = lookup x vars) ->
  eval_simples ((v, Value_const c) :: vars') args
  = eval_simples vars (map (constant_for v c) args).
Proof.
  intros Hagree. induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite (eval_simple_constant_for v c vars vars' s Hagree), IH.
  reflexivity.
Qed.

(* So the merged application steps as the arm does. *)
Lemma merged_steps_as_arm (v : variable) (c : const) (merged : apply_cont)
    (vars vars' : env) (conts : cont_env) (statics : static_env) (hp : heap) :
  (∀ x : variable, x <> v -> lookup x vars' = lookup x vars) ->
  step
    (State (Apply_cont merged) ((v, Value_const c) :: vars') conts statics hp)
  = step
      (State
         (Apply_cont
            (Apply_cont_expr (ac_continuation merged)
               (map (constant_for v c) (ac_args merged))
               (ac_trap_action merged)))
         vars conts statics hp).
Proof.
  intros Hagree. rewrite !step_apply_cont. simpl.
  rewrite (eval_simples_constant_for v c vars vars' _ Hagree). reflexivity.
Qed.

(* The arm that a [Switch] goes to is one that the test has looked at. *)
Lemma arm_is_merged_found (how : merge_by) (v : variable)
    (merged : apply_cont) (arms : list (Z * apply_cont)) (i : Z)
    (ac : apply_cont) :
  forallb (arm_is_merged how v merged) arms = true ->
  find_arm i arms = Some ac ->
  ∃ c : const,
    constant_of_arm how i = Some c
    ∧ ac
      = Apply_cont_expr (ac_continuation merged)
          (map (constant_for v c) (ac_args merged))
          (ac_trap_action merged).
Proof.
  intros Hall Hfind. apply find_arm_in in Hfind.
  rewrite forallb_forall in Hall. specialize (Hall (i, ac) Hfind).
  unfold arm_is_merged in Hall. simpl in Hall.
  destruct (constant_of_arm how i) as [c | ]; [ | discriminate ].
  exists c. split; [ reflexivity | ].
  destruct (apply_cont_eq_dec ac _) as [Heq | ]; [ exact Heq | discriminate ].
Qed.

Lemma naked_immediate_of_value_some (w : value) (i : Z) :
  naked_immediate_of_value w = Some i -> w = Value_const (Naked_immediate i).
Proof.
  destruct w; simpl; try discriminate.
  match goal with c : const |- _ => destruct c; simpl; try discriminate end.
  intros [= ->]. reflexivity.
Qed.

(* ======================================================================== *)
(* The steps of the new [Let]s                                              *)
(* ======================================================================== *)

Lemma step_bind_tagged (v : variable) (i : Z) (body : expr) (vars : env)
    (conts : cont_env) (statics : static_env) (hp : heap) :
  lookup v vars = Some (Value_const (Naked_immediate i)) ->
  in_range (int_width Standard_naked_immediate) i = true ->
  step (State (bind_tagged v body) vars conts statics hp)
  = Step
      (State body ((v, Value_const (Tagged_immediate i)) :: vars) conts
         statics hp).
Proof.
  intros Hv Hrange. unfold bind_tagged. rewrite step_let.
  cbn [eval_named eval_simples eval_simple]. rewrite Hv.
  cbn [eval_prim eval_unary_primitive int_of_value].
  rewrite Hrange. reflexivity.
Qed.

Lemma step_bind_negated (v : variable) (i : Z) (c : const) (body : expr)
    (vars : env) (conts : cont_env) (statics : static_env) (hp : heap) :
  lookup v vars = Some (Value_const (Tagged_immediate i)) ->
  constant_of_arm By_tagging_and_negating i = Some c ->
  step (State (bind_negated v body) vars conts statics hp)
  = Step (State body ((v, Value_const c) :: vars) conts statics hp).
Proof.
  intros Hv Hc. unfold bind_negated. rewrite step_let.
  cbn [eval_named eval_simples eval_simple]. rewrite Hv.
  cbn [eval_prim eval_unary_primitive int_of_value].
  unfold constant_of_arm in Hc.
  destruct (Z.eqb_spec i 0) as [-> | _];
    [ injection Hc as <-; reflexivity | ].
  destruct (Z.eqb_spec i 1) as [-> | _];
    [ injection Hc as <-; reflexivity | discriminate ].
Qed.

(* ======================================================================== *)
(* The refinement                                                           *)
(* ======================================================================== *)

Lemma lookup_other_variable (x v : variable) (w : value) (vars : env) :
  x <> v -> lookup x ((v, w) :: vars) = lookup x vars.
Proof.
  intros Hne. simpl. destruct (Pos.eqb_spec x v); [ contradiction | ].
  reflexivity.
Qed.

Lemma merge_by_tagging_refines (v : variable) (merged : apply_cont)
    (arms : list (Z * apply_cont)) :
  forallb (arm_is_merged By_tagging v merged) arms = true ->
  expr_refines (Switch (Var v) arms) (bind_tagged v (Apply_cont merged)).
Proof.
  intros Hall vars conts statics hp.
  destruct (step_switch_cases (Var v) arms vars conts statics hp)
    as [Hwrong | (w & i & ac & Hv & Hi & Hfind & Hstep)];
    [ apply step_undefined_refines, Hwrong | ].
  apply naked_immediate_of_value_some in Hi. subst w.
  destruct (arm_is_merged_found _ _ _ _ _ _ Hall Hfind) as (c & Hc & ->).
  unfold constant_of_arm in Hc.
  destruct (in_range (int_width Standard_naked_immediate) i) eqn:Hrange;
    [ | discriminate ].
  injection Hc as <-.
  apply equivalent_refines.
  eapply equivalent_trans; [ apply step_equivalent, Hstep | ].
  apply equivalent_sym.
  eapply equivalent_trans;
    [ apply step_equivalent, (step_bind_tagged v i); [ exact Hv | exact Hrange ]
    | ].
  apply step_eq_equivalent, merged_steps_as_arm. reflexivity.
Qed.

Lemma merge_by_negating_refines (v : variable) (merged : apply_cont)
    (arms : list (Z * apply_cont)) :
  forallb (arm_is_merged By_tagging_and_negating v merged) arms = true ->
  expr_refines (Switch (Var v) arms)
    (bind_tagged v (bind_negated v (Apply_cont merged))).
Proof.
  intros Hall vars conts statics hp.
  destruct (step_switch_cases (Var v) arms vars conts statics hp)
    as [Hwrong | (w & i & ac & Hv & Hi & Hfind & Hstep)];
    [ apply step_undefined_refines, Hwrong | ].
  apply naked_immediate_of_value_some in Hi. subst w.
  destruct (arm_is_merged_found _ _ _ _ _ _ Hall Hfind) as (c & Hc & ->).
  assert (Hrange : in_range (int_width Standard_naked_immediate) i = true).
  { unfold constant_of_arm in Hc.
    destruct (Z.eqb_spec i 0) as [-> | _]; [ reflexivity | ].
    destruct (Z.eqb_spec i 1) as [-> | _]; [ reflexivity | discriminate ]. }
  apply equivalent_refines.
  eapply equivalent_trans; [ apply step_equivalent, Hstep | ].
  apply equivalent_sym.
  eapply equivalent_trans;
    [ apply step_equivalent, (step_bind_tagged v i); [ exact Hv | exact Hrange ]
    | ].
  eapply equivalent_trans;
    [ apply step_equivalent, (step_bind_negated v i c);
      [ simpl; rewrite Pos.eqb_refl; reflexivity | exact Hc ]
    | ].
  apply step_eq_equivalent, merged_steps_as_arm.
  intros x Hne. apply lookup_other_variable, Hne.
Qed.

(* The variable passed as it is: the value that it has is the constant
   of the arm. *)
Lemma eval_simples_constant_held (v : variable) (c : const) (vars : env)
    (args : list simple) :
  lookup v vars = Some (Value_const c) ->
  eval_simples vars (map (constant_for v c) args) = eval_simples vars args.
Proof.
  intros Hv. induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite IH. destruct s as [x | sym | c']; simpl; try reflexivity.
  destruct (Pos.eqb_spec x v) as [-> | Hne]; [ | reflexivity ].
  simpl. rewrite Hv. reflexivity.
Qed.

Lemma merge_as_it_is_refines (v : variable) (merged : apply_cont)
    (arms : list (Z * apply_cont)) :
  forallb (arm_is_merged As_it_is v merged) arms = true ->
  expr_refines (Switch (Var v) arms) (Apply_cont merged).
Proof.
  intros Hall vars conts statics hp.
  destruct (step_switch_cases (Var v) arms vars conts statics hp)
    as [Hwrong | (w & i & ac & Hv & Hi & Hfind & Hstep)];
    [ apply step_undefined_refines, Hwrong | ].
  apply naked_immediate_of_value_some in Hi. subst w.
  destruct (arm_is_merged_found _ _ _ _ _ _ Hall Hfind) as (c & Hc & ->).
  injection Hc as <-.
  apply equivalent_refines.
  eapply equivalent_trans; [ apply step_equivalent, Hstep | ].
  apply step_eq_equivalent. rewrite !step_apply_cont. simpl.
  rewrite (eval_simples_constant_held v (Naked_immediate i) vars _ Hv).
  destruct merged. reflexivity.
Qed.

(* The arithmetic. An argument has the value that it has with the
   constant in place of the variable, in any environment in which the
   variable holds the constant and the other variables are bound
   alike. *)
Lemma eval_simples_constant_bound (v : variable) (c : const)
    (vars vars' : env) (args : list simple) :
  lookup v vars' = Some (Value_const c) ->
  (∀ x : variable, x <> v -> lookup x vars' = lookup x vars) ->
  eval_simples vars' args = eval_simples vars (map (constant_for v c) args).
Proof.
  intros Hv Hagree. induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite IH. destruct s as [x | sym | c']; simpl; try reflexivity.
  destruct (Pos.eqb_spec x v) as [-> | Hne]; simpl;
    [ rewrite Hv | rewrite (Hagree x Hne) ]; reflexivity.
Qed.

Lemma merged_steps_as_arm_bound (v : variable) (c : const)
    (merged : apply_cont) (vars vars' : env) (conts : cont_env)
    (statics : static_env) (hp : heap) :
  lookup v vars' = Some (Value_const c) ->
  (∀ x : variable, x <> v -> lookup x vars' = lookup x vars) ->
  step (State (Apply_cont merged) vars' conts statics hp)
  = step
      (State
         (Apply_cont
            (Apply_cont_expr (ac_continuation merged)
               (map (constant_for v c) (ac_args merged))
               (ac_trap_action merged)))
         vars conts statics hp).
Proof.
  intros Hv Hagree. rewrite !step_apply_cont. simpl.
  rewrite (eval_simples_constant_bound v c vars vars' _ Hv Hagree).
  reflexivity.
Qed.

(* What a step of the arithmetic makes of an integer of the width is
   one. *)
Lemma arithmetic_step_value_in_range (standard : standard_int)
    (arith : arithmetic_step) (a a' : Z) :
  arithmetic_step_value (int_width standard) arith a = Some a' ->
  in_range (int_width standard) a' = true.
Proof.
  destruct arith as [c | c | c]; cbn [arithmetic_step_value];
    destruct (in_range (int_width standard) c); try discriminate;
    intros [= <-]; apply wrap_in_range, int_width_positive.
Qed.

(* The [Let] of a step of the arithmetic binds the variable to what
   the step makes of the integer that it holds. *)
Lemma step_bind_arithmetic_step (standard : standard_int) (v : variable)
    (arith : arithmetic_step) (a a' : Z) (body : expr) (vars : env)
    (conts : cont_env) (statics : static_env) (hp : heap) :
  lookup v vars = Some (Value_const (const_of_int standard a)) ->
  in_range (int_width standard) a = true ->
  arithmetic_step_value (int_width standard) arith a = Some a' ->
  step
    (State (bind_arithmetic_step standard v arith body) vars conts statics hp)
  = Step
      (State body ((v, Value_const (const_of_int standard a')) :: vars) conts
         statics hp).
Proof.
  intros Hv Hrange Hvalue.
  assert
    (Hint :
      ∀ c : Z,
        in_range (int_width standard) c = true ->
        int_of_value standard (Value_const (const_of_int standard c))
        = Some c).
  { intros c Hc. destruct standard; simpl in *; rewrite Hc; reflexivity. }
  assert
    (Hkind :
      ∀ c : Z,
        kind_eqb (kind_of_value (Value_const (const_of_int standard c)))
          (kind_of_standard_int standard)
        = true).
  { intros c. destruct standard; reflexivity. }
  unfold bind_arithmetic_step. rewrite step_let.
  destruct arith as [c | c | c]; cbn [arithmetic_step_value] in Hvalue;
    destruct (in_range (int_width standard) c) eqn:Hc; try discriminate;
    injection Hvalue as <-;
    cbn [eval_named eval_simples eval_simple]; rewrite Hv;
    cbn [eval_prim eval_binary_primitive];
    rewrite (Hint a Hrange), (Hint c Hc); cbn [eval_int_arith];
    rewrite Hkind; reflexivity.
Qed.

(* So do the [Let]s of the steps, one after the other. The
   environment that they leave binds the other variables as before. *)
Lemma bind_arithmetic_steps_equivalent (standard : standard_int)
    (v : variable) (body : expr) (conts : cont_env) (statics : static_env)
    (hp : heap) (steps : list arithmetic_step) :
  ∀ (a a' : Z) (vars : env),
    lookup v vars = Some (Value_const (const_of_int standard a)) ->
    in_range (int_width standard) a = true ->
    arithmetic_value (int_width standard) steps a = Some a' ->
    ∃ vars' : env,
      lookup v vars' = Some (Value_const (const_of_int standard a'))
      ∧ (∀ x : variable, x <> v -> lookup x vars' = lookup x vars)
      ∧ equivalent
          (State (bind_arithmetic_steps standard v steps body) vars conts
             statics hp)
          (State body vars' conts statics hp).
Proof.
  induction steps as [ | arith steps IH]; intros a a' vars Hv Hrange Hvalue.
  - injection Hvalue as <-. exists vars.
    split; [ exact Hv | split; [ reflexivity | apply equivalent_refl ] ].
  - cbn [arithmetic_value] in Hvalue.
    destruct (arithmetic_step_value (int_width standard) arith a)
      as [a1 | ] eqn:Hstep; [ | discriminate ].
    destruct
      (IH a1 a' ((v, Value_const (const_of_int standard a1)) :: vars))
      as (vars' & Hv' & Hagree & Hequiv).
    + simpl. rewrite Pos.eqb_refl. reflexivity.
    + exact (arithmetic_step_value_in_range standard arith a a1 Hstep).
    + exact Hvalue.
    + exists vars'. split; [ exact Hv' | split ].
      * intros x Hne. rewrite (Hagree x Hne).
        apply lookup_other_variable, Hne.
      * eapply equivalent_trans; [ | exact Hequiv ].
        apply step_equivalent.
        exact
          (step_bind_arithmetic_step standard v arith a a1 _ vars conts
             statics hp Hv Hrange Hstep).
Qed.

Lemma merge_by_arithmetic_refines (kind : arithmetic_kind) (offset slope : Z)
    (v : variable) (merged : apply_cont) (arms : list (Z * apply_cont)) :
  forallb (arm_is_merged (By_arithmetic kind offset slope) v merged) arms
  = true ->
  expr_refines (Switch (Var v) arms)
    (bind_arithmetic kind offset slope v (Apply_cont merged)).
Proof.
  intros Hall vars conts statics hp.
  destruct (step_switch_cases (Var v) arms vars conts statics hp)
    as [Hwrong | (w & i & ac & Hv & Hi & Hfind & Hstep)];
    [ apply step_undefined_refines, Hwrong | ].
  apply naked_immediate_of_value_some in Hi. subst w.
  destruct (arm_is_merged_found _ _ _ _ _ _ Hall Hfind) as (c & Hc & ->).
  cbn [constant_of_arm] in Hc. cbv zeta in Hc.
  destruct (in_range (int_width (standard_int_of_arithmetic_kind kind)) i)
    eqn:Hrange; [ | discriminate ].
  destruct (arithmetic_value _ _ i) as [a | ] eqn:Hvalue; [ | discriminate ].
  injection Hc as <-.
  apply equivalent_refines.
  eapply equivalent_trans; [ apply step_equivalent, Hstep | ].
  apply equivalent_sym.
  unfold bind_arithmetic. cbv zeta.
  destruct kind; cbn [standard_int_of_arithmetic_kind] in *.
  - eapply equivalent_trans;
      [ apply step_equivalent, (step_bind_tagged v i);
        [ exact Hv | exact Hrange ]
      | ].
    destruct
      (bind_arithmetic_steps_equivalent Standard_tagged_immediate v
         (Apply_cont merged) conts statics hp
         (arithmetic_steps (int_width Standard_tagged_immediate) offset slope)
         i a ((v, Value_const (Tagged_immediate i)) :: vars))
      as (vars' & Hv' & Hagree & Hequiv);
      [ simpl; rewrite Pos.eqb_refl; reflexivity | exact Hrange
      | exact Hvalue | ].
    eapply equivalent_trans; [ exact Hequiv | ].
    apply step_eq_equivalent, merged_steps_as_arm_bound; [ exact Hv' | ].
    intros x Hne. rewrite (Hagree x Hne). apply lookup_other_variable, Hne.
  - destruct
      (bind_arithmetic_steps_equivalent Standard_naked_immediate v
         (Apply_cont merged) conts statics hp
         (arithmetic_steps (int_width Standard_naked_immediate) offset slope)
         i a vars)
      as (vars' & Hv' & Hagree & Hequiv);
      [ exact Hv | exact Hrange | exact Hvalue | ].
    eapply equivalent_trans; [ exact Hequiv | ].
    apply step_eq_equivalent, merged_steps_as_arm_bound;
      [ exact Hv' | exact Hagree ].
Qed.

Lemma merge_switch_refines (scrutinee : simple)
    (arms : list (Z * apply_cont)) :
  expr_refines (Switch scrutinee arms) (merge_switch scrutinee arms).
Proof.
  unfold merge_switch.
  destruct scrutinee as [v | sym | c]; try apply expr_refines_refl.
  destruct arms as [ | [i ac] [ | [i' ac'] others]];
    try apply expr_refines_refl.
  cbv zeta.
  destruct (var_in_simples v _); [ | apply expr_refines_refl ].
  destruct (forallb (arm_is_merged By_tagging v _) _) eqn:Htagging;
    [ apply merge_by_tagging_refines, Htagging | ].
  destruct (forallb (arm_is_merged By_tagging_and_negating v _) _)
    eqn:Hnegating; [ apply merge_by_negating_refines, Hnegating | ].
  destruct (forallb (arm_is_merged As_it_is v _) _) eqn:Has_it_is;
    [ apply merge_as_it_is_refines, Has_it_is | ].
  destruct (arithmetic_of_arms _ _ _ _) as [[[kind offset] slope] | ];
    [ | apply expr_refines_refl ].
  destruct (_ && _) eqn:Harithmetic; [ | apply expr_refines_refl ].
  apply andb_prop in Harithmetic as [_ Harithmetic].
  apply merge_by_arithmetic_refines, Harithmetic.
Qed.

Fixpoint merge_switches_refines_aux (e : expr) :
  expr_refines e (merge_switches e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    simpl; try apply expr_refines_refl.
  - exact (plug_refines (Let_body x kind d Hole) _ _ (not_many _)
      (merge_switches_refines_aux body)).
  - exact (plug_refines (Let_static_body bindings Hole) _ _ (not_many _)
      (merge_switches_refines_aux body)).
  - apply (expr_refines_trans _
      (Let_cont_non_recursive k
         (Handler params metadata (merge_switches handler)) body)).
    + exact (plug_refines
        (Let_cont_non_recursive_handler k params metadata Hole body)
        _ _ (not_many _)
        (merge_switches_refines_aux handler)).
    + exact (plug_refines
        (Let_cont_non_recursive_body k
           (Handler params metadata (merge_switches handler)) Hole)
        _ _ (not_many _) (merge_switches_refines_aux body)).
  - exact (plug_refines (Let_cont_recursive_body handlers Hole) _ _ (not_many _)
      (merge_switches_refines_aux body)).
  - apply merge_switch_refines.
Qed.

Theorem merge_switches_refines : merge_switches_refines_statement.
Proof. exact merge_switches_refines_aux. Qed.

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

(* A renaming is injective. The lemmas have names of their own, as the
   files that use this one have lemmas that say the same. *)
Lemma renamed_simple_same (r : renaming) (s s' : simple) :
  rename_simple r s = rename_simple r s' -> s = s'.
Proof.
  destruct s, s'; simpl; intros Heq; try discriminate; try exact Heq.
  injection Heq as Heq. apply rename_variable_injective in Heq. congruence.
Qed.

Lemma renamed_simples_same (r : renaming) (args args' : list simple) :
  map (rename_simple r) args = map (rename_simple r) args' -> args = args'.
Proof.
  revert args'.
  induction args as [ | s args IH]; intros [ | s' args']; simpl; intros Heq;
    try discriminate; [ reflexivity | ].
  injection Heq as Hs Hargs.
  apply renamed_simple_same in Hs. apply IH in Hargs. congruence.
Qed.

Lemma renamed_trap_action_same (r : renaming)
    (action action' : option trap_action) :
  option_map (rename_trap_action r) action
  = option_map (rename_trap_action r) action' ->
  action = action'.
Proof.
  destruct action as [[k | k kind] | ], action' as [[k' | k' kind'] | ];
    simpl; intros Heq; try discriminate; try reflexivity;
    injection Heq as Hk; apply rename_continuation_injective in Hk;
    congruence.
Qed.

Lemma renamed_apply_cont_same (r : renaming) (ac ac' : apply_cont) :
  rename_apply_cont r ac = rename_apply_cont r ac' -> ac = ac'.
Proof.
  destruct ac as [k args trap], ac' as [k' args' trap'].
  unfold rename_apply_cont. simpl. intros Heq.
  injection Heq as Hk Hargs Htrap.
  apply rename_continuation_injective in Hk.
  apply renamed_simples_same in Hargs.
  apply renamed_trap_action_same in Htrap. congruence.
Qed.

Lemma forallb_under_map {A B : Type} (f : B -> bool) (g : A -> B)
    (h : A -> bool) (l : list A) :
  (∀ a : A, f (g a) = h a) -> forallb f (map g l) = forallb h l.
Proof.
  intros Hfg. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hfg, IH. reflexivity.
Qed.

(* Each function that the rewrite is made of commutes with a renaming. *)
Lemma constant_for_renamed (r : renaming) (v : variable) (c : const)
    (s : simple) :
  constant_for (rename_variable r v) c (rename_simple r s)
  = rename_simple r (constant_for v c s).
Proof.
  destruct s as [x | sym | c']; simpl; try reflexivity.
  rewrite rename_variable_eqb. destruct (Pos.eqb x v); reflexivity.
Qed.

Lemma constants_for_renamed (r : renaming) (v : variable) (c : const)
    (args : list simple) :
  map (constant_for (rename_variable r v) c) (map (rename_simple r) args)
  = map (rename_simple r) (map (constant_for v c) args).
Proof.
  rewrite !map_map. apply map_ext. intros s. apply constant_for_renamed.
Qed.

Lemma merged_arguments_renamed (r : renaming) (v : variable)
    (args args' : list simple) :
  merged_arguments (rename_variable r v) (map (rename_simple r) args)
    (map (rename_simple r) args')
  = map (rename_simple r) (merged_arguments v args args').
Proof.
  revert args'.
  induction args as [ | s args IH]; intros [ | s' args']; simpl;
    try reflexivity.
  rewrite IH. f_equal.
  destruct (simple_eq_dec s s') as [-> | Hne],
    (simple_eq_dec (rename_simple r _) (rename_simple r _)) as [Heq | Hne'];
    try reflexivity; [ contradiction | ].
  elim Hne. exact (renamed_simple_same r _ _ Heq).
Qed.

Lemma var_in_simples_renamed (r : renaming) (v : variable)
    (args : list simple) :
  var_in_simples (rename_variable r v) (map (rename_simple r) args)
  = var_in_simples v args.
Proof.
  unfold var_in_simples. induction args as [ | s args IH]; simpl;
    [ reflexivity | ].
  rewrite IH. f_equal. destruct s; simpl; try reflexivity.
  apply rename_variable_eqb.
Qed.

Lemma arm_is_merged_renamed (how : merge_by) (r : renaming) (v : variable)
    (merged : apply_cont) (arm : Z * apply_cont) :
  arm_is_merged how (rename_variable r v) (rename_apply_cont r merged)
    (fst arm, rename_apply_cont r (snd arm))
  = arm_is_merged how v merged arm.
Proof.
  unfold arm_is_merged. cbn [fst snd].
  destruct (constant_of_arm how (fst arm)) as [c | ]; [ | reflexivity ].
  set (target :=
    Apply_cont_expr (ac_continuation merged)
      (map (constant_for v c) (ac_args merged)) (ac_trap_action merged)).
  replace
    (Apply_cont_expr (ac_continuation (rename_apply_cont r merged))
       (map (constant_for (rename_variable r v) c)
          (ac_args (rename_apply_cont r merged)))
       (ac_trap_action (rename_apply_cont r merged)))
    with (rename_apply_cont r target).
  - destruct (apply_cont_eq_dec (snd arm) target) as [-> | Hne],
      (apply_cont_eq_dec (rename_apply_cont r _) (rename_apply_cont r _))
        as [Heq | Hne'];
      try reflexivity; [ contradiction | ].
    elim Hne. exact (renamed_apply_cont_same r _ _ Heq).
  - unfold target, rename_apply_cont. cbn [ac_continuation ac_args
      ac_trap_action].
    rewrite constants_for_renamed. reflexivity.
Qed.

Lemma first_difference_renamed (r : renaming) (args args' : list simple) :
  first_difference (map (rename_simple r) args) (map (rename_simple r) args')
  = first_difference args args'.
Proof.
  revert args'.
  induction args as [ | s args IH]; intros [ | s' args']; simpl;
    try reflexivity.
  destruct (simple_eq_dec s s') as [-> | Hne],
    (simple_eq_dec (rename_simple r _) (rename_simple r _)) as [Heq | Hne'].
  - apply IH.
  - contradiction.
  - elim Hne. exact (renamed_simple_same r _ _ Heq).
  - destruct s, s'; reflexivity.
Qed.

Lemma arithmetic_of_arms_renamed (r : renaming) (i i' : Z)
    (args args' : list simple) :
  arithmetic_of_arms i i' (map (rename_simple r) args)
    (map (rename_simple r) args')
  = arithmetic_of_arms i i' args args'.
Proof.
  unfold arithmetic_of_arms. rewrite first_difference_renamed. reflexivity.
Qed.

Lemma bind_arithmetic_steps_renamed (r : renaming) (standard : standard_int)
    (v : variable) (steps : list arithmetic_step) (body : expr) :
  rename_expr r (bind_arithmetic_steps standard v steps body)
  = bind_arithmetic_steps standard (rename_variable r v) steps
      (rename_expr r body).
Proof.
  induction steps as [ | [c | c | c] steps IH]; simpl;
    [ reflexivity | rewrite IH; reflexivity .. ].
Qed.

Lemma bind_arithmetic_renamed (r : renaming) (kind : arithmetic_kind)
    (offset slope : Z) (v : variable) (body : expr) :
  rename_expr r (bind_arithmetic kind offset slope v body)
  = bind_arithmetic kind offset slope (rename_variable r v)
      (rename_expr r body).
Proof.
  unfold bind_arithmetic. cbv zeta.
  destruct kind; [ unfold bind_tagged; simpl | ];
    rewrite bind_arithmetic_steps_renamed; reflexivity.
Qed.

Lemma merge_switch_equivariant (r : renaming) (scrutinee : simple)
    (arms : list (Z * apply_cont)) :
  merge_switch (rename_simple r scrutinee)
    (map (fun arm => (fst arm, rename_apply_cont r (snd arm))) arms)
  = rename_expr r (merge_switch scrutinee arms).
Proof.
  destruct scrutinee as [v | sym | c]; try reflexivity.
  destruct arms as [ | [i ac] [ | [i' ac'] others]]; try reflexivity.
  unfold merge_switch. cbn [map fst snd rename_simple]. cbv zeta.
  set (merged :=
    Apply_cont_expr (ac_continuation ac)
      (merged_arguments v (ac_args ac) (ac_args ac')) None).
  replace
    (Apply_cont_expr (ac_continuation (rename_apply_cont r ac))
       (merged_arguments (rename_variable r v)
          (ac_args (rename_apply_cont r ac))
          (ac_args (rename_apply_cont r ac')))
       None)
    with (rename_apply_cont r merged)
    by (unfold merged, rename_apply_cont;
        cbn [ac_continuation ac_args ac_trap_action option_map];
        rewrite merged_arguments_renamed; reflexivity).
  change (ac_args (rename_apply_cont r merged))
    with (map (rename_simple r) (ac_args merged)).
  rewrite var_in_simples_renamed.
  change
    ((i, rename_apply_cont r ac) :: (i', rename_apply_cont r ac')
     :: map (fun arm => (fst arm, rename_apply_cont r (snd arm))) others)
    with
      (map (fun arm => (fst arm, rename_apply_cont r (snd arm)))
         ((i, ac) :: (i', ac') :: others)).
  rewrite
    !(forallb_under_map _ _ (arm_is_merged _ v merged))
    by (intros arm; apply arm_is_merged_renamed).
  destruct (var_in_simples v (ac_args merged)); [ | reflexivity ].
  destruct (forallb (arm_is_merged By_tagging v merged) _); [ reflexivity | ].
  destruct (forallb (arm_is_merged By_tagging_and_negating v merged) _);
    [ reflexivity | ].
  destruct (forallb (arm_is_merged As_it_is v merged) _); [ reflexivity | ].
  change (ac_args (rename_apply_cont r ac))
    with (map (rename_simple r) (ac_args ac)).
  change (ac_args (rename_apply_cont r ac'))
    with (map (rename_simple r) (ac_args ac')).
  rewrite arithmetic_of_arms_renamed.
  destruct (arithmetic_of_arms i i' (ac_args ac) (ac_args ac'))
    as [[[kind offset] slope] | ]; [ | reflexivity ].
  rewrite length_map,
    (forallb_under_map _ _ (arm_is_merged _ v merged))
    by (intros arm; apply arm_is_merged_renamed).
  destruct (_ && _); [ | reflexivity ].
  rewrite bind_arithmetic_renamed. reflexivity.
Qed.

Fixpoint merge_switches_equivariant_aux (r : renaming) (e : expr) :
  merge_switches (rename_expr r e) = rename_expr r (merge_switches e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    simpl; try reflexivity.
  - rewrite merge_switches_equivariant_aux. reflexivity.
  - rewrite merge_switches_equivariant_aux. reflexivity.
  - rewrite !merge_switches_equivariant_aux. reflexivity.
  - rewrite merge_switches_equivariant_aux. reflexivity.
  - apply merge_switch_equivariant.
Qed.

Theorem merge_switches_equivariant : merge_switches_equivariant_statement.
Proof. exact merge_switches_equivariant_aux. Qed.

(* ======================================================================== *)
(* Four terms                                                               *)
(* ======================================================================== *)

Theorem merge_switches_tagging_example :
  merge_switches_tagging_example_statement.
Proof. reflexivity. Qed.

Theorem merge_switches_negating_example :
  merge_switches_negating_example_statement.
Proof. reflexivity. Qed.

Theorem merge_switches_as_it_is_example :
  merge_switches_as_it_is_example_statement.
Proof. reflexivity. Qed.

Theorem merge_switches_arithmetic_example :
  merge_switches_arithmetic_example_statement.
Proof. vm_compute. reflexivity. Qed.
