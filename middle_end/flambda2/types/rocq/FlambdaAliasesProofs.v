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

(* Proofs of the statements of FlambdaAliasesSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaContextProofs FlambdaNominalSpec
  FlambdaNominalProofs FlambdaNormaliseSpec FlambdaNormaliseProofs.
From OxCamlFlambda2Types Require Import FlambdaTypesSpec FlambdaTypesProofs
  FlambdaAliasesSpec.
Import ListNotations.

(* ======================================================================== *)
(* Forgetting a name                                                        *)
(* ======================================================================== *)

Lemma env_satisfies_incl (tenv tenv' : typing_env) (vars : env) :
  (∀ entry : variable * flambda_type, entry ∈ tenv' -> entry ∈ tenv) ->
  env_satisfies tenv vars -> env_satisfies tenv' vars.
Proof. intros Hincl Hsat x t Hin. apply Hsat, Hincl, Hin. Qed.

Lemma drop_var_incl (x : variable) (tenv : typing_env)
    (entry : variable * flambda_type) :
  entry ∈ drop_var x tenv -> entry ∈ tenv.
Proof. unfold drop_var. intros Hin. apply filter_In in Hin. tauto. Qed.

Lemma drop_var_fresh (x : variable) (tenv : typing_env) :
  ~ var_in_typing_env x (drop_var x tenv).
Proof.
  intros (y & t & Hin & Hmention). unfold drop_var in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hkept].
  apply andb_true_iff in Hkept as [Hkey Htype].
  apply negb_true_iff in Hkey, Htype.
  destruct Hmention as [-> | (s & -> & Hfree)].
  - rewrite Pos.eqb_refl in Hkey. discriminate.
  - simpl in Htype. apply var_in_simple_sound in Hfree. congruence.
Qed.

Lemma drop_vars_incl (xs : list variable) (tenv : typing_env)
    (entry : variable * flambda_type) :
  entry ∈ drop_vars xs tenv -> entry ∈ tenv.
Proof.
  induction xs as [ | x xs IH]; simpl; [ auto | ].
  intros Hin. apply IH, (drop_var_incl x), Hin.
Qed.

Lemma drop_vars_fresh (xs : list variable) (tenv : typing_env) (x : variable) :
  x ∈ xs -> ~ var_in_typing_env x (drop_vars xs tenv).
Proof.
  induction xs as [ | y xs IH]; simpl; [ contradiction | ].
  intros [-> | Hin]; [ apply drop_var_fresh | ].
  intros (z & t & Hz & Hmention). apply (IH Hin).
  exists z, t. split; [ exact (drop_var_incl y _ _ Hz) | exact Hmention ].
Qed.

(* ======================================================================== *)
(* Following aliases at the head of a term                                  *)
(* ======================================================================== *)

Lemma canonical_value_slots_sound (tenv : typing_env) (vars : env)
    (slots : list (value_slot * simple)) :
  env_satisfies tenv vars ->
  eval_value_slots vars (canonical_value_slots tenv slots)
  = eval_value_slots vars slots.
Proof.
  intros Hsat. induction slots as [ | [slot s] slots IH]; simpl;
    [ reflexivity | ].
  rewrite (canonical_simple_sound tenv vars s Hsat), IH. reflexivity.
Qed.

Lemma canonical_named_sound (tenv : typing_env) (vars : env)
    (statics : static_env) (d : named) :
  env_satisfies tenv vars ->
  eval_named statics vars (canonical_named tenv d) = eval_named statics vars d.
Proof.
  intros Hsat. destruct d as [s | p args | code slots | slot closure]; simpl.
  - apply canonical_simple_sound, Hsat.
  - rewrite (canonical_simples_sound tenv vars args Hsat). reflexivity.
  - rewrite (canonical_value_slots_sound tenv vars slots Hsat). reflexivity.
  - rewrite (canonical_simple_sound tenv vars closure Hsat). reflexivity.
Qed.

Lemma canonical_static_bindings_sound (tenv : typing_env) (vars : env)
    (bindings : list static_binding) :
  env_satisfies tenv vars ->
  ∀ statics : static_env,
    eval_static_bindings vars (map (canonical_static_binding tenv) bindings)
      statics
    = eval_static_bindings vars bindings statics.
Proof.
  intros Hsat.
  induction bindings as [ | binding bindings IH]; intros statics;
    [ reflexivity | ].
  destruct binding
    as [id c | id | sym [code slots | tag fields | s | bytes]];
    simpl; try apply IH.
  - rewrite (canonical_value_slots_sound tenv vars slots Hsat).
    destruct (eval_value_slots vars slots); simpl; [ apply IH | reflexivity ].
  - rewrite (canonical_simples_sound tenv vars fields Hsat).
    destruct (eval_simples vars fields); simpl; [ apply IH | reflexivity ].
  - rewrite (canonical_simple_sound tenv vars s Hsat).
    destruct (eval_simple vars s); simpl; [ apply IH | reflexivity ].
Qed.

Lemma find_arm_canonical (tenv : typing_env) (i : Z)
    (arms : list (Z * apply_cont)) :
  find_arm i
    (map (fun arm => (fst arm, canonical_apply_cont tenv (snd arm))) arms)
  = option_map (canonical_apply_cont tenv) (find_arm i arms).
Proof.
  induction arms as [ | [discriminant ac] arms IH]; simpl; [ reflexivity | ].
  destruct (Z.eqb i discriminant); [ reflexivity | exact IH ].
Qed.

Lemma canonical_apply_cont_equivalent (tenv : typing_env) (ac : apply_cont)
    (vars : env) (conts : cont_env) (statics : static_env) :
  env_satisfies tenv vars ->
  equivalent (State (Apply_cont ac) vars conts statics)
    (State (Apply_cont (canonical_apply_cont tenv ac)) vars conts statics).
Proof.
  intros Hsat. apply (equivalent_of_run 1 1). simpl.
  rewrite (canonical_simples_sound tenv vars (ac_args ac) Hsat). reflexivity.
Qed.

(* ======================================================================== *)
(* Under binders                                                            *)
(* ======================================================================== *)

(* The environment under a [Let] satisfies what is known there. *)
Lemma env_satisfies_under_let (tenv : typing_env) (x : variable) (d : named)
    (vars : env) (statics : static_env) (v : value) :
  env_satisfies tenv vars ->
  eval_named statics vars d = Some v ->
  env_satisfies (typing_env_under_let tenv x d) ((x, v) :: vars).
Proof.
  intros Hsat Hd.
  assert (Hdropped : env_satisfies (drop_var x tenv) vars)
    by exact (env_satisfies_incl tenv _ vars (drop_var_incl x tenv) Hsat).
  assert (Hunknown : env_satisfies (drop_var x tenv) ((x, v) :: vars)).
  { apply (env_satisfies_incl ((x, Unknown) :: drop_var x tenv));
      [ intros entry Hin; right; exact Hin | ].
    exact (env_satisfies_extend _ vars x v Unknown Hdropped
      (drop_var_fresh x tenv) I). }
  destruct d as [s | p args | code slots | slot closure]; simpl;
    try exact Hunknown.
  destruct (var_in_simple x s) eqn:Hmention; [ exact Hunknown | ].
  apply (env_satisfies_extend _ vars x v (Equals s) Hdropped
    (drop_var_fresh x tenv)).
  simpl in Hd |- *. rewrite <- Hd.
  destruct s as [y | sym | c]; simpl in Hmention |- *; try reflexivity.
  destruct (Pos.eqb_spec y x) as [-> | _]; [ | reflexivity ].
  rewrite Pos.eqb_refl in Hmention. discriminate.
Qed.

Lemma let_equivalent_in (tenv : typing_env) (x : variable) (d : named)
    (body body' : expr) :
  expr_equivalent_in (typing_env_under_let tenv x d) body body' ->
  expr_equivalent_in tenv (Let x d body) (Let x d body').
Proof.
  intros Hbody vars conts statics Hsat.
  destruct (eval_named statics vars d) as [v | ] eqn:Hd.
  - eapply equivalent_step;
      [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity | ].
    apply Hbody.
    exact (env_satisfies_under_let tenv x d vars statics v Hsat Hd).
  - apply (equivalent_of_run 1 1). simpl. rewrite Hd. reflexivity.
Qed.

Lemma let_static_equivalent_in (tenv : typing_env)
    (bindings : list static_binding) (body body' : expr) :
  expr_equivalent_in tenv body body' ->
  expr_equivalent_in tenv (Let_static bindings body)
    (Let_static bindings body').
Proof.
  intros Hbody vars conts statics Hsat.
  destruct (eval_static_bindings vars bindings statics) as [extended | ]
    eqn:Hbindings.
  - eapply equivalent_step;
      [ simpl; rewrite Hbindings; reflexivity
      | simpl; rewrite Hbindings; reflexivity | apply Hbody, Hsat ].
  - apply (equivalent_of_run 1 1). simpl. rewrite Hbindings. reflexivity.
Qed.

(* A handler may be replaced by one equivalent to it under what is known
   where it is defined, less what mentions its parameters. *)
Lemma let_cont_handler_equivalent_in (tenv : typing_env) (k : continuation)
    (params : list variable) (handler handler' body : expr) :
  expr_equivalent_in (drop_vars params tenv) handler handler' ->
  expr_equivalent_in tenv
    (Let_cont_non_recursive k (Handler params handler) body)
    (Let_cont_non_recursive k (Handler params handler') body).
Proof.
  intros Hhandler vars conts statics Hsat.
  assert (Hruns :
    ∀ (vs : list value) (handler_vars : env),
      bind_params params vs vars = Some handler_vars ->
      env_satisfies (drop_vars params tenv) handler_vars).
  { intros vs handler_vars Hbind.
    apply (env_satisfies_bind_params _ params vs vars handler_vars);
      [ | intros param Hin; apply drop_vars_fresh, Hin | exact Hbind ].
    exact (env_satisfies_incl tenv _ vars (drop_vars_incl params tenv) Hsat). }
  apply refines_antisymmetric; apply let_cont_handler_refines_at;
    intros vs handler_vars conts' statics' Hbind; apply equivalent_refines;
    [ | apply equivalent_sym ];
    apply Hhandler, (Hruns vs handler_vars Hbind).
Qed.

Lemma expr_equivalent_in_trans (tenv : typing_env) (e e' e'' : expr) :
  expr_equivalent_in tenv e e' -> expr_equivalent_in tenv e' e'' ->
  expr_equivalent_in tenv e e''.
Proof.
  intros H H' vars conts statics Hsat.
  exact (equivalent_trans _ _ _ (H vars conts statics Hsat)
    (H' vars conts statics Hsat)).
Qed.

(* ======================================================================== *)
(* Following aliases                                                        *)
(* ======================================================================== *)

(* At each node: the head with its aliases followed is equivalent, by
   evaluating the same; then the parts under binders, by the induction. *)
Fixpoint follow_aliases_equivalent_in (e : expr) :
  ∀ tenv : typing_env, expr_equivalent_in tenv e (follow_aliases tenv e)
with follow_aliases_in_handler_equivalent_in (h : continuation_handler) :
  ∀ (tenv : typing_env) (k : continuation) (body : expr),
    expr_equivalent_in tenv (Let_cont_non_recursive k h body)
      (Let_cont_non_recursive k (follow_aliases_in_handler tenv h) body).
Proof.
  - destruct e
      as [ x d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros tenv; simpl.
    + (* Let *)
      apply (expr_equivalent_in_trans tenv _
        (Let x (canonical_named tenv d) body)).
      * intros vars conts statics Hsat. apply (equivalent_of_run 1 1). simpl.
        rewrite (canonical_named_sound tenv vars statics d Hsat). reflexivity.
      * apply let_equivalent_in, follow_aliases_equivalent_in.
    + (* Let_static *)
      apply (expr_equivalent_in_trans tenv _
        (Let_static (map (canonical_static_binding tenv) bindings) body)).
      * intros vars conts statics Hsat. apply (equivalent_of_run 1 1). simpl.
        rewrite (canonical_static_bindings_sound tenv vars bindings Hsat).
        reflexivity.
      * apply let_static_equivalent_in, follow_aliases_equivalent_in.
    + (* Let_cont_non_recursive *)
      apply (expr_equivalent_in_trans tenv _
        (Let_cont_non_recursive k (follow_aliases_in_handler tenv h) body));
        [ apply follow_aliases_in_handler_equivalent_in | ].
      intros vars conts statics Hsat.
      eapply equivalent_step; [ reflexivity | reflexivity | ].
      apply (follow_aliases_equivalent_in body tenv), Hsat.
    + (* Let_cont_recursive *)
      intros vars conts statics Hsat.
      eapply equivalent_step; [ reflexivity | reflexivity | ].
      apply (follow_aliases_equivalent_in body tenv), Hsat.
    + (* Apply *)
      intros vars conts statics Hsat. apply (equivalent_of_run 1 1). simpl.
      rewrite (canonical_simple_sound tenv vars (ap_callee ap) Hsat),
        (canonical_simples_sound tenv vars (ap_args ap) Hsat).
      reflexivity.
    + (* Apply_cont *)
      intros vars conts statics Hsat.
      apply canonical_apply_cont_equivalent, Hsat.
    + (* Switch *)
      intros vars conts statics Hsat.
      destruct (eval_simple vars scrutinee) as [v | ] eqn:Hscrutinee;
        [ destruct (naked_immediate_of_value v) as [i | ] eqn:Himmediate;
          [ destruct (find_arm i arms) as [ac | ] eqn:Hfind | ]
        | ].
      * eapply equivalent_step;
          [ simpl; rewrite Hscrutinee, Himmediate, Hfind; reflexivity
          | simpl;
            rewrite (canonical_simple_sound tenv vars scrutinee Hsat),
              Hscrutinee, Himmediate, find_arm_canonical, Hfind;
            reflexivity
          | ].
        apply canonical_apply_cont_equivalent, Hsat.
      * apply (equivalent_of_run 1 1). simpl.
        rewrite (canonical_simple_sound tenv vars scrutinee Hsat),
          Hscrutinee, Himmediate, find_arm_canonical, Hfind.
        reflexivity.
      * apply (equivalent_of_run 1 1). simpl.
        rewrite (canonical_simple_sound tenv vars scrutinee Hsat),
          Hscrutinee, Himmediate.
        reflexivity.
      * apply (equivalent_of_run 1 1). simpl.
        rewrite (canonical_simple_sound tenv vars scrutinee Hsat),
          Hscrutinee.
        reflexivity.
    + (* Invalid *)
      intros vars conts statics Hsat. apply equivalent_refl.
  - destruct h as [params handler]. intros tenv k body. simpl.
    apply let_cont_handler_equivalent_in, follow_aliases_equivalent_in.
Qed.

Theorem follow_aliases_equivalent : follow_aliases_equivalent_statement.
Proof.
  intros e vars conts statics.
  apply (follow_aliases_equivalent_in e []). intros x t [].
Qed.
