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

(* Proofs of the statements of FlambdaTypesSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaNominalSpec FlambdaNominalProofs.
From OxCamlFlambda2Types Require Import FlambdaTypesSpec.
Import ListNotations.

(* ======================================================================== *)
(* Refinement relative to a typing environment                              *)
(* ======================================================================== *)

Lemma env_satisfies_empty (vars : env) : env_satisfies [] vars.
Proof. intros x t []. Qed.

Theorem expr_refines_weaken : expr_refines_weaken_statement.
Proof. intros tenv source target Hrefines vars conts _. apply Hrefines. Qed.

Theorem expr_refines_in_empty : expr_refines_in_empty_statement.
Proof.
  intros source target. split; [ | apply expr_refines_weaken ].
  intros Hrefines vars conts. apply Hrefines, env_satisfies_empty.
Qed.

Lemma expr_equivalent_in_refines (tenv : typing_env) (e e' : expr) :
  expr_equivalent_in tenv e e' -> expr_refines_in tenv e e'.
Proof.
  intros Hequiv vars conts Hsat. apply equivalent_refines, Hequiv, Hsat.
Qed.

Lemma expr_refines_in_trans (tenv : typing_env) (e e' e'' : expr) :
  expr_refines_in tenv e e' -> expr_refines_in tenv e' e'' ->
  expr_refines_in tenv e e''.
Proof.
  intros H H' vars conts Hsat.
  exact (refines_trans _ _ _ (H vars conts Hsat) (H' vars conts Hsat)).
Qed.

Theorem bottom : bottom_statement.
Proof.
  intros tenv x e e' Hbottom vars conts Hsat.
  destruct (Hsat x Bottom Hbottom) as (v & _ & []).
Qed.

(* ======================================================================== *)
(* Following aliases                                                        *)
(* ======================================================================== *)

Lemma find_alias_in (tenv : typing_env) (x : variable) (s : simple) :
  find_alias tenv x = Some s -> (x, Equals s) ∈ tenv.
Proof.
  induction tenv as [ | [y t] tenv IH]; simpl; [ discriminate | ].
  destruct t as [ | | s'];
    try (intros Hfind; right; exact (IH Hfind)).
  destruct (Pos.eqb_spec x y) as [-> | _].
  - intros [= ->]. left. reflexivity.
  - intros Hfind. right. exact (IH Hfind).
Qed.

Theorem canonical_simple_sound : canonical_simple_sound_statement.
Proof.
  intros tenv vars s Hsat. destruct s as [x | c]; simpl; [ | reflexivity ].
  destruct (find_alias tenv x) as [alias | ] eqn:Hfind; [ | reflexivity ].
  destruct (Hsat x (Equals alias) (find_alias_in _ _ _ Hfind))
    as (v & Hlookup & Halias).
  simpl in Halias. rewrite Halias, Hlookup. reflexivity.
Qed.

Lemma canonical_simples_sound (tenv : typing_env) (vars : env)
    (args : list simple) :
  env_satisfies tenv vars ->
  eval_simples vars (map (canonical_simple tenv) args)
  = eval_simples vars args.
Proof.
  intros Hsat. induction args as [ | s args IH]; simpl; [ reflexivity | ].
  rewrite (canonical_simple_sound tenv vars s Hsat), IH. reflexivity.
Qed.

Theorem apply_cont_canonical : apply_cont_canonical_statement.
Proof.
  intros tenv k args vars conts Hsat. apply (equivalent_of_run 1 1). simpl.
  rewrite (canonical_simples_sound tenv vars args Hsat). reflexivity.
Qed.

Theorem let_simple_canonical : let_simple_canonical_statement.
Proof.
  intros tenv x s body vars conts Hsat. apply (equivalent_of_run 1 1).
  simpl. rewrite (canonical_simple_sound tenv vars s Hsat). reflexivity.
Qed.

Theorem switch_known : switch_known_statement.
Proof.
  intros tenv scrutinee i arms ac Hknown Hfind vars conts Hsat.
  apply step_equivalent. simpl.
  rewrite <- (canonical_simple_sound tenv vars scrutinee Hsat), Hknown.
  simpl. rewrite Hfind. reflexivity.
Qed.

(* ======================================================================== *)
(* Going under binders                                                      *)
(* ======================================================================== *)

(* Binding a variable that does not occur in the typing environment keeps
   it satisfied, and adds whatever type the value bound has. *)
Lemma env_satisfies_extend (tenv : typing_env) (vars : env) (x : variable)
    (v : value) (t : flambda_type) :
  env_satisfies tenv vars ->
  ~ var_in_typing_env x tenv ->
  type_satisfied ((x, v) :: vars) v t ->
  env_satisfies ((x, t) :: tenv) ((x, v) :: vars).
Proof.
  intros Hsat Hfresh Ht y t' [[= <- <-] | Hin].
  - exists v. split; [ simpl; rewrite Pos.eqb_refl; reflexivity | exact Ht ].
  - destruct (Hsat y t' Hin) as (w & Hlookup & Hw).
    assert (Hne : y <> x).
    { intros ->. apply Hfresh. exists x, t'. auto. }
    exists w. split.
    + simpl. destruct (Pos.eqb_spec y x); [ contradiction | exact Hlookup ].
    + destruct t' as [ | | [z | c]]; simpl in *; try exact Hw.
      destruct (Pos.eqb_spec z x) as [-> | _]; [ | exact Hw ].
      exfalso. apply Hfresh. exists y, (Equals (Var x)).
      split; [ exact Hin | ]. right. exists (Var x). split; reflexivity.
Qed.

Theorem let_refines_in : let_refines_in_statement.
Proof.
  intros tenv x d body body' Hfresh Hbody vars conts Hsat.
  destruct (eval_named vars d) as [v | ] eqn:Hd.
  - eapply refines_step;
      [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity | ].
    apply Hbody, env_satisfies_extend; [ exact Hsat | exact Hfresh | exact I ].
  - apply goes_wrong_refines. exists 1. simpl. rewrite Hd. reflexivity.
Qed.

Theorem let_simple_refines_in : let_simple_refines_in_statement.
Proof.
  intros tenv x s body body' Hfresh Hnotin Hbody vars conts Hsat.
  destruct (eval_simple vars s) as [v | ] eqn:Hs.
  - eapply refines_step;
      [ simpl; rewrite Hs; reflexivity | simpl; rewrite Hs; reflexivity | ].
    apply Hbody, env_satisfies_extend; [ exact Hsat | exact Hfresh | ].
    destruct s as [y | c]; simpl in *; [ | exact Hs ].
    destruct (Pos.eqb_spec y x) as [-> | _]; [ | exact Hs ].
    exfalso. apply Hnotin. reflexivity.
  - apply goes_wrong_refines. exists 1. simpl. rewrite Hs. reflexivity.
Qed.

Theorem let_cont_body_refines_in : let_cont_body_refines_in_statement.
Proof.
  intros tenv k h body body' Hbody vars conts Hsat.
  eapply refines_step; [ reflexivity | reflexivity | ].
  apply Hbody, Hsat.
Qed.

Theorem let_cont_recursive_body_refines_in :
  let_cont_recursive_body_refines_in_statement.
Proof.
  intros tenv handlers body body' Hbody vars conts Hsat.
  eapply refines_step; [ reflexivity | reflexivity | ].
  apply Hbody, Hsat.
Qed.

(* ======================================================================== *)
(* An example: propagating a constant                                       *)
(* ======================================================================== *)

(* Under the [Let] the variable is known to be the constant, so its use
   may be replaced; the [Let] is then unused. *)
Theorem let_const_apply_cont : let_const_apply_cont_statement.
Proof.
  intros x c k.
  assert (Hrewrite :
    expr_refines
      (Let x (Simple (Const c)) (Apply_cont (Apply_cont_expr k [Var x])))
      (Let x (Simple (Const c)) (Apply_cont (Apply_cont_expr k [Const c])))).
  { apply expr_refines_in_empty, let_simple_refines_in.
    - unfold var_in_typing_env. intros (y & t & [] & _).
    - simpl. intros [].
    - apply expr_equivalent_in_refines.
      pose proof (apply_cont_canonical [(x, Equals (Const c))] k [Var x])
        as Hcanonical.
      simpl in Hcanonical. rewrite Pos.eqb_refl in Hcanonical.
      exact Hcanonical. }
  assert (Hunused :
    expr_refines
      (Let x (Simple (Const c)) (Apply_cont (Apply_cont_expr k [Const c])))
      (Apply_cont (Apply_cont_expr k [Const c]))).
  { apply unused_let. simpl. unfold var_free_in_simples. intros Hfree.
    inversion Hfree as [? ? Hhead | ? ? Hrest];
      [ exact Hhead | inversion Hrest ]. }
  intros vars conts.
  exact (refines_trans _ _ _ (Hrewrite vars conts) (Hunused vars conts)).
Qed.
