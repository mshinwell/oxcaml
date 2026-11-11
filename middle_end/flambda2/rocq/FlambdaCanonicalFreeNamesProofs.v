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

(* Proofs of the statements of FlambdaCanonicalFreeNamesSpec.v. This file
   needs no review.

   Each statement is the one it restates, with the premise about names
   turned by [var_free_among] and [cont_free_among]: what is free by the
   relation is among the list, so a renaming that fixes the list fixes
   it, and a name that is not among the list is not free. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaBindersSpec FlambdaSemanticsSpec
  FlambdaNominalSpec FlambdaNominalProofs FlambdaAlphaSpec
  FlambdaAlphaProofs FlambdaFreeNamesSpec FlambdaFreeNamesProofs
  FlambdaNameAbstractionSpec FlambdaCanonicalFreeNamesSpec.
Import ListNotations.

(* ======================================================================== *)
(* What a renaming that fixes a list fixes                                  *)
(* ======================================================================== *)

Lemma fixes_variable (r : renaming) (names : list variable) (x : variable) :
  fixes (variable_permutation r) names ->
  among x names = true -> rename_variable r x = x.
Proof. intros Hfixes Hx. exact (Hfixes x Hx). Qed.

Lemma fixes_continuation (r : renaming) (names : list continuation)
    (k : continuation) :
  fixes (continuation_permutation r) names ->
  among k names = true -> rename_continuation r k = k.
Proof. intros Hfixes Hk. exact (Hfixes k Hk). Qed.

Lemma among_without_one (name bound : positive) (names : list positive) :
  name <> bound -> among name names = true ->
  among name (without [bound] names) = true.
Proof.
  intros Hne Hname. rewrite among_without, Hname.
  apply not_among_singleton in Hne. rewrite Hne. reflexivity.
Qed.

Lemma among_without_all (name : positive) (bound names : list positive) :
  name ∉ bound -> among name names = true ->
  among name (without bound names) = true.
Proof.
  intros Hnotin Hname. rewrite among_without, Hname.
  apply not_among_in in Hnotin. rewrite Hnotin. reflexivity.
Qed.

(* The premises of the older statements, from those of these. *)
Section Premises.

Variable r : renaming.

Lemma variables_fixed (e : expr) :
  fixes (variable_permutation r) (free_variables_of_expr e) ->
  ∀ y : variable, var_free_in_expr y e -> rename_variable r y = y.
Proof.
  intros Hfixes y Hy. apply (fixes_variable r _ y Hfixes), var_free_among, Hy.
Qed.

Lemma continuations_fixed (e : expr) :
  fixes (continuation_permutation r) (free_continuations_of_expr e) ->
  ∀ k : continuation, cont_free_in_expr k e -> rename_continuation r k = k.
Proof.
  intros Hfixes k Hk.
  apply (fixes_continuation r _ k Hfixes), cont_free_among, Hk.
Qed.

Lemma variables_fixed_but_one (x : variable) (e : expr) :
  fixes (variable_permutation r) (without [x] (free_variables_of_expr e)) ->
  ∀ y : variable,
    y <> x -> var_free_in_expr y e -> rename_variable r y = y.
Proof.
  intros Hfixes y Hne Hy. apply (fixes_variable r _ y Hfixes).
  apply among_without_one; [ exact Hne | apply var_free_among, Hy ].
Qed.

Lemma continuations_fixed_but_one (k : continuation) (e : expr) :
  fixes (continuation_permutation r)
    (without [k] (free_continuations_of_expr e)) ->
  ∀ k' : continuation,
    k' <> k -> cont_free_in_expr k' e -> rename_continuation r k' = k'.
Proof.
  intros Hfixes k' Hne Hk'. apply (fixes_continuation r _ k' Hfixes).
  apply among_without_one; [ exact Hne | apply cont_free_among, Hk' ].
Qed.

Lemma variables_fixed_but_params (params : list variable) (e : expr) :
  fixes (variable_permutation r)
    (without params (free_variables_of_expr e)) ->
  ∀ y : variable,
    y ∉ params -> var_free_in_expr y e -> rename_variable r y = y.
Proof.
  intros Hfixes y Hnotin Hy. apply (fixes_variable r _ y Hfixes).
  apply among_without_all; [ exact Hnotin | apply var_free_among, Hy ].
Qed.

End Premises.

(* ======================================================================== *)
(* The statements of FlambdaNominalSpec.v                                   *)
(* ======================================================================== *)

Theorem rename_let_canonical : rename_let_canonical_statement.
Proof.
  intros r x kind d body Hclosed [Hvars Hconts].
  apply rename_let;
    [ exact Hclosed | apply variables_fixed_but_one, Hvars
    | apply continuations_fixed, Hconts ].
Qed.

Theorem freshen_let_canonical : freshen_let_canonical_statement.
Proof.
  intros x fresh kind d body Hclosed Hfresh.
  apply freshen_let; [ exact Hclosed | ].
  intros Hfree. apply var_free_among in Hfree. congruence.
Qed.

Theorem rename_let_cont_canonical : rename_let_cont_canonical_statement.
Proof.
  intros r k h body Hclosed [Hvars Hconts].
  apply rename_let_cont;
    [ exact Hclosed | apply variables_fixed, Hvars
    | apply continuations_fixed_but_one, Hconts ].
Qed.

Theorem rename_handler_params_canonical :
  rename_handler_params_canonical_statement.
Proof.
  intros r k params metadata handler body Hclosed [Hvars Hconts].
  apply rename_handler_params;
    [ exact Hclosed | apply variables_fixed_but_params, Hvars
    | apply continuations_fixed, Hconts ].
Qed.

Theorem rename_recursive_handler_params_canonical :
  rename_recursive_handler_params_canonical_statement.
Proof.
  intros r before k params metadata handler after body Hclosed
    [Hvars Hconts].
  apply rename_recursive_handler_params;
    [ exact Hclosed | apply variables_fixed_but_params, Hvars
    | apply continuations_fixed, Hconts ].
Qed.

Theorem rename_let_cont_recursive_canonical :
  rename_let_cont_recursive_canonical_statement.
Proof.
  intros r handlers body Hclosed [Hvars Hconts].
  apply rename_let_cont_recursive;
    [ exact Hclosed | apply variables_fixed, Hvars
    | apply continuations_fixed, Hconts ].
Qed.

Theorem unused_let_canonical : unused_let_canonical_statement.
Proof.
  intros x kind d body Hunused. apply unused_let.
  intros Hfree. apply var_free_among in Hfree. congruence.
Qed.

Theorem unused_let_cont_canonical : unused_let_cont_canonical_statement.
Proof.
  intros k h body Hunused. apply unused_let_cont.
  intros Hfree. apply cont_free_among in Hfree. congruence.
Qed.

Theorem unused_let_cont_recursive_canonical :
  unused_let_cont_recursive_canonical_statement.
Proof.
  intros handlers body Hstatics Hunbound.
  apply unused_let_cont_recursive; [ exact Hstatics | ].
  intros k Hk. apply Hunbound, cont_free_among, Hk.
Qed.

(* ======================================================================== *)
(* The rules of alpha-equivalence                                           *)
(* ======================================================================== *)

Theorem alpha_rename_canonical : alpha_rename_canonical_statement.
Proof.
  intros r e Hclosed [Hvars Hconts].
  apply Alpha_rename;
    [ exact Hclosed | apply variables_fixed, Hvars
    | apply continuations_fixed, Hconts ].
Qed.

Theorem alpha_let_canonical : alpha_let_canonical_statement.
Proof.
  intros r x kind d body Hclosed [Hvars Hconts].
  apply Alpha_let;
    [ exact Hclosed | apply variables_fixed_but_one, Hvars
    | apply continuations_fixed, Hconts ].
Qed.

Theorem alpha_let_cont_canonical : alpha_let_cont_canonical_statement.
Proof.
  intros r k h body Hclosed [Hvars Hconts].
  apply Alpha_let_cont;
    [ exact Hclosed | apply variables_fixed, Hvars
    | apply continuations_fixed_but_one, Hconts ].
Qed.

Theorem alpha_handler_canonical : alpha_handler_canonical_statement.
Proof.
  intros r k params metadata handler body Hclosed [Hvars Hconts].
  apply Alpha_handler;
    [ exact Hclosed | apply variables_fixed_but_params, Hvars
    | apply continuations_fixed, Hconts ].
Qed.

Theorem alpha_recursive_handler_canonical :
  alpha_recursive_handler_canonical_statement.
Proof.
  intros r before k params metadata handler after body Hclosed
    [Hvars Hconts].
  apply Alpha_recursive_handler;
    [ exact Hclosed | apply variables_fixed_but_params, Hvars
    | apply continuations_fixed, Hconts ].
Qed.

Theorem rename_variables_equivalent_canonical :
  rename_variables_equivalent_canonical_statement.
Proof.
  intros r e vars conts statics Hclosed Hconts.
  apply rename_variables_equivalent;
    [ exact Hclosed | apply continuations_fixed, Hconts ].
Qed.
