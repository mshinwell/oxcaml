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


(* The two rewrites of FlambdaUnboxInScopeSpec.v commute with renaming
   and keep scope, where the rewrite that they are given does.

   This file is to be reviewed: [equivariant_where_known],
   [keeps_scope_where_known] and the statements.

   FlambdaUnboxInScopeSpec.rewrite_code_in_scope and
   FlambdaUnboxInScopeSpec.rewrite_rec_handlers_in_scope give a rewrite
   what is known of the symbols in scope, which mentions no variable
   (FlambdaUnboxInScopeSpec.symbols_only). So what they give it is not
   changed by a renaming: no renaming of FlambdaNominalSpec.v moves a
   symbol, and what is known of the symbols of a group of static
   bindings is the same of the group renamed, a field that holds a
   variable being forgotten either way
   ([symbols_under_statics_renamed_statement]). The two compare no
   name and bind none. So:
   - if the rewrite given commutes with renaming whatever it is given
     of symbols alone ([equivariant_where_known]), so do the two;
   - if it keeps scope
     (FlambdaValidatorEquivarianceSpec.keeps_scope) whatever it is
     given of symbols alone ([keeps_scope_where_known]), so do the two.

   The unboxing of the parameters of continuations is such a rewrite.
   Given what is known it commutes with renaming when what is known is
   renamed with the term
   ([unbox_variants_knowing_equivariant_statement] of
   FlambdaUnboxVariantsRenameSpec.v),
   and what is known of symbols alone is unchanged by a renaming
   ([symbols_only_renamed_statement]); and it keeps scope
   ([unbox_variants_knowing_symbols_keeps_scope_statement]): what an
   application is given is a constant, a symbol, or something in scope
   in the term.

   With these and the statements of FlambdaUnboxInScopeSpec.v the two
   are in a round of the validation
   (FlambdaValidateSpec.normalise_params_round): the validation is
   still sound, answers the same under a renaming and keeps scope with
   them.

   The proofs are in FlambdaUnboxInScopeRenameProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaNominalSpec
  FlambdaValidatorEquivarianceSpec FlambdaUnboxParamsSpec
  FlambdaUnboxParamsRenameSpec FlambdaUnboxVariantsSpec
  FlambdaUnboxInScopeSpec.
Import ListNotations.

(* A rewrite that takes what is known of symbols commutes with
   renaming, and keeps scope, whatever it is given of symbols alone. *)
Definition equivariant_where_known (f : facts -> expr -> expr) : Prop :=
  ∀ known : facts, symbols_only known -> rewrite_equivariant (f known).

Definition keeps_scope_where_known (f : facts -> expr -> expr) : Prop :=
  ∀ known : facts, symbols_only known -> keeps_scope (f known).

(* What is known of symbols alone is not changed by a renaming. *)
Definition symbols_only_renamed_statement : Prop :=
  ∀ (r : renaming) (known : facts),
    symbols_only known -> rename_facts r known = known.

(* What is known of the symbols of a group of static bindings is that of
   the group renamed. *)
Definition symbols_under_statics_renamed_statement : Prop :=
  ∀ (r : renaming) (known : facts) (bindings : list static_binding),
    symbols_under_statics known (map (rename_static_binding r) bindings)
    = symbols_under_statics known bindings.

Definition rewrite_code_in_scope_equivariant_statement : Prop :=
  ∀ f : facts -> expr -> expr,
    equivariant_where_known f ->
    equivariant_where_known (rewrite_code_in_scope f).

Definition rewrite_rec_handlers_in_scope_equivariant_statement : Prop :=
  ∀ f : facts -> expr -> expr,
    equivariant_where_known f ->
    equivariant_where_known (rewrite_rec_handlers_in_scope f).

Definition rewrite_code_in_scope_keeps_scope_statement : Prop :=
  ∀ f : facts -> expr -> expr,
    keeps_scope_where_known f ->
    keeps_scope_where_known (rewrite_code_in_scope f).

Definition rewrite_rec_handlers_in_scope_keeps_scope_statement : Prop :=
  ∀ f : facts -> expr -> expr,
    keeps_scope_where_known f ->
    keeps_scope_where_known (rewrite_rec_handlers_in_scope f).

Definition unbox_variants_knowing_symbols_keeps_scope_statement : Prop :=
  keeps_scope_where_known unbox_variants_knowing.
