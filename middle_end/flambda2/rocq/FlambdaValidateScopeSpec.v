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

(* The rounds of the validation keep scope.

   This file is to be reviewed: the statements.

   FlambdaKeepsScopeSpec.v says what it is for a rewrite to keep scope
   (FlambdaValidatorEquivarianceSpec.keeps_scope) and that each rewrite
   of a round does; FlambdaLoopsScopeSpec.v says it of the rewrites for
   loops. This file says it of what FlambdaValidateSpec.v makes of
   them for the term before: a round for an expression
   ([normalise_expr_before]) and a round for the body of code
   ([normalise_code_before]), which is the first taken into the
   handlers of the recursive continuations.

   The last section is about FlambdaGuardScopeSpec.guard_scope, which
   of a term whose code is closed gives what a rewrite gives only where
   that passes the test of keeping scope, and of a term whose code is
   not closed gives what the rewrite gives: it keeps scope whatever the
   rewrite; it is the rewrite where the rewrite keeps scope; and it
   commutes with renaming where the rewrite does. They are here and not
   beside the definition because [keeps_scope] and [rewrite_equivariant]
   are defined after the validation, which is to run [guard_scope].

   What is not here yet: the inlining of the calls of known code, and
   a round of the term as a whole. Their statements are to come with
   the change that makes the validation give every binder a name of its
   own, which changes both.

   Closed code is all that is asked of a term, as [keeps_scope] asks
   it.

   Nothing is trusted here. The proofs are in
   FlambdaValidateScopeProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaNominalSpec FlambdaGuardScopeSpec FlambdaValidateSpec
  FlambdaValidatorEquivarianceSpec.
Import ListNotations.

Definition normalise_expr_before_keeps_scope_statement : Prop :=
  keeps_scope normalise_expr_before.

Definition normalise_code_before_keeps_scope_statement : Prop :=
  keeps_scope normalise_code_before.

(* ======================================================================== *)
(* A rewrite made to keep scope by a test                                   *)
(* ======================================================================== *)

(* FlambdaGuardScopeSpec.guard_scope keeps scope, whatever the rewrite
   it is given. *)
Definition guard_scope_keeps_scope_statement : Prop :=
  ∀ f : expr -> expr, keeps_scope (guard_scope f).

(* It is the rewrite, where the rewrite keeps scope: the test then
   changes no result. *)
Definition guard_scope_unchanged_statement : Prop :=
  ∀ f : expr -> expr,
    keeps_scope f -> ∀ e : expr, guard_scope f e = f e.

(* It commutes with renaming where the rewrite does: the test does not
   tell a renamed pair of terms from the pair. *)
Definition guard_scope_equivariant_statement : Prop :=
  ∀ f : expr -> expr,
    rewrite_equivariant f -> rewrite_equivariant (guard_scope f).
