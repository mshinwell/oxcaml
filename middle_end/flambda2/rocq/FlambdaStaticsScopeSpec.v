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


(* The rewrites of static bindings that the check of the validation
   applies keep scope.

   This file is to be reviewed: the statements.

   A rewrite keeps scope (FlambdaValidatorEquivarianceSpec.keeps_scope)
   if, on a term whose code is closed, the code of its result is closed
   and every variable or continuation that is free in the result is
   free in the term. Symbols and code ids are not counted: a rewrite
   that keeps scope may mention or bind one that the term does not. The
   check of the validation (FlambdaValidateSpec.validate_unit) applies
   rewrites to the term before that are not rewrites of a round: it
   removes static bindings, it lifts, it uses what the unit binds its
   symbols to, and it removes value slots; and
   FlambdaStaticsOrderSpec.order_statics_as is for it to apply, with
   the term after as the pattern. Each keeps scope, and that is stated
   here. It is what a statement that the check answers the
   same on renamed terms needs of them, once a round of the check
   makes names (the last section of
   FlambdaValidatorEquivarianceSpec.v).

   - FlambdaUnusedStaticsSpec.erase_expr removes the bindings of the
     names given, in code and in handlers too, and adds nothing
     ([erase_expr_keeps_scope_statement]). The removal as the check
     applies it, FlambdaUnusedStaticsSpec.drop_statics, answers a term
     only where the term refers to none of the names, and the term it
     answers is that of [erase_expr]; the statement here does not need
     that test. FlambdaValidateSpec.without_statics is [drop_statics]
     and then two rewrites of a round,
     FlambdaNormaliseSpec.drop_deleted_code and [merge_statics], which
     keep scope (FlambdaKeepsScopeSpec.v): it keeps scope
     ([without_statics_keeps_scope_statement]).
   - FlambdaStaticsOrderSpec.order_statics_as puts the bindings of
     each group of static bindings in the order of another term. The
     bindings of a group are the same ones in another order, whatever
     the other term is ([order_statics_as_keeps_scope_statement]).
   - FlambdaLiftSpec.lift_expr makes of a [Let] a static binding of
     what the [Let] made and a [Let] of the symbol: the variables of
     the constant bound are those of the defining expression, and a
     symbol has none ([lift_expr_keeps_scope_statement]).
     FlambdaMyClosureSpec.bind_my_closures binds, in code, the closure
     of the code to a symbol: it adds a [Let] of the variable that the
     code binds for its closure ([bind_my_closures_keeps_scope_statement]).
     The lifting as the check applies it, FlambdaValidateSpec.with_lifting,
     is the two, or the term as it is
     ([with_lifting_keeps_scope_statement]). None of the three
     statements needs the tests that FlambdaLiftSpec.lift_unit makes.
   - FlambdaKnownSymbolsSpec.fold_known puts a constant or a symbol in
     the place of a defining expression, whatever is known of constants
     and of sets ([fold_known_keeps_scope_statement]); [with_known] is
     that, or the term as it is ([with_known_keeps_scope_statement]).
   - FlambdaUnusedSlotsSpec.drop_slots removes value slots from static
     sets of closures, and with them the variables they hold
     ([drop_slots_keeps_scope_statement]); [without_slots] is that, or
     the term as it is ([without_slots_keeps_scope_statement]).

   Nothing is asked of a term but that its code is closed, which
   [keeps_scope] itself asks, and nothing of what a rewrite is given.

   Nothing is trusted here. The proofs are in
   FlambdaStaticsScopeProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaBindersSpec FlambdaUnusedStaticsSpec
  FlambdaStaticsOrderSpec FlambdaMyClosureSpec FlambdaLiftSpec
  FlambdaUnusedSlotsSpec FlambdaKnownSymbolsSpec FlambdaValidateSpec
  FlambdaValidatorEquivarianceSpec.
Import ListNotations.

(* ======================================================================== *)
(* The removal of static bindings                                           *)
(* ======================================================================== *)

(* The bindings of the names given removed, whatever the names. *)
Definition erase_expr_keeps_scope_statement : Prop :=
  ∀ D : dropped, keeps_scope (erase_expr D).

(* The removal as the check applies it, whatever the names. *)
Definition without_statics_keeps_scope_statement : Prop :=
  ∀ unused : dropped, keeps_scope (without_statics unused).

(* ======================================================================== *)
(* The order of static bindings                                             *)
(* ======================================================================== *)

(* The bindings of each group in the order of another term, whatever
   that term. *)
Definition order_statics_as_keeps_scope_statement : Prop :=
  ∀ pattern : expr, keeps_scope (order_statics_as pattern).

(* ======================================================================== *)
(* The lifting                                                              *)
(* ======================================================================== *)

(* The [Let]s given lifted, whatever they are and wherever the term is
   said to be. *)
Definition lift_expr_keeps_scope_statement : Prop :=
  ∀ (lets : list (path * lift_to)) (at_path : path),
    keeps_scope (lift_expr lets at_path).

(* The closure of each code given bound to its symbol in the code. *)
Definition bind_my_closures_keeps_scope_statement : Prop :=
  ∀ known : list (code_id * symbol), keeps_scope (bind_my_closures known).

(* The lifting as the check applies it. *)
Definition with_lifting_keeps_scope_statement : Prop :=
  ∀ L : lifting, keeps_scope (with_lifting L).

(* ======================================================================== *)
(* What the unit binds its symbols to                                       *)
(* ======================================================================== *)

Definition fold_known_keeps_scope_statement : Prop :=
  ∀ statics sets : static_env, keeps_scope (fold_known statics sets).

Definition with_known_keeps_scope_statement : Prop := keeps_scope with_known.

(* ======================================================================== *)
(* The removal of value slots                                               *)
(* ======================================================================== *)

Definition drop_slots_keeps_scope_statement : Prop :=
  ∀ dropped : list value_slot, keeps_scope (drop_slots dropped).

Definition without_slots_keeps_scope_statement : Prop :=
  ∀ slots : list value_slot, keeps_scope (without_slots slots).
