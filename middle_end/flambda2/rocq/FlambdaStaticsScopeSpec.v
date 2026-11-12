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
   applies keep scope, and so does a rewrite of parameters that it
   applies once the continuations are placed.

   This file is to be reviewed: the statements.

   A rewrite keeps scope (FlambdaValidatorEquivarianceSpec.keeps_scope)
   if, on a term whose code is closed, the code of its result is closed
   and every variable or continuation that is free in the result is
   free in the term. Symbols and code ids are not counted: a rewrite
   that keeps scope may mention or bind one that the term does not. The
   check of the validation (FlambdaValidateSpec.validate_unit) applies
   rewrites to the term before that are not rewrites of a round: it
   removes static bindings, it lifts, it uses what the unit binds its
   symbols to and what is known of the static closures in sight, it
   removes value slots, and it moves the bindings of code up; and
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
     FlambdaLiftFromCodeSpec.lift_from_code puts a symbol in the place
     of a defining expression that has no variable, in code, and binds
     the symbol beside the code to a constant that has none
     ([lift_from_code_keeps_scope_statement]).
     FlambdaLiftFromArmsSpec.lift_to_head does the same outside code,
     and binds the symbols in a group around the unit
     ([lift_to_head_keeps_scope_statement]).
     FlambdaLiftAroundSpec.lift_around puts a symbol in the place of a
     defining expression, and a group of static bindings before a
     [Let_cont]. A group that the guess puts may mention variables,
     so this one needs a test: where FlambdaLiftAroundSpec.around_ok
     passes, a group put binds symbols only and mentions only
     variables that are free in the [Let_cont] that it is put before;
     where it does not pass the term is left as it is
     ([lift_around_keeps_scope_statement]).
     The lifting as the check applies it, FlambdaValidateSpec.with_lifting,
     is the fourth of these, then the third, then the first two, then
     the last, each made or not ([with_lifting_keeps_scope_statement]).
     None of the statements but that of [lift_around] needs the tests
     that FlambdaLiftSpec.lift_unit,
     FlambdaLiftFromCodeSpec.lift_from_code_unit,
     FlambdaLiftFromArmsSpec.lift_to_head_unit and
     FlambdaLiftAroundSpec.lift_around_unit make.
   - FlambdaKnownSymbolsSpec.fold_known puts a constant or a symbol in
     the place of a defining expression, and makes an indirect call a
     direct call of the same callee with the same arguments, whatever is
     known of constants and of sets
     ([fold_known_keeps_scope_statement]); [with_known] is that, or the
     term as it is ([with_known_keeps_scope_statement]).
   - FlambdaKnownSlotsSpec.read_slots puts a symbol or a constant in
     the place of the projection of a value slot, where what it is
     given lists symbols and constants only
     ([read_slots_keeps_scope_statement]); [read_known_slots] is that,
     with what it has checked, or the term as it is
     ([read_known_slots_keeps_scope_statement]).
   - FlambdaStubCallsSpec.demote_stub_calls makes, in the code of the
     stubs of a unit, a direct call an indirect call of the same
     callee with the same arguments
     ([demote_stub_calls_keeps_scope_statement]).
   - FlambdaUnusedSlotsSpec.drop_slots removes value slots from static
     sets of closures, and with them the variables they hold
     ([drop_slots_keeps_scope_statement]); [without_slots] is that
     followed by the removal of the [Let]s that nothing uses, in the
     term and in its code, or the term as it is
     ([without_slots_keeps_scope_statement]).
   - FlambdaKnownClosuresSpec.use_known_closures puts, for the
     projection of a value slot of a static closure in sight, what the
     slot holds, and makes a call of such a closure direct. A variable
     that a slot of a static closure holds is free in the binding of
     the closure, which is in the term
     ([use_known_closures_keeps_scope_statement]).
   - FlambdaFloatCodeSpec.float_code moves the bindings of code out of
     [Let]s and continuations. Closed code has no free variable and no
     free continuation, so none leaves the scope of its binder
     ([float_code_keeps_scope_statement]).
   - FlambdaGroupsUpSpec.groups_up moves a group of static bindings
     from the head of the body of a [Let_cont] to before it. A
     [Let_cont] binds no variable in its body, and a group whose code
     is closed mentions no continuation
     ([groups_up_keeps_scope_statement]).
   - FlambdaHoistStaticsSpec.hoist_statics moves to the head of the
     unit the bindings of code, and the bindings of symbols whose
     constant has a value in the empty environment, which has no
     variable; [with_statics_first] is that with the groups tidied, or
     the term as it is ([with_statics_first_keeps_scope_statement]).
     The statement does not need the tests that [hoist_statics] makes.
   - FlambdaUnaliasParamsSpec.unalias_params, of the rounds that
     follow the placing of the continuations
     (FlambdaValidateSpec.tidied_before), takes away a parameter of a
     continuation that every
     application gives one variable, and has the handler begin with a
     [Let] of the parameter to that variable. The variable is free in
     the body of the [Let_cont], where an application gives it and no
     binder on the way binds it; the applications lose an argument
     and mention no continuation more
     ([unalias_params_keeps_scope_statement]).

   Nothing is asked of a term but that its code is closed, which
   [keeps_scope] itself asks, and nothing of what a rewrite is given.

   Nothing is trusted here. The proofs are in
   FlambdaStaticsScopeProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaBindersSpec FlambdaUnusedStaticsSpec
  FlambdaStaticsOrderSpec FlambdaMyClosureSpec FlambdaLiftSpec
  FlambdaLiftFromCodeSpec FlambdaLiftFromArmsSpec FlambdaLiftAroundSpec
  FlambdaUnusedSlotsSpec
  FlambdaKnownSymbolsSpec FlambdaKnownClosuresSpec FlambdaFloatCodeSpec
  FlambdaGroupsUpSpec FlambdaKnownSlotsSpec FlambdaStubCallsSpec
  FlambdaUnaliasParamsSpec
  FlambdaValidateSpec
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

(* The [Let]s given lifted out of the code given, whatever they are. *)
Definition lift_from_code_keeps_scope_statement : Prop :=
  ∀ (K : lets_in_code) (lets : list (path * lift_to)) (at_path : path),
    keeps_scope (lift_from_code K lets at_path).

(* The [Let]s given lifted to the head of the unit, whatever they
   are. *)
Definition lift_to_head_keeps_scope_statement : Prop :=
  ∀ lets : list (path * lift_to), keeps_scope (lift_to_head lets).

(* The [Let]s given made aliases of the symbols given and the groups
   given put, where the check of FlambdaLiftAroundSpec.around_ok
   passes, from nothing known and at any path; the term as it is
   where it does not. *)
Definition lift_around_keeps_scope_statement : Prop :=
  ∀ (lets : list (path * lift_to))
    (groups : list (path * list static_binding)) (at_path : path),
    keeps_scope
      (fun e =>
         if around_ok lets groups [] at_path e
         then lift_around lets groups at_path e
         else e).

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
(* The value slots that the unit gives one symbol or constant               *)
(* ======================================================================== *)

Definition read_slots_keeps_scope_statement : Prop :=
  ∀ (known : known_slots) (syms : list symbol),
    closed_slots known = true -> keeps_scope (read_slots known syms).

Definition read_known_slots_keeps_scope_statement : Prop :=
  keeps_scope read_known_slots.

(* ======================================================================== *)
(* The direct calls of the code of a stub                                   *)
(* ======================================================================== *)

Definition demote_stub_calls_keeps_scope_statement : Prop :=
  keeps_scope demote_stub_calls.

(* ======================================================================== *)
(* The removal of value slots                                               *)
(* ======================================================================== *)

Definition drop_slots_keeps_scope_statement : Prop :=
  ∀ dropped : list value_slot, keeps_scope (drop_slots dropped).

Definition without_slots_keeps_scope_statement : Prop :=
  ∀ slots : list value_slot, keeps_scope (without_slots slots).

(* ======================================================================== *)
(* What is known of the static closures in sight                            *)
(* ======================================================================== *)

Definition use_known_closures_keeps_scope_statement : Prop :=
  keeps_scope use_known_closures.

(* ======================================================================== *)
(* The bindings of code moved up                                            *)
(* ======================================================================== *)

Definition float_code_keeps_scope_statement : Prop := keeps_scope float_code.

(* ======================================================================== *)
(* The groups moved above continuation bindings                             *)
(* ======================================================================== *)

Definition groups_up_keeps_scope_statement : Prop := keeps_scope groups_up.

(* ======================================================================== *)
(* The static bindings that need nothing bound first                        *)
(* ======================================================================== *)

Definition with_statics_first_keeps_scope_statement : Prop :=
  ∀ Ls : list lifting, keeps_scope (with_statics_first Ls).

(* ======================================================================== *)
(* A parameter that every application gives one variable                    *)
(* ======================================================================== *)

Definition unalias_params_keeps_scope_statement : Prop :=
  keeps_scope unalias_params.
