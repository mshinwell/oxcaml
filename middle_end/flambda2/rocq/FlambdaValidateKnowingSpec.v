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

(* The validation asked again, with the aliases followed by a function
   that knows what symbols are bound to.

   This file is to be reviewed: the definitions and the statements.

   FlambdaValidateSpec.validate_unit normalises the term before
   Simplify and the term after in rounds, and compares them. In each
   round it follows aliases with the function of
   ../types/rocq/FlambdaAliasesSpec.v, which knows nothing of what a
   symbol is bound to. The function of
   ../types/rocq/FlambdaEnvAliasesFollowSpec.v knows the closures that
   the static bindings in sight bind symbols to: it makes an indirect
   call of such a symbol the direct call of its code, puts in the
   place of the projection of a value slot from such a symbol what the
   slot holds, and in the place of the projection of a function slot
   the symbol that the set names for that slot. Units that are not
   validated with the first are validated with the second: those in
   which Simplify has used what a symbol is bound to.

   The second does not take the place of the first in the rounds. The
   normalisation of the term before has more rewrites than that of the
   term after: it may refine, and the other must keep the behaviour.
   Where the second function makes a call direct in both terms, the
   normalisation of the term before goes on from there (it inlines the
   call, moves the continuations that are applied once to where they
   are applied, and folds), and that of the term after may stop
   earlier (it inlines a call only where the kinds of the arguments
   are sure, and leaves a continuation that is applied once where it
   is). A unit whose two terms are the same once normalised by the
   first function, both left with the same indirect calls, is then
   not validated by the second. The example
   middle_end/flambda2/tests/semantics/indirect_higher_order.fl is
   one: with its two calls of a symbol made direct and inlined in
   both terms, the term before is folded to a constant, and the term
   after is left with a continuation applied once to a constant.

   So the validation is asked twice. First as it is. Then, if it
   fails, on the two terms normalised by rounds in front of each of
   which the second function is run ([normalise_knowing]): the round
   of the term before for the term before, the round of the term
   after for the term after. With a round that refines, the term so
   normalised refines the term, and with a round that is an
   equivalence it is equivalent to the term
   ([normalise_knowing_refines_statement],
   [normalise_knowing_equivalent_statement]); so if the second of the
   two normalised terms refines the first, by whatever
   FlambdaValidateSpec.v accepts, the term after refines the term
   before ([validate_knowing_sound_statement], for a unit run on its
   own from empty environments, and
   [validate_knowing_sound_everywhere_statement], under all
   environments). Nothing of FlambdaValidateSpec.v changes, and what it
   validates today it validates still.

   The rounds are arguments. They are to be
   FlambdaValidateSpec.normalise_before_round, which refines
   (FlambdaValidateProofs.normalise_before_round_refines), and
   FlambdaValidateSpec.normalise_after_round, which is an equivalence
   (normalise_after_round_equivalent). They are not named here so
   that the statements stay as they are when those two take an
   argument more (the list of code whose calls are left, which is on
   its way). For the same reason the statements do not name
   [validate_unit]: they say what follows from what it concludes.

   Renaming and scope. The validation is stated of terms up to their
   bound names, so a function on terms that it runs is to commute with
   renaming, at least up to the names that it makes, and to keep scope
   (FlambdaValidatorEquivarianceSpec.v). [normalise_knowing] does, for
   a round that does: [normalise_knowing_keeps_scope_statement],
   [normalise_knowing_equivariant_statement] and
   [normalise_knowing_equivariant_up_to_statement]. At one round they
   are the same of [knowing_round]. They rest on the laws of the
   function that follows aliases
   (FlambdaEnvAliasesFollowSpec.rename_follow_aliases_empty_statement,
   FlambdaEnvAliasesFollowScopeSpec.v) and on those of composition and
   iteration of FlambdaValidatorEquivarianceSpec.v.

   The proofs are in FlambdaValidateKnowingProofs.v, which needs no
   review. *)

(* CR mshinwell: the function of FlambdaAliasesSpec.v stays in the
   rounds, and the validation is asked a second time with the new one
   in front of each round. The first can go, and the new one take its
   place in the rounds, when two things are done. The normalisation of
   the term after is to reach what that of the term before reaches on
   indirect_higher_order.fl once the calls are direct, or the term
   before is to keep the calls that Simplify kept (the list of code
   that is not to be inlined), so that the example is validated with
   the new function alone. And the pass for loops
   (FlambdaLoopAliasesSpec.v), which is written with the typing
   environment of FlambdaAliasesSpec.v, is to be written with what the
   new function knows. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaUnusedStaticsSpec FlambdaValidateSpec
  FlambdaValidatorEquivarianceSpec.
From OxCamlFlambda2Types Require FlambdaEnvAliasesFollowSpec.
Import ListNotations.

(* A round, after the aliases have been followed with what is known of
   the symbols. *)
Definition knowing_round (round : expr -> expr) (e : expr) : expr :=
  round
    (FlambdaEnvAliasesFollowSpec.follow_aliases
       FlambdaEnvAliasesFollowSpec.Known.empty e).

Definition normalise_knowing (round : expr -> expr) (rounds : nat)
    (e : expr) : expr :=
  iterate rounds (knowing_round round) e.

(* With a round that refines, it refines the term; with a round that is
   an equivalence, it is equivalent to the term. *)
Definition normalise_knowing_refines_statement : Prop :=
  ∀ (round : expr -> expr) (rounds : nat) (e : expr),
    (∀ e : expr, expr_refines e (round e)) ->
    expr_refines e (normalise_knowing round rounds e).

Definition normalise_knowing_equivalent_statement : Prop :=
  ∀ (round : expr -> expr) (rounds : nat) (e : expr),
    (∀ e : expr, expr_equivalent e (round e)) ->
    expr_equivalent e (normalise_knowing round rounds e).

(* If the term after, so normalised, refines the term before, so
   normalised, then the term after refines the term before: run on its
   own from empty environments, and under all environments. The premise
   is what FlambdaValidateSpec.validate_unit concludes of the two
   normalised terms where it validates them
   (FlambdaValidateSpec.validate_unit_sound_statement,
   validate_unit_sound_everywhere_statement). *)
Definition validate_knowing_sound_statement : Prop :=
  ∀ (round_before round_after : expr -> expr) (rounds : nat)
    (before after : expr),
    (∀ e : expr, expr_refines e (round_before e)) ->
    (∀ e : expr, expr_equivalent e (round_after e)) ->
    program_refines (normalise_knowing round_before rounds before)
      (normalise_knowing round_after rounds after) ->
    program_refines before after.

Definition validate_knowing_sound_everywhere_statement : Prop :=
  ∀ (round_before round_after : expr -> expr) (rounds : nat)
    (before after : expr),
    (∀ e : expr, expr_refines e (round_before e)) ->
    (∀ e : expr, expr_equivalent e (round_after e)) ->
    expr_refines (normalise_knowing round_before rounds before)
      (normalise_knowing round_after rounds after) ->
    expr_refines before after.

(* ======================================================================== *)
(* Renaming and scope                                                       *)
(* ======================================================================== *)

(* With a round that keeps scope, it keeps scope. *)
Definition normalise_knowing_keeps_scope_statement : Prop :=
  ∀ (round : expr -> expr) (rounds : nat),
    keeps_scope round -> keeps_scope (normalise_knowing round rounds).

(* With a round that commutes with renaming, it commutes with
   renaming. *)
Definition normalise_knowing_equivariant_statement : Prop :=
  ∀ (round : expr -> expr) (rounds : nat),
    rewrite_equivariant round ->
    rewrite_equivariant (normalise_knowing round rounds).

(* With a round that keeps scope and commutes with renaming up to the
   names that it makes, it commutes with renaming up to the names that
   it makes. *)
Definition normalise_knowing_equivariant_up_to_statement : Prop :=
  ∀ (round : expr -> expr) (rounds : nat),
    keeps_scope round ->
    equivariant_up_to round ->
    equivariant_up_to (normalise_knowing round rounds).
