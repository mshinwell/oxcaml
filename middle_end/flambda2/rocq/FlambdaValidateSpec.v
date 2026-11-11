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

(* Validating what Simplify did to a compilation unit.

   This file is to be reviewed: [validate_unit] and the two statements.
   It is extracted and run by the test of
   middle_end/flambda2/tests/semantics/ on the term of a unit before
   Simplify and the term after.

   [validate_unit] is the whole check, so that what it accepts is correct
   by one theorem and not by how a tool puts the proved pieces together.
   It normalises the term before by rewrites that refine it
   ([normalise_before]) and the term after by rewrites that are
   equivalences ([normalise_after]), each gone round a number of times as
   they enable one another, and compares the results up to bound names
   (FlambdaCompareSpec.expr_eqb). Failing that, it removes from the term
   before the static bindings of the names given
   (FlambdaUnusedStaticsSpec.drop_statics) and compares again. Failing
   that too, it starts again from the term before as it was given: it
   makes the [Let]s given static bindings of the symbols given
   (FlambdaLiftSpec.lift_unit, which says what is lifted and under which
   conditions), normalises the result, each round followed by
   replacing the primitives and the projections applied to symbols that
   the unit binds to constants by their values
   (FlambdaKnownSymbolsSpec.fold_known_unit; [normalise_lifted]),
   removes from the static sets of closures the value slots given, if
   nothing projects them (FlambdaUnusedSlotsSpec.drop_unused_slots),
   removes the static bindings of the names given, and compares. The
   lifting comes first because the normalisation unfolds calls: a [Let]
   in the body of a function would be many [Let]s afterwards, and a
   closure that nothing uses would be gone. What is known of the
   symbols is used in every round because the two enable one another: a
   round puts a symbol where a variable stood for it, the folding puts
   what a projection of the symbol gives in place of the projection,
   and the next round follows that to where it is read in turn. The
   value slots come last because it is the normalisation that removes
   the projections which the code of a function makes and no longer
   needs.

   What it accepts is correct for the unit run as a compilation unit is
   run, on its own from empty environments
   ([validate_unit_sound_statement]): if the term before exits, the term
   after exits alike, and if the term after terminates then it does as
   the term before does, or the term before is undefined. Where no static
   binding had to be removed and nothing lifted, this holds under all
   environments too ([validate_unit_sound_everywhere_statement]). A unit
   in which something was lifted exits with constants and symbols only:
   that is one of the conditions.

   The number of rounds, the names and the value slots to remove and
   what to lift are for the caller to choose; none is trusted. Fewer
   rounds, the wrong names, the wrong value slots or the wrong [Let]s
   make the check fail, not accept what it should not. The names to
   remove are those of the term that is compared: of the term lifted,
   where something is lifted.

   The proofs are in FlambdaValidateProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaCompareSpec FlambdaNormaliseSpec FlambdaBlockLoadSpec
  FlambdaUnboxSpec FlambdaUnusedContsSpec FlambdaUnusedStaticsSpec
  FlambdaLiftSpec FlambdaUnusedSlotsSpec FlambdaKnownSymbolsSpec.
From OxCamlFlambda2Types Require Import FlambdaAliasesSpec.
Import ListNotations.

(* ======================================================================== *)
(* The normalisations                                                       *)
(* ======================================================================== *)

Fixpoint iterate (rounds : nat) (f : expr -> expr) (e : expr) : expr :=
  match rounds with
  | O => e
  | S rounds => iterate rounds f (f e)
  end.

(* One round for the body of code in the term before: the rewrites that
   need to know nothing of where they are applied. *)
Definition normalise_code_before (body : expr) : expr :=
  remove_unused_defined_lets []
    (remove_unused_lets
       (fold_constants
          (follow_aliases []
             (unbox_known_numbers
                (load_known_blocks
                   (thread_switches
                      (inline_tail_conts
                         (remove_unused_conts
                            (collapse_switches (fold_constants body)))))))))).

(* One round for the term before. Every rewrite refines. *)
Definition normalise_before_round (e : expr) : expr :=
  rewrite_code normalise_code_before
    (merge_statics
       (drop_deleted_code
          (remove_unused_defined_lets []
             (remove_unused_lets
                (fold_constants
                   (follow_aliases []
                      (unbox_known_numbers
                         (load_known_blocks
                            (thread_switches
                               (inline_tail_conts
                                  (remove_unused_conts
                                     (collapse_switches
                                        (fold_constants
                                           (inline_calls [] e)))))))))))))).

Definition normalise_before (rounds : nat) (e : expr) : expr :=
  iterate rounds normalise_before_round e.

(* The same for the term after. Every rewrite is an equivalence. *)
Definition normalise_code_after (body : expr) : expr :=
  remove_unused_defined_lets [] (fold_constants (follow_aliases [] body)).

Definition normalise_after_round (e : expr) : expr :=
  rewrite_code normalise_code_after
    (merge_statics
       (drop_deleted_code
          (remove_unused_defined_lets []
             (fold_constants
                (inline_known_calls [] [] (follow_aliases [] e)))))).

Definition normalise_after (rounds : nat) (e : expr) : expr :=
  iterate rounds normalise_after_round e.

(* The static bindings of the names given removed, if nothing refers to
   them, and the groups of bindings tidied again. *)
Definition without_statics (D : dropped) (e : expr) : expr :=
  match drop_statics D e with
  | Some e' => merge_statics (drop_deleted_code e')
  | None => e
  end.

(* The [Let]s given made static bindings of the symbols given, if the
   conditions of FlambdaLiftSpec.lift_unit hold. *)
Definition with_lifting (L : lifting) (e : expr) : expr :=
  match lift_unit L e with
  | Some e' => e'
  | None => e
  end.

(* What the unit binds its symbols to used wherever they are, if it
   binds each of them to one constant. *)
Definition with_known (e : expr) : expr :=
  match fold_known_unit e with
  | Some e' => e'
  | None => e
  end.

(* The normalisation of a term in which something was lifted: each round
   of that of the term before is followed by the use of what the unit
   binds its symbols to. *)
Definition normalise_lifted_round (e : expr) : expr :=
  with_known (normalise_before_round e).

Definition normalise_lifted (rounds : nat) (e : expr) : expr :=
  iterate rounds normalise_lifted_round e.

(* The value slots given removed from the static sets of closures, if
   nothing projects them. *)
Definition without_slots (slots : list value_slot) (e : expr) : expr :=
  match drop_unused_slots slots e with
  | Some e' => e'
  | None => e
  end.

(* ======================================================================== *)
(* The check                                                                *)
(* ======================================================================== *)

(* How a pair of terms was found to be correct, if it was. *)
Inductive validation : Type :=
  | Same_up_to_bound_names
  | Same_once_normalised
  | Same_once_unused_statics_removed
  | Same_once_lifted
  | Not_validated.

Definition validate_unit (rounds : nat) (unused : dropped)
    (slots : list value_slot) (L : lifting) (before after : expr)
    : validation :=
  if expr_eqb [] [] before after then Same_up_to_bound_names
  else
    let normalised := normalise_before rounds before in
    let after := normalise_after rounds after in
    if expr_eqb [] [] normalised after then Same_once_normalised
    else if expr_eqb [] [] (without_statics unused normalised) after
    then Same_once_unused_statics_removed
    else if
      expr_eqb [] []
        (without_statics unused
           (without_slots slots
              (normalise_lifted rounds (with_lifting L before))))
        after
    then Same_once_lifted
    else Not_validated.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

(* A unit that is validated refines the unit it came from, run on its own
   from empty environments. *)
Definition validate_unit_sound_statement : Prop :=
  ∀ (rounds : nat) (unused : dropped) (slots : list value_slot) (L : lifting)
    (before after : expr),
    validate_unit rounds unused slots L before after <> Not_validated ->
    program_refines before after.

(* It does so under all environments if no static binding was removed and
   nothing was lifted. *)
Definition validate_unit_sound_everywhere_statement : Prop :=
  ∀ (rounds : nat) (unused : dropped) (slots : list value_slot) (L : lifting)
    (before after : expr),
    validate_unit rounds unused slots L before after = Same_up_to_bound_names
    ∨ validate_unit rounds unused slots L before after
      = Same_once_normalised ->
    expr_refines before after.
