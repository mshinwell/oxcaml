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

(* The check of regions (FlambdaRegionsCheckSpec.v) is sound: the
   regions of a term that passes it add no fault to the term, under
   two premises: the term is one that the erasure is meant for
   ([erasable]), and the symbols that the machine draws are none of
   the term or of the static environment, which holds no location
   ([region_names_fresh]: "the freshness", below).

   This file is to be reviewed: all of it. It adds nothing to the
   machine, to the check or to the property of states.
   FlambdaRegionsCheckSoundProofs.v proves its eleven statements.

   Each statement here about a run on the machine of regions is of a
   run from the first state of a term in a static environment
   ([initial_region_state]), under those two premises, which it
   writes out: of the one term where one term is run, of the term
   after where only its run on the machine of regions is spoken of,
   of both terms where an exit of the term before is.

   WHAT IT ADDS TO THE STATEMENT OF THE CHECK

   FlambdaRegionsCheckSpec.region_check_fault_statement is that the
   run of a term that passes the check, from its first state and with
   symbols to draw that are none of the term or of the static
   environment, which holds no location, stops without a step only
   where [step] has none. For the regions of such a term to add no
   fault to it (FlambdaRegionsCheckSpec.regions_add_no_fault), what
   that leaves
   is that where the run stops so, the run of the term with its
   regions dropped goes wrong too ([no_plain_step_erased_statement]).
   With it the check is sound ([region_check_sound_statement]), under
   the premises of freshness and [erasable].

   WITH THE VALIDATION OF A RUN OF SIMPLIFY

   The two statements of FlambdaRegionsCheckSpec.v about a run of
   Simplify take [regions_add_no_fault] of the term after as a
   premise. The last nine statements here are those two with the
   check in the place of that premise: each in two forms; in the
   first form again with less than [refines] for its premise, with
   the statement that [refines] gives that premise; and in the first
   form again of a unit with its imports.

   In the first form ([refined_and_checked_safe_statement],
   [refined_and_checked_exits_agree_statement]) a premise is
   [refines] of the two terms with their regions dropped, from their
   first states in the static environment: a relation of the model,
   and not a verdict of the validation. If it holds, the term before
   does not go wrong with its regions dropped, and the term after
   passes the check, then, under the freshness and [erasable] of the
   term after, the term after, with its regions, never stops without
   a step; and, under the freshness and [erasable] of both terms, an
   exit of the term before with its regions is an exit of the term
   after with its regions.

   The first form uses two things of [refines] and no more. Each is a
   premise of the first form with less than a refinement
   ([related_and_checked_safe_statement],
   [related_and_checked_exits_statement]). The first: where the term
   after, with its regions dropped, goes wrong, the term before, with
   its regions dropped, does ([erased_after_wrong_only_if_before]).
   The second, for the exits: an exit of the term before, with its
   regions dropped, is matched by an exit of the term after, with its
   regions dropped, through the same continuation, and a relation [R]
   that the statement is given holds of the values and the heaps of
   the two exits ([erased_exits_related]). With the first, the term
   after, with its regions, never stops without a step. With both, an
   exit of the term before with its regions is matched by one of the
   term after with its regions: the values of each are related by
   [value_erased_if_usable] to those of an exit of its term with its
   regions dropped, and [R] holds of those two erased exits' values
   and heaps. It is for a statement about a pass that compares the
   exits of the two terms by less than equality: a pass that removes
   what nothing reads may leave a closure at an exit with fewer value
   slots, or leave different cells in the heap. [refines]
   gives the two premises, the second with equality for [R]
   ([refines_erased_related_statement]), and the first form of a unit
   with its imports is proved so.

   The first form of a unit with its imports
   ([unit_refined_and_checked_safe_statement],
   [unit_refined_and_checked_exits_agree_statement]) is the first
   form at the static environment of the imports
   ([FlambdaImportsSpec.imports_statics]), with
   [FlambdaImportsSpec.unit_refines] of the two terms with their
   regions dropped ([erase]) in the place of [refines] of their first
   states. The two are one proposition: [erase_statics] leaves the
   static environment of the imports, which has no code, as it is.
   It is for a refinement that is proved, on the machine of
   FlambdaSemanticsSpec.v, of the two terms with their regions
   dropped. A refinement of the two terms as they are, on that
   machine, says nothing of a term before whose run comes to a
   primitive of regions: the machine gives the primitive no value,
   and the run is undefined there. regions/REFINEMENT.md says how a
   statement about a pass is brought to these two.

   The second form ([validated_and_checked_safe_statement],
   [validated_and_checked_exits_agree_statement]) is of a unit with
   its imports, run from the static environment of the imports
   ([FlambdaImportsSpec.imports_statics]), and has in the place of
   [refines] what the test tool computes. It has two terms more, the
   two that the validation is given, and three premises on them. The
   verdict that [FlambdaValidateSpec.validate_unit] gives of those
   two terms passes the model's test of it with the imports
   ([FlambdaValidateImportsSpec.verdict_holds_from], asked with the
   same arguments): it is the premise of
   FlambdaValidateImportsSpec.validate_unit_sound_verdict_imports_statement,
   which gives [FlambdaImportsSpec.unit_refines] of the two terms.
   And each of the two is, up to bound names, [erase] of the term
   with its regions ([FlambdaCompareSpec.expr_eqb], which is sound:
   [expr_eqb_sound_statement]). With these that premise of the first
   form holds: [erase_statics] leaves the static environment of the
   imports, which has no code, as it is.

   What is between the test tool and the second form is not a
   statement of the tree, and is three things. The tool reads the two
   terms of a unit; it converts each twice, once with its regions
   dropped, for the validation, and once with them kept; and it calls
   the functions of the model that the first three premises name, on
   those terms: the validation and the test of its verdict on the two
   terms made with regions dropped and, before it runs a unit on the
   machine of regions, the comparison of [erase] of each term made
   with regions kept with the term that the validation was given.
   That it does is not proved: it is in rocq/TRUST-LEDGER.md (the
   entries "The check of regions" and "What the tool reports").

   What has no statement of the second form. A verdict of the second
   asking ([validate_unit_knowing]) and one of the two validators
   that read (FlambdaValidateReadingSpec.v): for each a statement of
   the same kind gives [unit_refines] of the two terms that the
   validator is given
   ([validate_unit_knowing_sound_verdict_imports_statement],
   [validate_unit_reading_verdict_imports_statement],
   [validate_unit_knowing_reading_verdict_imports_statement]), from
   which the like of the second form would follow as it does here;
   it is not stated. The route that the tool takes for a unit that
   imports nothing, which asks no test of the verdict: the second
   form is of such a unit too, if its premise on the verdict holds,
   but nothing here derives that premise merely from an accepted
   verdict; what is proved of an accepted verdict is of the two terms
   run from the empty static environment
   (FlambdaValidateSpec.validate_unit_sound_statement). A line of the
   tool that begins "related once lifted", which is no such verdict:
   what is proved of that check (FlambdaValidateRelatedSpec.v) is
   another relation than [refines]. And the check itself, which the
   tool does not ask (FlambdaRegionsCheckSpec.v).

   [no_plain_step_erased_statement] is about the erasure and not
   about the check. It is of any term that the erasure is meant for
   ([erasable]), and it asks of the states of the run two things that
   a state of FlambdaRegionsCheckedSpec.v is proved to have:
   [reads_live], with its tests of region arguments and symbols read
   as values, and a jump to a handler
   gives every kind [Region] of the handler a parameter and an
   argument ([regions_given]).

   Without the first it is false: a partial application whose callee
   is a symbol that is gone may be evaluated, and calling it has no
   step, where the term with its regions dropped calls a closure; a
   value that is no mark, given at the place of a region, has no step
   for the kinds, where the term with its regions dropped has neither
   the parameter nor the argument.

   Without the second it is false too, and a first text of the
   statement, which asked [reads_live] alone, was. A handler with a
   parameter of the kind [Region] that is applied to no argument has
   no step on the machine of regions: it has a kind and no argument
   for it. A handler with no parameter whose kinds have a [Region],
   applied to an open region, has none either: it has no parameter
   to bind the mark to. In both, the term with its regions dropped
   has neither the kind nor the argument, goes on and exits. The
   erasure mends a number of parameters, of kinds or of arguments
   that is wrong by the regions that it drops, and by nothing else:
   of a handler with no kind [Region] it changes neither the
   parameters nor the kinds (its body is erased as every expression
   is), and it drops no argument of a jump to it. The check refuses
   both terms. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaValueSpec
  FlambdaSemanticsSpec FlambdaCompareSpec FlambdaUnusedStaticsSpec
  FlambdaLoopifySpec FlambdaLiftSpec FlambdaImportsSpec FlambdaValidateSpec
  FlambdaValidateImportsSpec FlambdaRegionsSpec FlambdaRegionsErasureSpec
  FlambdaRegionsCheckSpec FlambdaRegionsCheckedSpec.
Import ListNotations.

(* ======================================================================== *)
(* Statements                                                               *)
(* ======================================================================== *)

(* Of a run whose states satisfy [reads_live] and in every state of
   which the regions of the handler that is applied are given: where
   it stops because [step] has no step, the run of the term with its
   regions dropped goes wrong. *)
Definition no_plain_step_erased_statement : Prop :=
  ∀ (e : expr) (statics : static_env) (base : symbol) (fuel : nat),
    region_names_fresh base e statics = true ->
    erasable e statics = true ->
    (∀ (fuel' : nat) (rs : region_state),
       region_run fuel' (initial_region_state e statics base)
       = Region_step rs ->
       reads_live rs ∧ regions_given rs = true) ->
    region_run fuel (initial_region_state e statics base)
    = Region_undefined No_plain_step ->
    behaves (erased_initial_state e statics) Goes_wrong.

(* The check is sound: the regions of a term that passes it, with any
   certificate, add no fault to the term. *)
Definition region_check_sound_statement : Prop :=
  ∀ (cert : certificate) (statics : static_env) (base : symbol) (e : expr),
    region_check cert statics e = true ->
    region_names_fresh base e statics = true ->
    erasable e statics = true ->
    regions_add_no_fault e statics base.

(* Of a run of Simplify, with the check. The first premise is
   [refines] of the two terms with their regions dropped: a relation
   of the model, and not a verdict of the validation
   ([validated_and_checked_safe_statement] has in its place what the
   test tool computes). If it holds, the term before, with its
   regions dropped, does not go wrong, and the term after passes the
   check, with any certificate, then the term after, with its
   regions, never stops without a step. It is
   FlambdaRegionsCheckSpec.checked_after_safe_statement with the
   check of the term after, the freshness ([region_names_fresh]) and
   [erasable] of the term after in the place of its
   premise [regions_add_no_fault]. Nothing is asked of the regions of
   the term before. *)
Definition refined_and_checked_safe_statement : Prop :=
  ∀ (cert : certificate) (statics : static_env) (base : symbol)
    (before after : expr),
    refines (erased_initial_state before statics)
      (erased_initial_state after statics) ->
    ~ behaves (erased_initial_state before statics) Goes_wrong ->
    region_check cert statics after = true ->
    region_names_fresh base after statics = true ->
    erasable after statics = true ->
    region_safe (initial_region_state after statics base).

(* And then the two runs compute the same: an exit of the term before
   with its regions is an exit of the term after with its regions,
   through the same continuation, with values that are erased to the
   same values where they may be evaluated or are locations. It is
   FlambdaRegionsCheckSpec.checked_exits_agree_statement with the
   check of the term after in the place of its premise
   [regions_add_no_fault]. *)
Definition refined_and_checked_exits_agree_statement : Prop :=
  ∀ (cert : certificate) (statics : static_env) (base : symbol)
    (before after : expr),
    region_names_fresh base before statics = true ->
    region_names_fresh base after statics = true ->
    erasable before statics = true ->
    erasable after statics = true ->
    refines (erased_initial_state before statics)
      (erased_initial_state after statics) ->
    ~ behaves (erased_initial_state before statics) Goes_wrong ->
    region_check cert statics after = true ->
    ∀ (fuel : nat) (k : continuation) (vs : list value) (rs : region_state),
      region_run fuel (initial_region_state before statics base)
      = Region_exit k vs rs ->
      ∃ (fuel' : nat) (ws : list value) (rs' : region_state)
        (us : list value),
        region_run fuel' (initial_region_state after statics base)
        = Region_exit k ws rs'
        ∧ Forall2 (value_erased_if_usable rs) vs us
        ∧ Forall2 (value_erased_if_usable rs') ws us.

(* Where the term after, with its regions dropped, goes wrong, the
   term before, with its regions dropped, does. *)
Definition erased_after_wrong_only_if_before (before after : expr)
    (statics : static_env) : Prop :=
  behaves (erased_initial_state after statics) Goes_wrong ->
  behaves (erased_initial_state before statics) Goes_wrong.

(* An exit of the term before, with its regions dropped, is matched by
   an exit of the term after, with its regions dropped, through the
   same continuation, and [R] holds of the values and the heap of the
   first and of those of the second. *)
Definition erased_exits_related
    (R : list value -> heap -> list value -> heap -> Prop)
    (before after : expr) (statics : static_env) : Prop :=
  ∀ (k : continuation) (vs : list value) (hp : heap),
    behaves (erased_initial_state before statics) (Exits k vs hp) ->
    ∃ (vs' : list value) (hp' : heap),
      behaves (erased_initial_state after statics) (Exits k vs' hp')
      ∧ R vs hp vs' hp'.

(* [refines] of the first states of the two terms with their regions
   dropped gives both: the second with, for [R], the same values and
   the same heap. *)
Definition refines_erased_related_statement : Prop :=
  ∀ (statics : static_env) (before after : expr),
    refines (erased_initial_state before statics)
      (erased_initial_state after statics) ->
    erased_after_wrong_only_if_before before after statics
    ∧ erased_exits_related (fun vs hp vs' hp' => vs' = vs ∧ hp' = hp) before
        after statics.

(* [refined_and_checked_safe_statement] with what it uses of [refines]
   in the place of [refines]. The first two premises together imply
   that the term after, with its regions dropped, does not go wrong.
   With non-wrongness of the erased term before fixed, the first
   premise is equivalent to non-wrongness of the erased term after.
   Nothing else of the term before is used. Nothing is asked of the
   regions of the term before. *)
Definition related_and_checked_safe_statement : Prop :=
  ∀ (cert : certificate) (statics : static_env) (base : symbol)
    (before after : expr),
    erased_after_wrong_only_if_before before after statics ->
    ~ behaves (erased_initial_state before statics) Goes_wrong ->
    region_check cert statics after = true ->
    region_names_fresh base after statics = true ->
    erasable after statics = true ->
    region_safe (initial_region_state after statics base).

(* And the exits, with a relation [R] of the exits of the two terms
   with their regions dropped in the place of their equality. An exit
   of the term before with its regions is matched by an exit of the
   term after with its regions, through the same continuation. The
   values of the first are erased, where they may be evaluated or are
   locations, to those of an exit of the term before with its regions
   dropped; the values of the second, in the same way, to those of an
   exit of the term after with its regions dropped; and [R] holds of
   those two exits, values and heaps.

   [R] is any relation. With one that nothing satisfies,
   [erased_exits_related] says that the term before, with its regions
   dropped, has no exit; the term before with its regions then has
   none (FlambdaRegionsErasureSpec.erasure_exits_statement), and the
   statement says nothing. With one that everything satisfies, the
   conclusion is still that the term after with its regions exits
   through the same continuation, with values erased to those of an
   exit of the term after with its regions dropped. *)
Definition related_and_checked_exits_statement : Prop :=
  ∀ (R : list value -> heap -> list value -> heap -> Prop)
    (cert : certificate) (statics : static_env) (base : symbol)
    (before after : expr),
    region_names_fresh base before statics = true ->
    region_names_fresh base after statics = true ->
    erasable before statics = true ->
    erasable after statics = true ->
    erased_exits_related R before after statics ->
    erased_after_wrong_only_if_before before after statics ->
    ~ behaves (erased_initial_state before statics) Goes_wrong ->
    region_check cert statics after = true ->
    ∀ (fuel : nat) (k : continuation) (vs : list value) (rs : region_state),
      region_run fuel (initial_region_state before statics base)
      = Region_exit k vs rs ->
      ∃ (fuel' : nat) (ws : list value) (rs' : region_state)
        (us us' : list value) (hp hp' : heap),
        region_run fuel' (initial_region_state after statics base)
        = Region_exit k ws rs'
        ∧ behaves (erased_initial_state before statics) (Exits k us hp)
        ∧ behaves (erased_initial_state after statics) (Exits k us' hp')
        ∧ Forall2 (value_erased_if_usable rs) vs us
        ∧ Forall2 (value_erased_if_usable rs') ws us'
        ∧ R us hp us' hp'.

(* [refined_and_checked_safe_statement] of a unit with its imports,
   for a refinement that is proved on the machine of
   FlambdaSemanticsSpec.v of the two terms with their regions
   dropped. The static environment is that of the imports, and
   [unit_refines] of [erase] of the two terms is in the place of
   [refines] of their first states there: the two are one
   proposition, as [erase_statics] leaves a static environment that
   has no code as it is. The other premises are those of
   [refined_and_checked_safe_statement] at that static environment.
   Nothing is asked of the regions of the term before. *)
Definition unit_refined_and_checked_safe_statement : Prop :=
  ∀ (imports : list (symbol * import_class)) (cert : certificate)
    (base : symbol) (before after : expr),
    let statics := imports_statics imports in
    unit_refines imports (erase [] before) (erase [] after) ->
    ~ behaves (erased_initial_state before statics) Goes_wrong ->
    region_check cert statics after = true ->
    region_names_fresh base after statics = true ->
    erasable after statics = true ->
    region_safe (initial_region_state after statics base).

(* And then the two runs compute the same, as in
   [refined_and_checked_exits_agree_statement] and with its other
   premises at the static environment of the imports: an exit of the
   term before with its regions is an exit of the term after with its
   regions, through the same continuation, with values that are
   erased to the same values where they may be evaluated or are
   locations. *)
Definition unit_refined_and_checked_exits_agree_statement : Prop :=
  ∀ (imports : list (symbol * import_class)) (cert : certificate)
    (base : symbol) (before after : expr),
    let statics := imports_statics imports in
    region_names_fresh base before statics = true ->
    region_names_fresh base after statics = true ->
    erasable before statics = true ->
    erasable after statics = true ->
    unit_refines imports (erase [] before) (erase [] after) ->
    ~ behaves (erased_initial_state before statics) Goes_wrong ->
    region_check cert statics after = true ->
    ∀ (fuel : nat) (k : continuation) (vs : list value) (rs : region_state),
      region_run fuel (initial_region_state before statics base)
      = Region_exit k vs rs ->
      ∃ (fuel' : nat) (ws : list value) (rs' : region_state)
        (us : list value),
        region_run fuel' (initial_region_state after statics base)
        = Region_exit k ws rs'
        ∧ Forall2 (value_erased_if_usable rs) vs us
        ∧ Forall2 (value_erased_if_usable rs') ws us.

(* The same of a unit with its imports, with what the test tool
   computes in the place of [refines]. [validated_before] and
   [validated_after] are the two terms that the validation is given.
   If the verdict that [validate_unit] gives of them passes the
   model's test of it with the imports ([verdict_holds_from]: the
   premise of
   FlambdaValidateImportsSpec.validate_unit_sound_verdict_imports_statement),
   each of them is, up to bound names, [erase] of the term with its
   regions ([expr_eqb]), the term before, with its regions dropped,
   does not go wrong, and the term after passes the check, with any
   certificate, then the term after, with its regions, run from the
   static environment of the imports, never stops without a step.
   The other premises are those of
   [refined_and_checked_safe_statement] at that static environment.
   Nothing is asked of the regions of the term before. *)
Definition validated_and_checked_safe_statement : Prop :=
  ∀ (imports : list (symbol * import_class)) (rounds : nat)
    (unused : dropped) (slots : list value_slot) (G : loopified)
    (Ls : list lifting) (kept : list code_id) (cert : certificate)
    (base : symbol) (before after validated_before validated_after : expr),
    let statics := imports_statics imports in
    verdict_holds_from statics rounds unused slots G Ls kept
      validated_before validated_after
      (validate_unit rounds unused slots G Ls kept validated_before
         validated_after)
    = true ->
    expr_eqb [] [] (erase [] before) validated_before = true ->
    expr_eqb [] [] (erase [] after) validated_after = true ->
    ~ behaves (erased_initial_state before statics) Goes_wrong ->
    region_check cert statics after = true ->
    region_names_fresh base after statics = true ->
    erasable after statics = true ->
    region_safe (initial_region_state after statics base).

(* And then the two runs compute the same, as in
   [refined_and_checked_exits_agree_statement] and with its other
   premises at the static environment of the imports: an exit of the
   term before with its regions is an exit of the term after with its
   regions, through the same continuation, with values that are
   erased to the same values where they may be evaluated or are
   locations. *)
Definition validated_and_checked_exits_agree_statement : Prop :=
  ∀ (imports : list (symbol * import_class)) (rounds : nat)
    (unused : dropped) (slots : list value_slot) (G : loopified)
    (Ls : list lifting) (kept : list code_id) (cert : certificate)
    (base : symbol) (before after validated_before validated_after : expr),
    let statics := imports_statics imports in
    verdict_holds_from statics rounds unused slots G Ls kept
      validated_before validated_after
      (validate_unit rounds unused slots G Ls kept validated_before
         validated_after)
    = true ->
    expr_eqb [] [] (erase [] before) validated_before = true ->
    expr_eqb [] [] (erase [] after) validated_after = true ->
    ~ behaves (erased_initial_state before statics) Goes_wrong ->
    region_check cert statics after = true ->
    region_names_fresh base before statics = true ->
    region_names_fresh base after statics = true ->
    erasable before statics = true ->
    erasable after statics = true ->
    ∀ (fuel : nat) (k : continuation) (vs : list value) (rs : region_state),
      region_run fuel (initial_region_state before statics base)
      = Region_exit k vs rs ->
      ∃ (fuel' : nat) (ws : list value) (rs' : region_state)
        (us : list value),
        region_run fuel' (initial_region_state after statics base)
        = Region_exit k ws rs'
        ∧ Forall2 (value_erased_if_usable rs) vs us
        ∧ Forall2 (value_erased_if_usable rs') ws us.
