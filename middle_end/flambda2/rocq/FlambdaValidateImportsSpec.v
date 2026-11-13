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

(* The validation, of a unit that imports symbols.

   This file is to be reviewed: [holds_from_imports], which is extracted
   and read by the test tool of middle_end/flambda2/tests/semantics/;
   [holds_from], which that tool is to read in its place; the eight
   statements of the validation; and
   [static_names_free_in_head_statement].

   FlambdaValidateSpec.validate_unit_sound_statement is of the two
   units run from the empty static environment
   (FlambdaUnusedStaticsSpec.program_refines). A unit that mentions a
   symbol of another unit is run from the static environment of its
   imports (FlambdaImportsSpec.imports_statics), and of that run the
   statement says nothing: in the empty environment the symbol is bound
   to nothing.

   [validate_unit_sound_imports_statement] is the same of the unit run
   from its imports (FlambdaImportsSpec.unit_refines), whatever they
   are, for three of the five ways in which a unit is validated: the
   two terms are the same up to bound names; they are once normalised;
   they are once the unused static bindings of the term before are
   removed as well ([holds_from_imports]). Why these three:
   - the normalisations of the two terms, the making of loops, the
     placing of continuations, the tidying of the terms so placed and
     the comparison are refinements or equivalences under all
     environments, so under that of the imports;
   - the removal of unused static bindings is a refinement from any
     environments in which the names removed occur nowhere
     (FlambdaUnusedStaticsSpec.drop_statics_refines_statement), and
     they occur nowhere in the static environment of the imports, which
     has no code and binds each symbol to something that holds no
     value.
   Nothing else is asked of the list of imports. A list may bind a
   symbol which the unit before binds too. A run of the unit before
   that reaches that binding is then undefined (a static binding of a
   name that is bound has no step), and the statement holds of such a
   run for nothing; a binding that is not reached, in a handler that
   is not applied, changes nothing.

   The removal is from the term before only, and that is why it needs
   no condition: removing a binding from the term before can only take
   away a reason for it to be undefined. Removing an unused static
   binding from the term after is the converse, and is not right from
   the imports as it stands: a term after that binds an imported
   symbol, and does not use it, is undefined from the imports, and is
   the same as the term before once the binding is removed. A verdict
   that rests on such a removal is not one of the three. It holds
   under the condition that this asks for: the static environment
   binds none of the names that the groups at the head of the term
   after bind (FlambdaUnusedHeadStaticsSpec.head_free_in, the premise
   of FlambdaUnusedHeadStaticsSpec.drop_head_statics_refines_from_statement).
   [holds_from] is [holds_from_imports] with that verdict taken under
   that test, and [validate_unit_sound_head_from_statement], the same
   of the second asking, and the two at the static environment of the
   imports, are the statements of the section above with [holds_from]
   in the place of [holds_from_imports]. The test is of the term that
   the validation removes the bindings from: the term after,
   normalised and tidied.

   [validate_unit_knowing_sound_imports_statement] is the same of the
   second asking (FlambdaValidateKnowingSpec.validate_unit_knowing),
   which is [validate_unit] of the two terms normalised with what is
   known of their names (the aliases of variables, what symbols are
   bound to, the closures that a [Let] binds): those normalisations
   are under all environments too.

   [validate_unit_sound_from_statement] and
   [validate_unit_knowing_sound_from_statement] are the same two from
   any heap and from any static environment in whose code and in whose
   values the names that the validation removes from the term before
   do not occur (FlambdaUnusedStaticsSpec.statics_free_of; which
   symbols and code ids the environment binds is not looked at). The
   two above are these at the static environment of the imports, which
   holds no code and binds each symbol to something that holds no
   value. They are of a unit run after other units have
   bound code and symbols, as far as the model can say what those are:
   a call of code that the unit does not bind has there the meaning of
   the code that the environment binds. They say nothing of a call
   whose code is not code of the model.

   What it is not of:
   - a unit validated once unused static bindings are removed from the
     head of the term after as well
     ([Same_once_head_statics_removed]), where the static environment
     binds a name that the groups at the head of that term bind: that
     removal is the one of the paragraph above;
   - a unit validated once something is lifted
     ([Same_once_lifted]). The liftings, and what is done to a lifted
     term (FlambdaLiftSpec, FlambdaLiftFromCodeSpec,
     FlambdaLiftFromArmsSpec, FlambdaKnownSymbolsSpec,
     FlambdaKnownSlotsSpec, FlambdaUnusedSlotsSpec,
     FlambdaHoistCodeSpec, FlambdaHoistStaticsSpec), are each stated
     from the empty static environment. Each is to be stated from the
     imports by its owner before this is;
   - the machine with a stack of handlers (FlambdaTrapSpec.v). Its
     agreement with this one is stated from any static environment
     that holds no code, of which that of the imports is one
     (FlambdaTrapSpec.stack_agrees_from_statement), for a unit whose
     binders are distinct and that follows the discipline of trap
     actions; no statement here puts the two together.

   The proofs are in FlambdaValidateImportsProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaUnusedStaticsSpec FlambdaUnusedHeadStaticsSpec FlambdaLoopifySpec
  FlambdaLiftSpec FlambdaValidateSpec FlambdaValidateKnowingSpec
  FlambdaImportsSpec.
Import ListNotations.

(* Whether a verdict of [validate_unit] is one that holds of the unit
   run from its imports: every way of being validated but the one that
   removes static bindings from the head of the term after and the one
   that lifts. *)
Definition holds_from_imports (v : validation) : bool :=
  match v with
  | Same_up_to_bound_names | Same_once_normalised
  | Same_once_unused_statics_removed =>
    true
  | Same_once_head_statics_removed | Same_once_lifted | Not_validated =>
    false
  end.

(* A unit that is validated in one of the three ways that
   [holds_from_imports] accepts refines the unit it came from, each run
   on its own from the same imports. *)
Definition validate_unit_sound_imports_statement : Prop :=
  ∀ (imports : list (symbol * import_class)) (rounds : nat)
    (unused : dropped) (slots : list value_slot) (G : loopified)
    (Ls : list lifting) (kept : list code_id) (before after : expr),
    holds_from_imports
      (validate_unit rounds unused slots G Ls kept before after)
    = true ->
    unit_refines imports before after.

(* The same of the second asking. *)
Definition validate_unit_knowing_sound_imports_statement : Prop :=
  ∀ (imports : list (symbol * import_class)) (rounds : nat)
    (unused : dropped) (slots : list value_slot) (G : loopified)
    (Ls : list lifting) (kept : list code_id) (before after : expr),
    holds_from_imports
      (validate_unit_knowing rounds unused slots G Ls kept before after)
    = true ->
    unit_refines imports before after.

(* The same from any heap and from any static environment in whose
   code and in whose values the names that the validation removes from
   the term before do not occur
   (FlambdaUnusedStaticsSpec.statics_free_of). *)
(* CR mshinwell: the heap is any heap because no step of this machine
   reads or changes it. When a step runs the primitives of the heap,
   the premise [heap_free_of unused hp = true] (the names removed
   occur in no value of a cell of the heap;
   FlambdaHeapMachineSpec.heap_free_of in this tree, which is to move
   beside [statics_free_of] with that change) is to be added here, as
   it is to be added to
   FlambdaUnusedStaticsSpec.drop_statics_refines_statement: a symbol
   that only the heap names is otherwise removed from under a read. *)
Definition validate_unit_sound_from_statement : Prop :=
  ∀ (statics : static_env) (hp : heap) (rounds : nat) (unused : dropped)
    (slots : list value_slot) (G : loopified) (Ls : list lifting)
    (kept : list code_id) (before after : expr),
    holds_from_imports
      (validate_unit rounds unused slots G Ls kept before after)
    = true ->
    statics_free_of unused statics = true ->
    refines (State before [] [] statics hp) (State after [] [] statics hp).

(* The same of the second asking. *)
Definition validate_unit_knowing_sound_from_statement : Prop :=
  ∀ (statics : static_env) (hp : heap) (rounds : nat) (unused : dropped)
    (slots : list value_slot) (G : loopified) (Ls : list lifting)
    (kept : list code_id) (before after : expr),
    holds_from_imports
      (validate_unit_knowing rounds unused slots G Ls kept before after)
    = true ->
    statics_free_of unused statics = true ->
    refines (State before [] [] statics hp) (State after [] [] statics hp).

(* ======================================================================== *)
(* The verdict that removes static bindings from the head of the term after *)
(* ======================================================================== *)

(* Whether a verdict of [validate_unit] is one that holds of the unit
   run from the static environment [statics]: the three of
   [holds_from_imports], and the one that removes static bindings from
   the head of the term after, where [statics] binds no symbol and no
   code id that the groups at the head of that term bind
   (FlambdaUnusedHeadStaticsSpec.head_free_in). The term is the one
   that [validate_unit] removes them from: [after], normalised and
   tidied. For a static environment in general the statements below
   also ask that the names removed occur in none of its code and
   values ([statics_free_of]); this test does not check that. *)
Definition holds_from (statics : static_env) (rounds : nat)
    (kept : list code_id) (after : expr) (v : validation) : bool :=
  match v with
  | Same_up_to_bound_names | Same_once_normalised
  | Same_once_unused_statics_removed =>
    true
  | Same_once_head_statics_removed =>
    head_free_in statics
      (tidied_after rounds (normalise_after rounds kept after))
  | Same_once_lifted | Not_validated => false
  end.

(* A static environment that binds no name that a term binds
   (FlambdaImportsSpec.static_names_free_in) binds none that the
   groups at its head bind. *)
Definition static_names_free_in_head_statement : Prop :=
  ∀ (statics : static_env) (e : expr),
    static_names_free_in statics e = true -> head_free_in statics e = true.

(* A unit that is validated in one of the ways that [holds_from]
   accepts refines the unit it came from, each run from a static
   environment in whose code and in whose values the names removed do
   not occur, and from any heap. *)
(* CR mshinwell: as at [validate_unit_sound_from_statement], and at
   FlambdaUnusedHeadStaticsSpec.drop_head_statics_refines_from_statement:
   the heap is any heap because no step of this machine reads or
   changes it, and the premise [heap_free_of unused hp = true] is to
   be added when a step runs the primitives of the heap. *)
Definition validate_unit_sound_head_from_statement : Prop :=
  ∀ (statics : static_env) (hp : heap) (rounds : nat) (unused : dropped)
    (slots : list value_slot) (G : loopified) (Ls : list lifting)
    (kept : list code_id) (before after : expr),
    holds_from statics rounds kept after
      (validate_unit rounds unused slots G Ls kept before after)
    = true ->
    statics_free_of unused statics = true ->
    refines (State before [] [] statics hp) (State after [] [] statics hp).

(* The same of the second asking. The term after that it gives
   [validate_unit] is the term after normalised with what is known of
   its names. *)
Definition validate_unit_knowing_sound_head_from_statement : Prop :=
  ∀ (statics : static_env) (hp : heap) (rounds : nat) (unused : dropped)
    (slots : list value_slot) (G : loopified) (Ls : list lifting)
    (kept : list code_id) (before after : expr),
    holds_from statics rounds kept
      (normalise_knowing (normalise_after_round kept) rounds after)
      (validate_unit_knowing rounds unused slots G Ls kept before after)
    = true ->
    statics_free_of unused statics = true ->
    refines (State before [] [] statics hp) (State after [] [] statics hp).

(* The two at the static environment of the imports: the test is that
   the groups at the head of the term after bind no imported symbol. *)
Definition validate_unit_sound_head_imports_statement : Prop :=
  ∀ (imports : list (symbol * import_class)) (rounds : nat)
    (unused : dropped) (slots : list value_slot) (G : loopified)
    (Ls : list lifting) (kept : list code_id) (before after : expr),
    holds_from (imports_statics imports) rounds kept after
      (validate_unit rounds unused slots G Ls kept before after)
    = true ->
    unit_refines imports before after.

Definition validate_unit_knowing_sound_head_imports_statement : Prop :=
  ∀ (imports : list (symbol * import_class)) (rounds : nat)
    (unused : dropped) (slots : list value_slot) (G : loopified)
    (Ls : list lifting) (kept : list code_id) (before after : expr),
    holds_from (imports_statics imports) rounds kept
      (normalise_knowing (normalise_after_round kept) rounds after)
      (validate_unit_knowing rounds unused slots G Ls kept before after)
    = true ->
    unit_refines imports before after.
