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

(* The machine under a permutation of locations.

   This file is to be reviewed: [state_locations_bound],
   [result_locations_bound], and the statements.

   FlambdaLocationsSpec.v has the action of a permutation of locations
   on a state, and FlambdaLocationsPrimitiveSpec.v says how the
   primitives go through it. This file says it of a step of the
   machine (FlambdaSemanticsSpec.step), of a run and of a behaviour.

   The form of the statements. A step that allocates chooses a
   location (FlambdaHeapSpec.fresh_location), and the choice does not
   commute with a permutation. So a step, a run and a behaviour go
   through the action up to a second permutation
   ([step_permuted_statement], [run_permuted_statement],
   [behaves_permuted_statement]): what the state moved by [p] comes to
   is what the state comes to, moved by some [p'] that agrees with [p]
   on every location that the heap of the state binds, as the state
   is before the step or the run. That agreement is all that is said
   of [p']: nothing is said of it on a location that the heap of the
   state does not bind, whether or not the run allocates it.

   The premise ([state_locations_bound]): the heap of the state binds
   every location of the state, those of every entry of the heap
   among them. FlambdaLocationsPrimitiveSpec.v says why it is needed
   and why it counts the entries that a later write hides. A state
   that holds no location satisfies it ([no_location_bound_statement];
   its heap is empty, a key being a location): such is the state that
   a unit starts from. It is kept by a step and by a run
   ([step_keeps_locations_bound_statement],
   [run_keeps_locations_bound_statement]), with the fact that a
   location bound stays bound; and by the action
   ([permute_state_locations_bound_statement]).

   Where the machine stands. The primitives that allocate, read and
   write are those of FlambdaHeapSpec.exec_prim, and [step] does not
   run them yet: a [Let] of a primitive is
   FlambdaPrimitiveSpec.eval_prim, which has no value on them, and
   every step leaves the heap as it is. So of the machine as it is
   the equation holds with [p'] equal to [p] and without the premise.
   It is not stated: it stops being true when [step] runs the
   primitives of the heap, and the statements here are those that stay
   true then. What a [Let] is to run is FlambdaHeapMachineSpec.exec_named,
   and the two statements about it here
   ([exec_named_permuted_statement],
   [exec_named_keeps_locations_bound_statement]) are what the case of
   a [Let] needs then; the other cases of a step do not allocate.

   What is not here. The equivalences and refinements of
   FlambdaSemanticsSpec.v compare exits by [=], values and heap, so a
   state and the state moved need not be equivalent in that sense; a
   relation between exits that pairs locations is in
   FlambdaHeapMachineSpec.v, for the machine with a heap of its own, and the
   link between it and the action is not stated.

   Nothing is trusted here. The proofs are in
   FlambdaLocationsMachineProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaNominalSpec FlambdaHeapSpec
  FlambdaHeapMachineSpec FlambdaLocationsSpec FlambdaLocationsPrimitiveSpec.
Import ListNotations.

(* ======================================================================== *)
(* The premise                                                              *)
(* ======================================================================== *)

(* The heap of the state binds every location of the state. *)
Definition state_locations_bound (s : state) : Prop :=
  locations_bound (state_heap s) (locations_of_state s).

(* The same of what a step or a run comes to, with the fact that a
   location that the heap [h] bound is still bound: of the state that
   it steps to; of the heap and the values of an exit. *)
Definition result_locations_bound (h : heap) (result : step_result)
    : Prop :=
  match result with
  | Step s =>
    state_locations_bound s
    ∧ (∀ l : location,
         is_bound l h = true -> is_bound l (state_heap s) = true)
  | Exit _ vs hp =>
    locations_bound hp (locations_of_heap hp)
    ∧ locations_bound hp (locations_of_values vs)
    ∧ (∀ l : location, is_bound l h = true -> is_bound l hp = true)
  | Undefined => True
  end.

(* A state that holds no location. *)
Definition no_location_bound_statement : Prop :=
  ∀ s : state, locations_of_state s = [] -> state_locations_bound s.

(* The action keeps it. *)
Definition permute_state_locations_bound_statement : Prop :=
  ∀ (p : permutation) (s : state),
    state_locations_bound s -> state_locations_bound (permute_state p s).

(* A step and a run keep it. *)
Definition step_keeps_locations_bound_statement : Prop :=
  ∀ s : state,
    state_locations_bound s ->
    result_locations_bound (state_heap s) (step s).

Definition run_keeps_locations_bound_statement : Prop :=
  ∀ (fuel : nat) (s : state),
    state_locations_bound s ->
    result_locations_bound (state_heap s) (run fuel s).

(* ======================================================================== *)
(* A step, a run and a behaviour, up to the locations allocated             *)
(* ======================================================================== *)

Definition step_permuted_statement : Prop :=
  ∀ (p : permutation) (s : state),
    state_locations_bound s ->
    ∃ p' : permutation,
      (∀ l : location,
         is_bound l (state_heap s) = true -> permute p' l = permute p l)
      ∧ step (permute_state p s) = permute_result p' (step s).

Definition run_permuted_statement : Prop :=
  ∀ (p : permutation) (fuel : nat) (s : state),
    state_locations_bound s ->
    ∃ p' : permutation,
      (∀ l : location,
         is_bound l (state_heap s) = true -> permute p' l = permute p l)
      ∧ run fuel (permute_state p s) = permute_result p' (run fuel s).

Definition behaves_permuted_statement : Prop :=
  ∀ (p : permutation) (s : state) (b : behaviour),
    state_locations_bound s ->
    behaves s b ->
    ∃ p' : permutation,
      (∀ l : location,
         is_bound l (state_heap s) = true -> permute p' l = permute p l)
      ∧ behaves (permute_state p s) (permute_behaviour p' b).

(* ======================================================================== *)
(* What a [Let] is to run                                                   *)
(* ======================================================================== *)

(* FlambdaHeapMachineSpec.exec_named: a primitive is
   FlambdaHeapSpec.exec_prim on the heap, and anything else is
   FlambdaSemanticsSpec.eval_named with the heap as it came. *)
Definition exec_named_permuted_statement : Prop :=
  ∀ (p : permutation) (statics : static_env) (h : heap) (vars : env)
    (defining_expr : named),
    locations_bound h (locations_of_heap h) ->
    locations_bound h (locations_of_env vars) ->
    ∃ p' : permutation,
      (∀ l : location, is_bound l h = true -> permute p' l = permute p l)
      ∧ exec_named (permute_static_env p statics) (permute_heap p h)
          (permute_env p vars) defining_expr
        = option_map (permute_value_and_heap p')
            (exec_named statics h vars defining_expr).

Definition exec_named_keeps_locations_bound_statement : Prop :=
  ∀ (statics : static_env) (h h' : heap) (vars : env)
    (defining_expr : named) (v : value),
    locations_bound h (locations_of_heap h) ->
    locations_bound h (locations_of_env vars) ->
    locations_bound h (locations_of_static_env statics) ->
    exec_named statics h vars defining_expr = Some (v, h') ->
    locations_bound h' (locations_of_heap h')
    ∧ locations_bound h' (locations_of_value v)
    ∧ (∀ l : location, is_bound l h = true -> is_bound l h' = true).
