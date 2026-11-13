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

(* What may follow a unit, and two exits that nothing that may follow
   tells apart.

   This file is to be reviewed: [scalar], [same_scalars],
   [observed_refines], [binds_no_static], [observer], [observers],
   [worlds_observed], [refines_under_observers], and the statements.

   [FlambdaSemanticsSpec.refines] asks of two exits the same values. A
   pass that changes a value that a unit exits with cannot be stated
   so: a lifting gives a symbol where there was a block or a closure
   (FlambdaLiftSpec.v). What such a pass keeps is what can be done next
   with the values. This file says that by the terms that may be run
   next:
   - an [observer] is what the continuation of an exit may stand for: a
     way out, or a handler with no environment of its own, which binds
     nothing static, names no symbol and no code id, and projects none
     of some value slots given. It may read, store, allocate, project
     and call;
   - [worlds_observed] relates two worlds that exits leave
     (FlambdaExitWorldSpec.exit_world) when every observer, applied to
     the values of the first under its static environment and heap, and
     to the values of the second under its own, comes to two results
     that [observed_refines] relates;
   - [observed_refines] is [refines] of what two steps come to, with an
     exit compared by its continuation, by the constants and the
     locations among its values, and by the locations that its heap
     binds: not by its other values, nor by what the cells hold.
   The comparison of two units is then
   [FlambdaExitWorldSpec.refines_world (worlds_observed slots)] of the
   two, each run on its own.

   A pass proves it in another form, [refines_under_observers]: the two
   units, run from one continuation environment of observers, come to
   results that [observed_refines] relates, whatever the environment.
   The two forms say the same of units whose code is closed, from a
   static environment whose code is closed
   ([under_observers_worlds_statement], by FlambdaRunUnderSpec.v).
   Refinement under all environments gives the second form
   ([expr_refines_under_observers_statement]), and the second form
   composes ([refines_under_observers_trans_statement]).

   The units start with no variable, from a static environment and a
   heap that are given: the empty ones, or those of the imports of a
   unit.

   Whether this is what the verdict on a pass that changes values is to
   mean has not been decided. The statements of passes that use this
   file are in the files of those passes; the validation does not use
   it.

   The proofs are in FlambdaObserversProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaValueSpec FlambdaSemanticsSpec FlambdaBindersSpec
  FlambdaStaticsInScopeSpec FlambdaUnusedSlotsSpec FlambdaUnusedStaticsSpec
  FlambdaExitWorldSpec FlambdaRunUnderSpec.
Import ListNotations.

(* ======================================================================== *)
(* What an exit is compared by                                              *)
(* ======================================================================== *)

(* A constant or a location. *)
Definition scalar (v : value) : Prop :=
  (∃ c : const, v = Value_const c) ∨ (∃ l : location, v = Value_location l).

(* Two lists of values with the same constants and the same locations at
   the same places: where either value is a constant or a location, the
   two are the same value. *)
Definition same_scalars (vs vs' : list value) : Prop :=
  Forall2 (fun v v' => scalar v ∨ scalar v' -> v = v') vs vs'.

Definition same_scalars_refl_statement : Prop :=
  ∀ vs : list value, same_scalars vs vs.

Definition same_scalars_trans_statement : Prop :=
  ∀ vs vs' vs'' : list value,
    same_scalars vs vs' -> same_scalars vs' vs'' -> same_scalars vs vs''.

(* [refines] of what two steps come to, with an exit compared by its
   continuation, by the constants and the locations among its values,
   and by the locations that its heap binds, in their order: not by the
   other values, nor by what the cells hold. An exit of the source is
   answered by such an exit of the target; and the target ends only if
   the source exits or goes wrong. *)
Definition observed_refines (source target : step_result) : Prop :=
  (∀ (k : continuation) (vs : list value) (hp : heap),
    step_result_behaves source (Exits k vs hp) ->
    ∃ (vs' : list value) (hp' : heap),
      step_result_behaves target (Exits k vs' hp')
      ∧ same_scalars vs vs'
      ∧ map fst hp = map fst hp')
  ∧ (∀ b : behaviour,
      b <> Diverges ->
      step_result_behaves target b ->
      step_result_behaves source Goes_wrong
      ∨ ∃ (k : continuation) (vs : list value) (hp : heap),
          step_result_behaves source (Exits k vs hp)).

Definition observed_refines_refl_statement : Prop :=
  ∀ result : step_result, observed_refines result result.

Definition observed_refines_trans_statement : Prop :=
  ∀ r1 r2 r3 : step_result,
    observed_refines r1 r2 -> observed_refines r2 r3 ->
    observed_refines r1 r3.

(* ======================================================================== *)
(* What may follow a unit                                                   *)
(* ======================================================================== *)

(* An expression with no static binding in it, of a symbol, of code or
   of deleted code, at any depth. *)
Fixpoint binds_no_static (e : expr) : bool :=
  match e with
  | Let _ _ _ body => binds_no_static body
  | Let_static _ _ => false
  | Let_cont_non_recursive _ h body =>
    handler_binds_no_static h && binds_no_static body
  | Let_cont_recursive handlers body =>
    forallb (fun '(_, h) => handler_binds_no_static h) handlers
    && binds_no_static body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => true
  end
with handler_binds_no_static (h : continuation_handler) : bool :=
  match h with
  | Handler _ _ body => binds_no_static body
  end.

(* What a unit may be followed by: a way out, or a handler with no
   environment of its own, in which there is no static binding, which
   names no symbol and no code id (with no static binding in it,
   nothing is in scope but what is around it, and nothing is), and
   which projects none of the value slots given. It may read, store,
   allocate, project and call. *)
Definition observer (slots : list value_slot) (c : cont_value) : Prop :=
  match c with
  | Outer _ => True
  | Closure (Handler _ _ body) [] [] [] =>
    binds_no_static body = true
    ∧ expr_statics_in_scope [] [] body = true
    ∧ slots_unused slots body = true
  | _ => False
  end.

(* Every entry, the ones that an earlier entry hides included. *)
Definition observers (slots : list value_slot) (conts : cont_env) : Prop :=
  Forall (fun kc => observer slots (snd kc)) conts.

(* A control: a declaration of deleted code brings its code id into
   scope and is not counted by [FlambdaSemanticsSpec.binds_statics]. A
   handler that declares a code id deleted and makes a closure of it
   passes those two tests, and it is not free of that code id;
   [binds_no_static] refuses it. *)
Definition deleted_code_no_observer_statement : Prop :=
  let d : code_id := 1%positive in
  let body :=
    Let_static [Bind_deleted_code d]
      (Let 1%positive Value (Set_of_closures d []) Invalid)
  in
  let c := Closure (Handler [] (make_handler_metadata []) body) [] [] [] in
  expr_statics_in_scope [] [] body = true
  ∧ binds_statics body = false
  ∧ cont_free_of (Dropped [] [d]) c = false
  ∧ binds_no_static body = false.

(* ======================================================================== *)
(* Two exits that no observer tells apart                                   *)
(* ======================================================================== *)

(* The two exits are by the same continuation, and every observer,
   applied to the values of the first under its static environment and
   heap and to the values of the second under its own, comes to results
   that [observed_refines] relates. *)
Definition worlds_observed (slots : list value_slot) (w w' : exit_world)
    : Prop :=
  exit_cont w = exit_cont w'
  ∧ ∀ c : cont_value,
      observer slots c ->
      observed_refines
        (apply_cont_value c (exit_values w) (exit_statics w) (exit_heap w))
        (apply_cont_value c (exit_values w') (exit_statics w')
           (exit_heap w')).

(* The way out is an observer: so the two exits have the same constants
   and the same locations among their values, and their heaps bind the
   same locations, in the same order. *)
Definition worlds_observed_way_out_statement : Prop :=
  ∀ (slots : list value_slot) (w w' : exit_world),
    worlds_observed slots w w' ->
    exit_cont w = exit_cont w'
    ∧ same_scalars (exit_values w) (exit_values w')
    ∧ map fst (exit_heap w) = map fst (exit_heap w').

(* ======================================================================== *)
(* The form in which a pass proves it                                       *)
(* ======================================================================== *)

(* The two units, run from one continuation environment of observers,
   come to results that [observed_refines] relates, whatever the
   environment. *)
Definition refines_under_observers (slots : list value_slot)
    (statics : static_env) (hp : heap) (source target : expr) : Prop :=
  ∀ conts : cont_env,
    observers slots conts ->
    observed_refines (Step (State source [] conts statics hp))
      (Step (State target [] conts statics hp)).

(* Refinement under all environments gives it. *)
Definition expr_refines_under_observers_statement : Prop :=
  ∀ (slots : list value_slot) (statics : static_env) (hp : heap)
    (source target : expr),
    expr_refines source target ->
    refines_under_observers slots statics hp source target.

(* It composes. *)
Definition refines_under_observers_trans_statement : Prop :=
  ∀ (slots : list value_slot) (statics : static_env) (hp : heap)
    (e1 e2 e3 : expr),
    refines_under_observers slots statics hp e1 e2 ->
    refines_under_observers slots statics hp e2 e3 ->
    refines_under_observers slots statics hp e1 e3.

(* The two forms say the same of two units whose code is closed, from a
   static environment whose code is closed: the two units are so
   related from every continuation environment of observers exactly
   when, run on their own, an exit of the first is answered by an exit
   of the second that no observer tells apart from it, and the second
   ends only if the first exits or goes wrong. *)
Definition under_observers_worlds_statement : Prop :=
  ∀ (slots : list value_slot) (statics : static_env) (hp : heap)
    (source target : expr),
    code_closed source = true ->
    code_closed target = true ->
    static_code_closed statics ->
    (refines_under_observers slots statics hp source target
     <-> refines_world (worlds_observed slots)
           (State source [] [] statics hp)
           (State target [] [] statics hp)).
