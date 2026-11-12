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


(* The meet and its fuel.

   This file is to be reviewed: the definitions and the statements,
   which are about the functions of FlambdaMeet.v and FlambdaMeetEnv.v.
   The contract of the meet is FlambdaMeetSpec.v. The proofs are in
   FlambdaMeetTerminationProofs.v, which needs no review.

   The meet of expanded types is defined by recursion on a number, the
   fuel ([Meet.meet_expanded_head], FlambdaMeet.v): with no fuel it
   answers nothing, and with one more it is [meet_expanded_head_step]
   of the meet with one less. The compiler has no fuel: its meet is a
   recursive function, and nothing in it says why it ends. So a [None]
   of the model is a fatal error of the compiler, or the one state at
   which the model stops and the compiler does not (FlambdaMeetEnv.v,
   "A name that is no longer canonical"), or fuel that has run out; and
   the contract of the meet, which is about the answers that are not
   [None], says nothing of an input on which no fuel is enough.

   What is stated here is what can be said of the fuel without a
   bound on it. First, an answer, once given, is the answer at every
   greater fuel.
   - [meet_head_le mh mh']: wherever the meet of expanded types [mh]
     answers, [mh'] gives the same answer.
   - One step is monotone ([meet_expanded_head_step_monotone_statement]):
     the step of a meet that answers more answers more. The join that
     the meet is given takes the meet of less fuel too, so it is asked
     to be monotone in it ([join_monotone]); the join that forgets
     (FlambdaMeetExamplesSpec.v) is
     ([forgetful_join_monotone_statement]). That the compiler's join is
     monotone in its meet is not stated here.
   - So the meet of expanded types answers at a greater fuel what it
     answers at a lesser ([meet_expanded_head_fuel_monotone_statement]),
     and so do the meet of types ([meet_fuel_monotone_statement]),
     [Meet.meet_shape] ([meet_shape_fuel_monotone_statement]) and the
     functions that add to a typing environment
     ([typing_env_functions_fuel_monotone_statement]).
   - So an input has one answer at most, whatever the fuel
     ([meet_answer_unique_statement]).
   Nothing is supposed of the inputs, of the choices of the meet
   ([meet_choices]) or of the contract of the join.

   Second, what it is for the fuel to be enough, [None] included. A
   [None] of the model does not say whether the fuel ran out, so that
   cannot be said of the answers alone. The meet of no fuel answers
   [None] on every input; [meet_expanded_head_over] is the meet with
   any meet [mh0] in its place. The fuel is enough on an input
   ([fuel_enough], [meet_fuel_enough]) if the answer is the same
   whatever [mh0] is. That is a property of the answers and not of how
   the meet runs: it does not say that the meet never gets to the
   bottom of its fuel on that input (the join, which is any function
   here, may ask the meet that it is given and not use the answer),
   only that what is answered there makes no difference.
   - Where the fuel is enough, more fuel is enough and the answer is
     the same, [None] included ([fuel_enough_stable_statement],
     [meet_fuel_enough_stable_statement]). So a [None] at a fuel that
     is enough is a [None] at every greater fuel: more of this fuel
     does not remedy it. What it is otherwise is not said here: a
     fatal error of the compiler, the one state at which the model
     stops, or a [None] of the join, which where it is the transcribed
     join has fuel of its own. This supposes nothing of the join.
   - A fuel at which the meet answers is enough
     ([answer_fuel_enough_statement], [meet_answer_fuel_enough_statement]),
     for a join that is monotone.

   What is not here: a bound. That is, a number computed from the
   environment and the two types at which the fuel is enough,
   [meet_fuel_enough join choices (bound tenv t1 t2) tenv t1 t2], for
   the inputs that a meet may be given. With it and
   [meet_fuel_enough_stable_statement] the answer of the meet does not
   change from the bound on. No argument for it is written down in the
   compiler, and nothing here proves any part of what follows.

   What a proof would rest on. A meet of expanded types of less fuel
   is asked for in three ways: for two parts of the types in hand,
   which are smaller; for a type and the type that the environment has
   for a canonical name, where an equation is added to the name; and,
   where two canonical elements are made equal, for the type that the
   name demoted had and the type of the other, or the constant that
   the other is. In the second the name is among those that an
   equation is being added to until that meet answers
   ([Meet_env.adding_equation_for_name]), and an equation on such a
   name is passed over; in the third a name ceases to be canonical. So
   along the meets that are inside one another those of the second and
   third ways are no more than twice the names of the environment, and
   between two of them the types get smaller.

   What is in the way of a bound. The types of the environment change
   while the meet runs: a meet gives a name the type that it answers,
   and that type holds the extensions made from the equations added in
   the scopes of a disjunction, so it can be deeper than the two types
   met. And a join may define variables, which are new names; the join
   that forgets defines none. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaTypingEnv FlambdaMeetGrammar FlambdaExpandHead
  FlambdaMeetEnv FlambdaMeet FlambdaMeetSpec.
From OxCamlFlambda2Types Require FlambdaMeetExamplesSpec.
Import ListNotations.

(* ======================================================================== *)
(* A meet that answers more                                                 *)
(* ======================================================================== *)

(* Wherever [mh] answers, [mh'] gives the same answer. *)
Definition meet_head_le (mh mh' : meet_expanded_head) : Prop :=
  ∀ (menv : Meet_env.t) (e1 e2 : Expanded_type.t)
    (result : Meet_result.t Expanded_type.t),
    mh menv e1 e2 = Some result -> mh' menv e1 e2 = Some result.

(* A join answers the same with a meet that answers more. *)
Definition join_monotone (join : join_scoped_envs) : Prop :=
  ∀ (mh mh' : meet_expanded_head) (cut_after : Scope.t)
    (initial_env result : Meet_env.t) (initial_tenv : Typing_env.t)
    (scoped_envs : list Typing_env.t),
    meet_head_le mh mh' ->
    join mh cut_after initial_env initial_tenv scoped_envs = Some result ->
    join mh' cut_after initial_env initial_tenv scoped_envs = Some result.

Definition forgetful_join_monotone_statement : Prop :=
  join_monotone FlambdaMeetExamplesSpec.forgetful_join.

(* ======================================================================== *)
(* More fuel changes no answer                                              *)
(* ======================================================================== *)

(* One step. *)
Definition meet_expanded_head_step_monotone_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices)
    (mh mh' : meet_expanded_head),
    join_monotone join ->
    meet_head_le mh mh' ->
    meet_head_le (meet_expanded_head_step join choices mh)
      (meet_expanded_head_step join choices mh').

(* The meet of expanded types. *)
Definition meet_expanded_head_fuel_monotone_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel fuel' : nat),
    join_monotone join ->
    fuel <= fuel' ->
    meet_head_le (Meet.meet_expanded_head join choices fuel)
      (Meet.meet_expanded_head join choices fuel').

(* The meet of types. *)
Definition meet_fuel_monotone_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel fuel' : nat)
    (tenv : Typing_env.t) (t1 t2 : flambda_type)
    (result : Or_bottom.t (flambda_type * Typing_env.t)),
    join_monotone join ->
    fuel <= fuel' ->
    Meet.meet join choices fuel tenv t1 t2 = Some result ->
    Meet.meet join choices fuel' tenv t1 t2 = Some result.

Definition meet_shape_fuel_monotone_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel fuel' : nat)
    (tenv : Typing_env.t) (t shape : flambda_type)
    (result : Or_bottom.t Typing_env.t),
    join_monotone join ->
    fuel <= fuel' ->
    Meet.meet_shape join choices fuel tenv t shape = Some result ->
    Meet.meet_shape join choices fuel' tenv t shape = Some result.

(* An input has one answer at most, whatever the fuel. *)
Definition meet_answer_unique_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel fuel' : nat)
    (tenv : Typing_env.t) (t1 t2 : flambda_type)
    (result result' : Or_bottom.t (flambda_type * Typing_env.t)),
    join_monotone join ->
    Meet.meet join choices fuel tenv t1 t2 = Some result ->
    Meet.meet join choices fuel' tenv t1 t2 = Some result' ->
    result = result'.

(* The functions that add to a typing environment
   (types/flambda2_types.ml). *)
Definition typing_env_functions_fuel_monotone_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel fuel' : nat)
    (tenv tenv' : Typing_env.t),
    join_monotone join ->
    fuel <= fuel' ->
    (∀ (n : name) (ty : flambda_type),
      Flambda2_types.add_equation join choices fuel tenv n ty = Some tenv' ->
      Flambda2_types.add_equation join choices fuel' tenv n ty = Some tenv')
    ∧ (∀ extension : env_extension,
        Flambda2_types.add_env_extension join choices fuel tenv extension
        = Some tenv' ->
        Flambda2_types.add_env_extension join choices fuel' tenv extension
        = Some tenv')
    ∧ (∀ (params : list (variable * flambda_kind))
         (param_types : list flambda_type),
        Flambda2_types.add_equations_on_params join choices fuel tenv params
          param_types
        = Some tenv' ->
        Flambda2_types.add_equations_on_params join choices fuel' tenv params
          param_types
        = Some tenv')
    ∧ (∀ (n : name) (scrutinee : simple) (name_ty : flambda_type)
         (scrutinee_head : variable -> head_of_kind_value),
        Flambda2_types.add_relation join choices fuel tenv n scrutinee name_ty
          scrutinee_head
        = Some tenv' ->
        Flambda2_types.add_relation join choices fuel' tenv n scrutinee
          name_ty scrutinee_head
        = Some tenv').

(* ======================================================================== *)
(* A fuel that is enough                                                    *)
(* ======================================================================== *)

(* The meet of expanded types, with the meet [mh0] where the fuel runs
   out. *)
Fixpoint meet_expanded_head_over (join : join_scoped_envs)
    (choices : meet_choices) (mh0 : meet_expanded_head) (fuel : nat)
    : meet_expanded_head :=
  match fuel with
  | O => mh0
  | S fuel =>
    meet_expanded_head_step join choices
      (meet_expanded_head_over join choices mh0 fuel)
  end.

(* [Meet.meet_expanded_head] is that, over the meet that answers
   nothing. *)
Definition meet_expanded_head_over_none_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel : nat),
    meet_expanded_head_over join choices (fun _ _ _ => None) fuel
    = Meet.meet_expanded_head join choices fuel.

(* The fuel is enough for the meet of two expanded types: the answer
   is the same whatever is answered where the fuel runs out. *)
Definition fuel_enough (join : join_scoped_envs) (choices : meet_choices)
    (fuel : nat) (menv : Meet_env.t) (e1 e2 : Expanded_type.t) : Prop :=
  ∀ mh0 : meet_expanded_head,
    meet_expanded_head_over join choices mh0 fuel menv e1 e2
    = Meet.meet_expanded_head join choices fuel menv e1 e2.

(* The same for the meet of two types ([Meet.meet], which is made of
   [Meet_env.meet_type] in the environment of the meet). *)
Definition meet_fuel_enough (join : join_scoped_envs)
    (choices : meet_choices) (fuel : nat) (tenv : Typing_env.t)
    (t1 t2 : flambda_type) : Prop :=
  ∀ mh0 : meet_expanded_head,
    Meet_env.meet_type (Meet_env.create tenv) t1 t2
      (meet_expanded_head_over join choices mh0 fuel)
    = Meet_env.meet_type (Meet_env.create tenv) t1 t2
        (Meet.meet_expanded_head join choices fuel).

(* Where the fuel is enough, more fuel is enough, and the answer is the
   same, [None] included. *)
Definition fuel_enough_stable_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel fuel' : nat)
    (menv : Meet_env.t) (e1 e2 : Expanded_type.t),
    fuel_enough join choices fuel menv e1 e2 ->
    fuel <= fuel' ->
    fuel_enough join choices fuel' menv e1 e2
    ∧ Meet.meet_expanded_head join choices fuel' menv e1 e2
      = Meet.meet_expanded_head join choices fuel menv e1 e2.

Definition meet_fuel_enough_stable_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel fuel' : nat)
    (tenv : Typing_env.t) (t1 t2 : flambda_type),
    meet_fuel_enough join choices fuel tenv t1 t2 ->
    fuel <= fuel' ->
    meet_fuel_enough join choices fuel' tenv t1 t2
    ∧ Meet.meet join choices fuel' tenv t1 t2
      = Meet.meet join choices fuel tenv t1 t2.

(* A fuel at which the meet answers is enough. *)
Definition answer_fuel_enough_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel : nat)
    (menv : Meet_env.t) (e1 e2 : Expanded_type.t)
    (result : Meet_result.t Expanded_type.t),
    join_monotone join ->
    Meet.meet_expanded_head join choices fuel menv e1 e2 = Some result ->
    fuel_enough join choices fuel menv e1 e2.

(* (In an environment that is bottom [Meet.meet] answers bottom at
   every fuel and makes no meet of types.) *)
Definition meet_answer_fuel_enough_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel : nat)
    (tenv : Typing_env.t) (t1 t2 : flambda_type)
    (result : Or_bottom.t (flambda_type * Typing_env.t)),
    join_monotone join ->
    Typing_env.is_bottom tenv = false ->
    Meet.meet join choices fuel tenv t1 t2 = Some result ->
    meet_fuel_enough join choices fuel tenv t1 t2.
