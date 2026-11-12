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


(* The meet and its fuel: more fuel changes no answer.

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

   What is stated here is the first half of "some fuel is enough":
   an answer, once given, is the answer at every greater fuel.
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
   Nothing is supposed of the inputs, of the choices of the meet
   ([meet_choices]) or of the contract of the join.

   What is not here: that there is a fuel from which the answer does
   not change, so that a [None] there is not the fuel's. *)

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
