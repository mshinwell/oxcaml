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


(* The types of the equations that the join adds fit the environment
   of the meet: what FlambdaJoinMeetSpec.v leaves as a premise
   ([types_fit_otherwise], [join_adds_types_that_fit_otherwise]) is
   true of the join put together in FlambdaJoinMeet.v.

   This file is to be reviewed: the statements. The proofs are in
   FlambdaJoinMeetFitsProofs.v, which needs no review.

   An extension that the environment of the meet is given is supposed
   to have types that are well formed and in which the names of the
   equations inside them are of the kinds of their types
   ([type_fits], FlambdaMeetSpec.v, with the variables and the aliases
   that FlambdaJoinMeetSpec.v has). Of the two extensions that the
   last phase of the join adds:

   - the types are well formed: FlambdaJoinWellFormedSpec.v, for the
     state that the first phases answer and for what the last phase
     makes of it;
   - the names of the equations inside the types are of their kinds
     in the target, by the kinds that the bindings of the state
     record: FlambdaJoinEquationNamesSpec.v. Here: so they are in the
     environment of the meet in which the variables of the target
     are defined ([last_phase_equation_names_known_statement]), as
     [last_phase_kinds_known_statement] (FlambdaJoinMeetSpec.v) says
     of the aliases, and under its premises;
   - so the join that the meet calls adds types that fit otherwise
     ([model_join_adds_types_that_fit_otherwise_statement]), and has
     the conclusions of the contract that the meet has for its join
     that are not about values, with no premise left about the join
     itself ([model_join_scoped_envs_keeps_outright_statement]:
     [model_join_scoped_envs_keeps_statement] of FlambdaJoinMeetSpec.v
     with its premise discharged). The same of the conclusion about
     values that FlambdaJoinMeetSpec.v has on the runs that have its
     conditions ([model_join_scoped_envs_satisfied_outright_statement]:
     [model_join_scoped_envs_satisfied_statement] with its premise
     about the join discharged, and nothing else changed).

   The expansion of heads that the join of types is given has what
   the join of types supposes of it for the names of equations
   ([expand_head_for_join_equations_kinded_statement]). *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaClosuresSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeWellFormedSpec FlambdaBindingTime
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvInvariantSpec
  FlambdaTypingEnvKindedSpec FlambdaJoinEnv FlambdaJoinSpec
  FlambdaJoinEnvSpec FlambdaJoinStateSpec FlambdaJoinDefineSpec
  FlambdaJoinFitsSpec FlambdaJoinAddsSpec FlambdaJoinKindsSpec
  FlambdaJoinTypes FlambdaJoinTypesSpec FlambdaMeetGrammar FlambdaMeetEnv
  FlambdaMeet FlambdaMeetSpec FlambdaMeetStepsSpec FlambdaMeetEnvSpec
  FlambdaJoinMeet FlambdaJoinMeetSpec FlambdaJoinEquationNamesSpec.
Import ListNotations.

(* The expansion of heads that the join of types is given in
   FlambdaJoinMeet.v keeps the names of the equations inside a type
   at their kinds. *)
Definition expand_head_for_join_equations_kinded_statement : Prop :=
  FlambdaJoinTypesSpec.expand_head_equations_kinded expand_head_for_join.

(* The names of the equations inside the types of the equations that
   the last phase adds are of their kinds in the environment in which
   the variables are defined. The premises are those of
   [last_phase_kinds_known_statement] (FlambdaJoinMeetSpec.v), with
   [equation_names_kinded] (FlambdaJoinEquationNamesSpec.v) of the
   state where that has the kinds of its aliases. *)
Definition last_phase_equation_names_known_statement : Prop :=
  ∀ (tenv : Typing_env.t) (fuel : nat) (source : Typing_env.t)
    (s : Join_env.t) (relations : Join_env.inverse_relations)
    (menv : Meet_env.t) (kept : list (variable * flambda_kind))
    (equations relation_equations : list (name * flambda_type))
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind)),
    state_true source s ->
    relations_hold s relations ->
    relations_nonempty relations ->
    state_scoped s ->
    state_kinded s ->
    joined_envs_are typing_env_invariant s ->
    joined_envs_are typing_env_kinded s ->
    symbols_of_joined_envs_in_source source s ->
    equation_names_kinded s ->
    Meet_env.typing_env menv = source ->
    typing_env_fits (Meet_env.typing_env menv) ->
    last_phase_adds tenv fuel s relations kept equations relation_equations
      definitions ->
    let menv' :=
      variables_defined meet_env_functions menv
        (Bindings_in_target_env.imported_variables_in_order
           (Join_env.bindings s)
         ++ kept)
    in
    ∀ (n : name) (ty : flambda_type),
      (n, ty) ∈ equations ++ relation_equations ->
      type_equations_kinded (Meet_env.typing_env menv') ty.

(* The join that the meet calls adds types that fit otherwise. *)
Definition model_join_adds_types_that_fit_otherwise_statement : Prop :=
  ∀ (join_choices : Join_env.choices) (join_depth : nat) (fuel : fuels),
    join_adds_types_that_fit_otherwise join_choices join_depth fuel.

(* So it has the conclusions of the contract that the meet has for
   its join that are not about values. *)
Definition model_join_scoped_envs_keeps_outright_statement : Prop :=
  ∀ (join_choices : Join_env.choices) (join_depth : nat) (fuel : fuels),
    join_scoped_envs_keeps
      (model_join_scoped_envs join_choices join_depth fuel).

(* And it has the conclusion of that contract about values, on the
   runs that have the conditions of FlambdaJoinMeetSpec.v: the
   statement there ([model_join_scoped_envs_satisfied_statement]),
   word for word, without its premise about the join. *)
Definition model_join_scoped_envs_satisfied_outright_statement : Prop :=
  ∀ (join_choices : Join_env.choices) (join_depth : nat) (fuel : fuels)
    (meet_head : meet_expanded_head) (initial_env result : Meet_env.t)
    (scoped_envs : list Typing_env.t) (envs : Joined_envs.t)
    (s1 s2 s3 : Join_env.t)
    (relations2 relations3 : Join_env.inverse_relations)
    (kept : list (variable * flambda_kind))
    (equations relation_equations : list (name * flambda_type))
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) (scoped_env : Typing_env.t) (statics : static_env)
    (valuation : env),
    let initial_tenv := Meet_env.typing_env initial_env in
    let p := join_parameters join_depth in
    let jt := model_join_of_types join_depth fuel in
    let avoid :=
      Meet_env.names_to_avoid initial_env
      ++ Join_env.variables_of_env initial_tenv
      ++ flat_map Join_env.variables_of_env scoped_envs
    in
    let s0 :=
      Join_env.create envs
        (Bindings_in_target_env.from_source_env avoid initial_tenv)
    in
    let menv :=
      Meet_env.with_names_to_avoid initial_env
        (Bindings_in_target_env.names_to_avoid (Join_env.bindings s3))
    in
    meet_expanded_head_sound meet_head ->
    meet_expanded_head_keeps meet_head ->
    typing_env_fits initial_tenv ->
    (∀ scoped_env : Typing_env.t,
      scoped_env ∈ scoped_envs -> scoped_env_of initial_tenv scoped_env) ->
    scoped_envs_agree scoped_envs ->
    model_join_scoped_envs join_choices join_depth fuel meet_head
      (Typing_env.current_scope initial_tenv) initial_env initial_tenv
      scoped_envs
    = Some result ->
    Join_env.cut_for_joins (Typing_env.current_scope initial_tenv)
      (Index.number scoped_envs)
    = Some envs ->
    Join_env.join_aliases_into_bindings p (fuel_of_env fuel) s0 envs
    = Some s1 ->
    Join_env.n_way_join_delayed_equations (fuel_of_env fuel) join_choices jt
      s1 [] (Join_env.new_equations_in_joined_envs s1 s0)
    = Some (relations2, s2) ->
    Join_env.n_way_join_loop join_depth p (fuel_of_env fuel) join_choices jt
      s2 relations2 (Join_env.new_definitions_of_existentials s2 s0)
    = Some (relations3, s3) ->
    last_phase_adds
      (Meet_env.typing_env
         (variables_defined meet_env_functions menv
            (Bindings_in_target_env.imported_variables_in_order
               (Join_env.bindings s3))))
      (fuel_of_env fuel) s3 relations3 kept equations relation_equations
      definitions ->
    Join_env.joined_env s3 index = Some scoped_env ->
    statics_valid statics ->
    typing_env_satisfied_strictly statics valuation initial_tenv ->
    typing_env_satisfied_strictly statics valuation scoped_env ->
    tags_at s3 scoped_env statics valuation ->
    aliases_have_values s3 index scoped_env valuation ->
    relation_scrutinees_have_values s3 relations3 index scoped_env valuation
    ->
    (∀ (n : name) (ty : flambda_type),
       (n, ty) ∈ equations ++ relation_equations ->
       ∃ v : value,
         value_of_name (target_valuation s3 index scoped_env valuation) n
         = Some v) ->
    ∃ valuation' : env,
      extended_from scoped_env valuation valuation'
      ∧ typing_env_satisfied_strictly statics valuation'
          (Meet_env.typing_env result)
      ∧ keeps_equations_valued initial_tenv (Meet_env.typing_env result)
          valuation valuation'.
