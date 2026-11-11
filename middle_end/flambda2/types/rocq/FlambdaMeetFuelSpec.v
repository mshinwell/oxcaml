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

(* The meet of expanded types at every fuel, and the meet of types.

   This file is to be reviewed: the statements, which are about
   [meet_expanded_head_step], [Meet.meet_expanded_head] and [Meet.meet]
   of FlambdaMeet.v. The proofs are in FlambdaMeetFuelProofs.v, which
   needs no review.

   The meet of expanded types is defined by recursion on a number, the
   fuel: with no fuel it answers nothing, and with one more it is
   [meet_expanded_head_step] of the meet with one less. The contract
   of FlambdaMeetSpec.v is proved of it in the same way.

   - One step ([meet_expanded_head_step_ok_statement]). If the meet of
     less fuel has its contracts ([meet_expanded_head_keeps],
     [meet_expanded_head_sound], and [meet_expanded_head_other_kinds]
     of FlambdaMeetImmediateSpec.v), the step of it has the first
     two. Two things are supposed. The type of the [Get_tag] step is
     the one that is true (FlambdaMeetSpec.v). And the meet of two
     heads of kind value is right ([value_heads_right]): that is the
     part of the meet that goes through variants, row-like structures
     and closures, with the join of scoped environments; it is stated
     and proved apart, from the join's contract, and is a hypothesis
     here.
   - Every fuel ([meet_expanded_head_fuel_ok_statement]): if every
     meet that has its contracts makes the meet of two heads of kind
     value right, the meet of expanded types has its contracts at
     every fuel.
   - The meet of types ([meet_of_fuel_contract_statement]): if the
     meet of expanded types of some fuel has its contracts, [Meet.meet]
     of that fuel has [meet_contract].

   - The functions that add to a typing environment
     ([typing_env_functions_sound_statement]): at such a fuel,
     [Typing_env.add_env_extension] of flambda2_types.ml has its
     contract of FlambdaMeetSpec.v, and [Typing_env.add_equation] and
     [Typing_env.add_equations_on_params] have theirs for names that
     the environment knows. The contracts of FlambdaMeetSpec.v do not
     suppose that the name is known; what is missing is said below.

   What is not here: that some fuel is enough (a meet that runs out
   of fuel answers nothing, and the contracts say nothing of it). *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaClosuresSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaMeetGrammar FlambdaExpandHead FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec FlambdaMeetStepsSpec FlambdaMeetImmediateSpec.
Import ListNotations.

(* The meet of two heads of kind value is right, for every value: a
   head fits an environment, and is true of the value in hand, as the
   type that it makes does. *)
Definition value_heads_right (join : join_scoped_envs)
    (choices : meet_choices) (mh : meet_expanded_head) : Prop :=
  ∀ v : value,
    part_meet_ok
      (fun (tenv : Typing_env.t) (head : head_of_kind_value) =>
         type_fits tenv (Type_value (Ok (No_alias head))))
      (fun (statics : static_env) (valuation : env)
           (head : head_of_kind_value) =>
         type_satisfied statics valuation v (Type_value (Ok (No_alias head))))
      (meet_head_of_kind_value join choices mh).

(* One step: the meet of expanded types made of a meet that has its
   contracts has the two of FlambdaMeetSpec.v. *)
Definition meet_expanded_head_step_ok_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices)
    (mh : meet_expanded_head),
    type_of_get_tag_scrutinee choices = immediate_or_blocks_with_these_tags ->
    meet_expanded_head_keeps mh ->
    meet_expanded_head_sound mh ->
    meet_expanded_head_other_kinds mh ->
    value_heads_right join choices mh ->
    meet_expanded_head_keeps (meet_expanded_head_step join choices mh)
    ∧ meet_expanded_head_sound (meet_expanded_head_step join choices mh).

(* Every fuel. *)
Definition meet_expanded_head_fuel_ok_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices),
    type_of_get_tag_scrutinee choices = immediate_or_blocks_with_these_tags ->
    (∀ mh : meet_expanded_head,
       meet_expanded_head_keeps mh ->
       meet_expanded_head_sound mh ->
       meet_expanded_head_other_kinds mh ->
       value_heads_right join choices mh) ->
    ∀ fuel : nat,
      meet_expanded_head_keeps (Meet.meet_expanded_head join choices fuel)
      ∧ meet_expanded_head_sound (Meet.meet_expanded_head join choices fuel).

(* The meet of types has its contract, at a fuel at which the meet of
   expanded types has its own. *)
Definition meet_of_fuel_contract_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel : nat),
    meet_expanded_head_keeps (Meet.meet_expanded_head join choices fuel) ->
    meet_expanded_head_sound (Meet.meet_expanded_head join choices fuel) ->
    meet_contract (Meet.meet join choices fuel).

(* The three together, for the meet that is to be proved
   ([meet_to_prove], FlambdaMeetSpec.v): it has its contract at every
   fuel, if the meet of two heads of kind value is right with every
   meet of expanded types that has its contracts. *)
Definition meet_to_prove_contract_statement : Prop :=
  ∀ join : join_scoped_envs,
    (∀ mh : meet_expanded_head,
       meet_expanded_head_keeps mh ->
       meet_expanded_head_sound mh ->
       meet_expanded_head_other_kinds mh ->
       value_heads_right join repaired_choices mh) ->
    ∀ fuel : nat, meet_contract (meet_to_prove join fuel).

(* ======================================================================== *)
(* Adding to a typing environment                                           *)
(* ======================================================================== *)

(* [add_equation_sound] (FlambdaMeetSpec.v) for a name that the
   environment knows. *)
(* CR mshinwell: the contract of FlambdaMeetSpec.v does not suppose
   that the environment knows the name, and what is proved supposes
   it. The statements about [Meet_env.add_equation]
   (FlambdaMeetEnvSpec.v) suppose that the name is of the kind of the
   type. For a name that the environment knows that follows from the
   other premises: the name has a value, of the type given and of the
   type that the environment has for it. For a name that it does not
   know it does not, and the proof would be that the function does
   not answer (it reads the type of the name); that is done where the
   type is not an alias (FlambdaMeetImmediateProofs.v) and not where
   it is one. Simplify adds equations on names that it has defined.
   Either the contract takes the premise, or the case is proved. *)
Definition add_equation_sound_where_known
    (add_equation : add_equation_function) : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv tenv' : Typing_env.t)
    (n : name) (ty : flambda_type) (v : value),
    typing_env_fits tenv ->
    type_fits tenv ty ->
    Typing_env.mem None tenv n = true ->
    statics_valid statics ->
    typing_env_satisfied_strictly statics valuation tenv ->
    value_of_name valuation n = Some v ->
    type_satisfied statics valuation v ty ->
    add_equation tenv n ty = Some tenv' ->
    ∃ valuation' : env,
      extended_from tenv valuation valuation'
      ∧ typing_env_satisfied_strictly statics valuation' tenv'
      ∧ keeps_equations_valued tenv tenv' valuation valuation'.

(* [add_equations_on_params_sound] (FlambdaMeetSpec.v) for parameters
   that the environment knows. *)
Definition add_equations_on_params_sound_where_known
    (add_equations_on_params : add_equations_on_params_function) : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv tenv' : Typing_env.t)
    (params : list (variable * flambda_kind))
    (param_types : list flambda_type),
    typing_env_fits tenv ->
    (∀ ty : flambda_type, ty ∈ param_types -> type_fits tenv ty) ->
    (∀ param : variable * flambda_kind,
       param ∈ params ->
       Typing_env.mem None tenv (Name_var (fst param)) = true) ->
    statics_valid statics ->
    typing_env_satisfied_strictly statics valuation tenv ->
    Forall2
      (fun (param : variable * flambda_kind) (ty : flambda_type) =>
         ∃ v : value,
           lookup (fst param) valuation = Some v
           ∧ type_satisfied statics valuation v ty)
      params param_types ->
    add_equations_on_params tenv params param_types = Some tenv' ->
    ∃ valuation' : env,
      extended_from tenv valuation valuation'
      ∧ typing_env_satisfied_strictly statics valuation' tenv'
      ∧ keeps_equations_valued tenv tenv' valuation valuation'.

(* The three functions, at a fuel at which the meet of expanded types
   has its contracts. *)
Definition typing_env_functions_sound_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel : nat),
    meet_expanded_head_keeps (Meet.meet_expanded_head join choices fuel) ->
    meet_expanded_head_sound (Meet.meet_expanded_head join choices fuel) ->
    add_equation_sound_where_known
      (Flambda2_types.add_equation join choices fuel)
    ∧ add_env_extension_sound
        (Flambda2_types.add_env_extension join choices fuel)
    ∧ add_equations_on_params_sound_where_known
        (Flambda2_types.add_equations_on_params join choices fuel).
