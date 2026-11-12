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

(* The slices of the [Switch] and the fuel of the meet: for the
   scrutinees and under the hypotheses below, the slices answer the
   same from one unit of fuel on, or from two.

   This file is to be reviewed: the definitions and the statements.
   The slices are those of FlambdaSimplifySwitchSpec.v,
   FlambdaSimplifySwitchArmsSpec.v and FlambdaSimplifySwitchMergeSpec.v.
   What it is for the fuel of the meet to be enough is
   FlambdaMeetTerminationSpec.v; the meet for an arm, for a scrutinee
   that is the result of a relation, is FlambdaMeetRelationFuelSpec.v.
   The proofs are in FlambdaSimplifySwitchFuelProofs.v, which needs no
   review.

   The slices take a meet as a parameter. The meet that the model has
   for the compiler's is defined by recursion on a number, the fuel,
   which the compiler's has not. So a slice applied to the model's
   meet depends on the fuel, and with too little of it may answer
   nothing: the meet answers nothing where the fuel runs out at a
   meet that it asks of itself. What is stated here is from which
   fuel on the slices no longer depend on it.

   What is stated.
   - [slices_of_agreeing_meets_statement]: the three slices ask one
     meet for each arm, that of the type which the environment
     answers for the scrutinee with the type of the number of the
     arm, and no other. So with two meets that answer the same on
     those ([arm_meets_agree]) each slice answers the same.
   - [flat_switch_fuel_statement]: for a scrutinee whose type is flat
     (a set of numbers, as the result of a comparison is; or a type
     that says nothing or has no value), the meets of every fuel from
     one unit on answer the same on those as the meet of one unit.
   - [relation_switch_fuel_statement]: for a scrutinee that is the
     result of relations ([Is_int], [Get_tag], [Is_null]; one, none or
     several),
     the meets of every fuel from two units on answer the same as the
     meet of two units, under what FlambdaMeetRelationFuelSpec.v
     supposes of the environment, of the choices of the meet and of
     the join.
   - [relation_switch_arm_keeps_statement]: under the same
     hypotheses, the environment that the meet for an arm answers has
     one of them again ([values_extension_free]): its types of kind
     value are aliases or have no extension. Its aliases are
     consistent, as those of the environment of the [Switch] are
     ([relation_switch_arm_keeps_aliases_statement]). What
     [scrutinee_has] asks of a scrutinee is not shown of it, so a
     [Switch] that is simplified in the environment of an arm still
     needs that.
   - [model_relation_switch_fuel_statement]: the same of the meet of
     the model (FlambdaJoinMeet.model_meet), whose join has what is
     supposed where there is fuel for the join of environments
     (FlambdaMeetDepthSpec.model_join_of_nothing_statement): for such
     a scrutinee, two meets of the model that differ in the fuel of
     the meet only, two units or more in both, answer the same.
   With the first, each slice applied to the meet of any such fuel is
   the slice applied to the meet of one unit, or of two.

   What is supposed of the scrutinee ([scrutinee_has]): the type that
   the environment answers for it is an alias whose canonical element,
   as the meet reads it, is a canonical name, and the type that the
   environment has for that name is flat ([flat_type]) or is a head of
   naked immediates, with whatever inverse relations
   ([relation_type]). The aliases of the environment are consistent,
   as in FlambdaMeetTerminationSpec.v. Both [scrutinee_has] and
   [arm_meets_agree] are about the type that the environment answers
   for the scrutinee, if it answers one: that it answers one is not
   said, and where it answers none the slices answer nothing, whatever
   the meet. A flat type may be of any kind; where it is not one of
   naked immediates, the two types that are met for an arm are of
   different kinds, and the meet answers the same at every fuel.

   An example ([example_switch_fuel_statement]): the environment after
   [let tag = Get_tag p] of FlambdaMeetExamplesSpec.v and a [Switch]
   on [tag]; the first slice answers the same from two units on,
   whatever the arms.

   What is not here: that the slices applied to the meet of that fuel
   answer what the compiler does (the places where the model of the
   meet is not the compiler's are listed in FlambdaMeet.v and
   FlambdaMeetEnv.v); a scrutinee whose type is neither flat nor a
   head of naked immediates (a head of values that is not flat), or
   for which the meet reads no canonical name (a constant); and the
   environments in which a type of kind value has an extension. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaCseSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaMeetGrammar
  FlambdaExpandHead FlambdaMeetEnv FlambdaMeet FlambdaMeetSpec
  FlambdaMeetTerminationSpec FlambdaMeetDepthSpec FlambdaMeetRelationFuelSpec
  FlambdaSimplifyPrimitivesSpec FlambdaSimplifySwitchSpec
  FlambdaSimplifySwitchArmsSpec FlambdaSimplifySwitchMergeSpec.
From OxCamlFlambda2Types Require FlambdaMeetExamplesSpec FlambdaJoinEnv
  FlambdaJoinMeet.
Import ListNotations.

(* ======================================================================== *)
(* The meets that the slices ask                                            *)
(* ======================================================================== *)

(* Two meets answer the same on the type that the environment answers
   for the scrutinee, if it answers one, and the type of each
   number. *)
Definition arm_meets_agree (meet meet' : meet_function) (tenv : Typing_env.t)
    (scrutinee : simple) : Prop :=
  ∀ (scrutinee_ty : flambda_type) (canonical : simple) (i : Z),
    Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal) scrutinee
    = Some (Some (scrutinee_ty, canonical)) ->
    meet tenv scrutinee_ty (this_naked_immediate i)
    = meet' tenv scrutinee_ty (this_naked_immediate i).

(* The three slices ask no other meet: with two meets that agree there
   they answer the same. *)
Definition slices_of_agreeing_meets_statement : Prop :=
  ∀ (meet meet' : meet_function) (rewrite : apply_cont_rewrite)
    (known : computed) (fresh : list variable) (tenv : Typing_env.t)
    (scrutinee : simple) (arms : list (Z * apply_cont)),
    arm_meets_agree meet meet' tenv scrutinee ->
    simplify_switch meet tenv scrutinee arms
    = simplify_switch meet' tenv scrutinee arms
    ∧ simplify_switch_arms meet rewrite tenv scrutinee arms
      = simplify_switch_arms meet' rewrite tenv scrutinee arms
    ∧ simplify_switch_merging meet rewrite known fresh tenv scrutinee arms
      = simplify_switch_merging meet' rewrite known fresh tenv scrutinee arms.

(* ======================================================================== *)
(* The scrutinees for which a fuel is known                                 *)
(* ======================================================================== *)

(* What the environment has for the scrutinee: the type that it answers
   for it, if it answers one, is an alias whose canonical element, as
   the meet reads it, is a canonical name, and the type of that name
   has [P]. *)
Definition scrutinee_has (P : flambda_type -> Prop) (tenv : Typing_env.t)
    (scrutinee : simple) : Prop :=
  ∀ (scrutinee_ty : flambda_type) (canonical : simple),
    Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal) scrutinee
    = Some (Some (scrutinee_ty, canonical)) ->
    ∃ (n : name) (ty : flambda_type),
      is_canonical (Typing_env.aliases tenv) (simple_of_name n)
      ∧ Typing_env.get_alias_then_canonical_simple_exn tenv
          (Some Name_mode.in_types) None scrutinee_ty
        = Some (Some (simple_of_name n))
      ∧ Typing_env.find tenv n (Some (kind scrutinee_ty)) = Some ty
      ∧ P ty.

(* The type of the scrutinee is flat: a set of numbers, or a type that
   says nothing or has no value. *)
Definition flat_type (ty : flambda_type) : Prop :=
  ∃ e : Expanded_type.t,
    Expanded_type.of_non_alias_type ty = Some e ∧ flat e = true.

(* The type of the scrutinee is that of the result of relations: a
   head of naked immediates, with the inverse relations that it
   has. *)
Definition relation_type (ty : flambda_type) : Prop :=
  ∃ head : head_of_kind_naked_immediate,
    ty = Type_naked_immediate (Ok (No_alias head)).

(* From one unit of fuel on, the meets for the arms are the same, for
   a scrutinee whose type is flat. *)
Definition flat_switch_fuel_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (tenv : Typing_env.t)
    (scrutinee : simple) (fuel : nat),
    aliases_consistent (Typing_env.aliases tenv) ->
    scrutinee_has flat_type tenv scrutinee ->
    1 <= fuel ->
    arm_meets_agree (Meet.meet join choices fuel) (Meet.meet join choices 1)
      tenv scrutinee.

(* From two units on, for a scrutinee that is the result of
   relations. *)
Definition relation_switch_fuel_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (tenv : Typing_env.t)
    (scrutinee : simple) (fuel : nat),
    join_of_nothing join ->
    get_tag_shapes choices ->
    values_extension_free tenv ->
    aliases_consistent (Typing_env.aliases tenv) ->
    scrutinee_has relation_type tenv scrutinee ->
    2 <= fuel ->
    arm_meets_agree (Meet.meet join choices fuel) (Meet.meet join choices 2)
      tenv scrutinee.

(* The environment that the meet for an arm answers has
   [values_extension_free], as the environment of the [Switch] has.
   Nothing is said of another scrutinee in it. *)
Definition relation_switch_arm_keeps_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices)
    (tenv tenv' : Typing_env.t) (scrutinee : simple) (fuel : nat)
    (scrutinee_ty ty : flambda_type) (canonical : simple) (i : Z),
    join_of_nothing join ->
    get_tag_shapes choices ->
    values_extension_free tenv ->
    aliases_consistent (Typing_env.aliases tenv) ->
    scrutinee_has relation_type tenv scrutinee ->
    2 <= fuel ->
    Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal) scrutinee
    = Some (Some (scrutinee_ty, canonical)) ->
    Meet.meet join choices fuel tenv scrutinee_ty (this_naked_immediate i)
    = Some (Or_bottom.Ok (ty, tenv')) ->
    values_extension_free tenv'.

(* And its aliases are consistent. *)
Definition relation_switch_arm_keeps_aliases_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices)
    (tenv tenv' : Typing_env.t) (scrutinee : simple) (fuel : nat)
    (scrutinee_ty ty : flambda_type) (canonical : simple) (i : Z),
    join_of_nothing join ->
    get_tag_shapes choices ->
    values_extension_free tenv ->
    aliases_consistent (Typing_env.aliases tenv) ->
    scrutinee_has relation_type tenv scrutinee ->
    2 <= fuel ->
    Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal) scrutinee
    = Some (Some (scrutinee_ty, canonical)) ->
    Meet.meet join choices fuel tenv scrutinee_ty (this_naked_immediate i)
    = Some (Or_bottom.Ok (ty, tenv')) ->
    aliases_consistent (Typing_env.aliases tenv').

(* The same of the meet of the model, where there is fuel for the join
   of environments: two meets of the model that differ in the fuel of
   the meet only, two units or more in both, answer the same for the
   arms. *)
Definition model_relation_switch_fuel_statement : Prop :=
  ∀ (join_choices : FlambdaJoinEnv.Join_env.choices) (choices : meet_choices)
    (join_depth : nat) (fuel fuel' : FlambdaJoinMeet.fuels)
    (tenv : Typing_env.t) (scrutinee : simple),
    FlambdaJoinMeet.fuel_of_env fuel <> 0%nat ->
    FlambdaJoinMeet.fuel_of_env fuel' = FlambdaJoinMeet.fuel_of_env fuel ->
    FlambdaJoinMeet.fuel_of_types fuel' = FlambdaJoinMeet.fuel_of_types fuel ->
    2 <= FlambdaJoinMeet.fuel_of_meet fuel ->
    2 <= FlambdaJoinMeet.fuel_of_meet fuel' ->
    get_tag_shapes choices ->
    values_extension_free tenv ->
    aliases_consistent (Typing_env.aliases tenv) ->
    scrutinee_has relation_type tenv scrutinee ->
    arm_meets_agree
      (FlambdaJoinMeet.model_meet join_choices choices join_depth fuel)
      (FlambdaJoinMeet.model_meet join_choices choices join_depth fuel')
      tenv scrutinee.

(* ======================================================================== *)
(* An example                                                               *)
(* ======================================================================== *)

(* The environment after [let tag = Get_tag p] of
   FlambdaMeetExamplesSpec.v, and a [Switch] on [tag]: the first slice
   answers the same from two units of fuel on, whatever the arms, with
   every join and all choices that have what is supposed of them. *)
Definition example_switch_fuel_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (fuel : nat)
    (arms : list (Z * apply_cont)),
    join_of_nothing join ->
    get_tag_shapes choices ->
    2 <= fuel ->
    simplify_switch (Meet.meet join choices fuel)
      FlambdaMeetExamplesSpec.example_get_tag_env
      (Var FlambdaMeetExamplesSpec.example_tag) arms
    = simplify_switch (Meet.meet join choices 2)
        FlambdaMeetExamplesSpec.example_get_tag_env
        (Var FlambdaMeetExamplesSpec.example_tag) arms.
