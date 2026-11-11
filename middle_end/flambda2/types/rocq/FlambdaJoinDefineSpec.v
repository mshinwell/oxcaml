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


(* The last phase of the n-way join: the variables of the target are
   defined, and its equations are added.

   To be reviewed: every definition and statement of this file. The
   proofs are in FlambdaJoinDefineProofs.v.

   The phase is [define_or_eliminate_variables_and_add_equations]
   (FlambdaJoinEnv.v, after types/env/join_env.ml). It is given the
   state and the relations that the first phases leave
   ([first_phases_true_statement], FlambdaJoinStateSpec.v). It defines
   in the target the variables that the join has brought in; then, for
   each variable that the join has made: if a variable of the target is
   to be its alias, that one takes its place (its definition, its
   equation and its relations move to it, and the other aliases get an
   equation to it); if it is mentioned once and no relation is about it,
   it is removed, and its type is put where it was mentioned; otherwise
   it is defined. The equations, with the variables that have gone
   projected out of their types, are then added to the target through
   the environment of the meet, and after them the relations, as
   equations on the variables that hold their results.

   What is here:

   - The projection keeps what a type says
     ([project_variables_out_sound_statement], and the same of an
     environment extension): if, in a valuation, each variable that is
     projected out has the type that is put for it, a value of a type
     has the type with those variables projected out. The valuation
     gives values to the variables that are projected out: it is a
     valuation of the state of the join, and not only of the target.
   - The type that is put for a variable that goes
     ([expand_variable_sound_statement]): [Join_env.expand_variable]
     follows the types of the variables that go, and what it answers
     is true of the variable if each of those types is.
   - What the phase does and what it adds
     ([define_variables_true_statement]). The target that it answers
     is the environment given, with the variables brought in and some
     of the variables made defined in it, to which two environment
     extensions have been added: the equations, and those of the
     relations. At the run of an input, in the valuation of the target
     that the state gives ([target_valuation], FlambdaJoinStateSpec.v),
     every equation of the two is true of the value of its variable,
     where it has one, and the definitions answered hold. This is of
     the runs that have two conditions, below.
   - Of the relations given, the phase needs that no variable is kept
     with an empty list of them ([relations_nonempty]): the rounds
     keep that ([delayed_equations_relations_nonempty_statement],
     [loop_relations_nonempty_statement]), and start from no
     relation.
   - An extension asks more than that its equations are true where
     their names have values: each name is to have a value
     (FlambdaTypeMeaningSpec.v). [equations_true_with_values_statement]
     is the step from one to the other.

   The two conditions on a run, which nothing in the compiler
   establishes (there is a CR at each):

   - [aliases_have_values]: a variable of the target that is to be an
     alias of a variable that the join has made has a value where that
     one has. The state only knows the converse ([alias_holds]).
   - [relation_scrutinees_have_values]: where the variable that holds
     the result of a relation kept has a value, the variable that the
     relation is on has one.

   They are stated of the state of the join and of its valuation, and
   not of the target answered as the conditions of the contract are
   ([values_are_read], FlambdaJoinSpec.v). How the two sets are related
   is not stated here; see the CRs.

   Not here yet: that the two extensions fit the environment that they
   are added to (the variables of their types are variables of the
   target, at their kinds), which the functions of the meet's
   environment ask before they say anything; and the contract of the
   whole join. *)

From Stdlib Require Import ZArith List Bool PeanoNat.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeProject FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaTypingEnv
  FlambdaTypingEnvSpec FlambdaTypingEnvInvariantSpec
  FlambdaTypingEnvKindedSpec FlambdaJoinEnv FlambdaJoinSpec
  FlambdaJoinEnvSpec FlambdaJoinStateSpec.
Import ListNotations.

(* ======================================================================== *)
(* The projection of variables out of a type                                *)
(* ======================================================================== *)

(* In a valuation, each variable that is projected out and has a value
   has the type that is put for it. *)
Definition expansions_true (statics : static_env) (vars : env)
    (to_project : list variable) (expand : variable -> option flambda_type)
    : Prop :=
  ∀ (e : variable) (ty : flambda_type) (w : value),
    among e to_project = true ->
    expand e = Some ty ->
    lookup e vars = Some w ->
    type_satisfied statics vars w ty.

(* A value of a type has the type with the variables projected out. *)
Definition project_variables_out_sound_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (to_project : list variable)
    (expand : variable -> option flambda_type) (t t' : flambda_type)
    (v : value),
    expansions_true statics vars to_project expand ->
    project_variables_out to_project expand t = Some t' ->
    type_satisfied statics vars v t ->
    type_satisfied statics vars v t'.

(* The same of an environment extension. (The equations on the
   variables that are projected out are dropped.) *)
Definition project_env_extension_sound_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (to_project : list variable)
    (expand : variable -> option flambda_type)
    (extension extension' : env_extension),
    expansions_true statics vars to_project expand ->
    project_env_extension to_project expand extension = Some extension' ->
    env_extension_satisfied statics vars extension ->
    env_extension_satisfied statics vars extension'.

(* The type that [Join_env.expand_variable] answers for a variable is
   true of it, if the type kept for each variable is true of that
   variable. *)
Definition expand_variable_sound_statement : Prop :=
  ∀ (statics : static_env) (vars : env)
    (to_expand : finite_map flambda_type) (fuel : nat) (e : variable)
    (ty : flambda_type) (w : value),
    (∀ (e' : variable) (ty' : flambda_type) (w' : value),
       lookup e' to_expand = Some ty' ->
       lookup e' vars = Some w' ->
       type_satisfied statics vars w' ty') ->
    Join_env.expand_variable fuel to_expand e = Some ty ->
    lookup e vars = Some w ->
    type_satisfied statics vars w ty.

(* ======================================================================== *)
(* Two conditions on a run                                                  *)
(* ======================================================================== *)

(* At the run of an input, a variable of the target that is to be an
   alias of a variable that the join has made has a value where that
   one has. (It is then the same value: [alias_holds].) *)
(* CR mshinwell: nothing in the compiler establishes this. The
   variable that takes the place of a variable that the join has made
   gets its definition, and the others get an equation to it: so, on
   a run in which the vector of [Simple]s of the definition has a
   value at the input and the variable has none, the target asks of
   the variable a value that it has not. The variable is one of the
   source that has an equation in the level of every input, or one
   brought in from the inputs that know it, and the vector has a
   [Simple] exactly at the inputs that know the variable. So the
   condition is expected to follow from two of the conditions of the
   contract, [joined_variables_have_values] and
   [imported_variables_have_values] (FlambdaJoinSpec.v), which say
   that such a variable has a value at an input that knows it. That
   is not proved: the state of the join does not record at which
   inputs the vector of an alias has a [Simple], nor that an alias
   that the source knows has an equation in every level. Discrepancies
   T5-5 and T5-10. *)
Definition aliases_have_values (s : Join_env.t) (index : Index.t)
    (use : Typing_env.t) (valuation : env) : Prop :=
  ∀ (e x : variable) (v : value),
    x
    ∈ Aliases_of_existentials.aliases_of_existential_var
        (Join_env.aliases_of_existentials s) e ->
    lookup e (target_valuation s index use valuation) = Some v ->
    ∃ w : value, lookup x (target_valuation s index use valuation) = Some w.

(* At the run of an input, where the variable that holds the result of
   a relation kept has a value, the variable that the relation is on
   has one. *)
(* CR mshinwell: nothing in the compiler establishes this; it is
   [scrutinees_have_values] of FlambdaJoinSpec.v (see the CR there),
   asked of the relations that the join has kept and not of the
   relations that the target answered has. The two differ: the
   relations kept are added to the target by a meet, with the types
   that the target has already for the variables that hold their
   results, and a relation whose result has an alias or a constant
   for type there is not at the head of a type of the target
   afterwards, though the meet has used it. The condition here is the
   one that the proof needs, since the meet's environment is told
   that the equations added are true. Which of the two the contract
   should ask is open. Discrepancy T5-10. *)
Definition relation_scrutinees_have_values (s : Join_env.t)
    (relations : Join_env.inverse_relations) (index : Index.t)
    (use : Typing_env.t) (valuation : env) : Prop :=
  ∀ (r : variable) (relation : Relation.t) (x : variable) (v : value),
    relation_recorded relations r relation (Name_var x) ->
    lookup r (target_valuation s index use valuation) = Some v ->
    ∃ w : value, lookup x (target_valuation s index use valuation) = Some w.

(* ======================================================================== *)
(* What the phase does, and what it adds                                    *)
(* ======================================================================== *)

(* Every variable that holds the result of a relation kept has one
   kept for it. (The rounds add a relation to those kept for a
   variable, and start from none.) *)
Definition relations_nonempty (relations : Join_env.inverse_relations)
    : Prop :=
  ∀ (r : variable) (names : list (Relation.t * name)),
    lookup r relations = Some names -> names <> [].

(* The rounds keep it, whatever the join of types. *)
Definition delayed_equations_relations_nonempty_statement : Prop :=
  ∀ (fuel : nat) (choices : Join_env.choices)
    (jt : Join_env.n_way_join_type) (s s' : Join_env.t)
    (relations relations' : Join_env.inverse_relations)
    (equations : finite_map (Keyed.finite_map Index.t flambda_type)),
    relations_nonempty relations ->
    Join_env.n_way_join_delayed_equations fuel choices jt s relations
      equations
    = Some (relations', s') ->
    relations_nonempty relations'.

Definition loop_relations_nonempty_statement : Prop :=
  ∀ (depth : nat) (p : Join_env.parameters) (fuel : nat)
    (choices : Join_env.choices) (jt : Join_env.n_way_join_type)
    (s s' : Join_env.t) (relations relations' : Join_env.inverse_relations)
    (existentials : finite_map (Simples_in_joined_envs.t * flambda_kind)),
    relations_nonempty relations ->
    Join_env.n_way_join_loop depth p fuel choices jt s relations existentials
    = Some (relations', s') ->
    relations_nonempty relations'.

(* In a valuation, each equation of a list is true of the value of its
   name, where it has one. *)
Definition equations_true_at (statics : static_env) (vars : env)
    (equations : list (name * flambda_type)) : Prop :=
  ∀ (n : name) (ty : flambda_type) (v : value),
    (n, ty) ∈ equations ->
    value_of_name vars n = Some v ->
    type_satisfied statics vars v ty.

(* An extension is satisfied if its equations are true and each of its
   names has a value. *)
Definition equations_true_with_values_statement : Prop :=
  ∀ (statics : static_env) (vars : env)
    (equations : list (name * flambda_type)),
    equations_true_at statics vars equations ->
    (∀ (n : name) (ty : flambda_type),
       (n, ty) ∈ equations -> ∃ v : value, value_of_name vars n = Some v) ->
    env_extension_satisfied statics vars (Env_extension equations).

(* The environment of the meet in which variables have been defined,
   in order, each at its kind and at the name mode of the variables
   that exist only in types. *)
Definition variables_defined {meet_env meet_expanded_head : Type}
    (ops : Join_env.meet_env_functions meet_env meet_expanded_head)
    (menv : meet_env) (vars : list (variable * flambda_kind)) : meet_env :=
  List.fold_left
    (fun menv binding =>
       Join_env.add_variable_definition ops menv (fst binding) (snd binding)
         Name_mode.in_types)
    vars menv.

(* [define_or_eliminate_variables_and_add_equations], given a state
   that has the invariant and relations that are true of it. The
   target answered is made from the environment given by defining the
   variables brought in and some of the variables made, and adding two
   extensions. At the run of an input that has the two conditions
   above, and whose blocks have tags in range, each equation of the
   two extensions is true, in the valuation of the target that the
   state gives, of the value of its variable where it has one; and the
   definitions answered hold in that valuation. *)
Definition define_variables_true_statement : Prop :=
  ∀ (meet_env meet_expanded_head : Type)
    (ops : Join_env.meet_env_functions meet_env meet_expanded_head)
    (fuel : nat) (mh : meet_expanded_head) (source : Typing_env.t)
    (s : Join_env.t) (menv target : meet_env)
    (relations : Join_env.inverse_relations)
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind)),
    state_true source s ->
    state_kinded s ->
    joined_envs_are typing_env_kinded s ->
    relations_hold s relations ->
    relations_nonempty relations ->
    Join_env.define_or_eliminate_variables_and_add_equations ops fuel mh s
      menv relations
    = Some (target, definitions) ->
    ∃ (kept : list (variable * flambda_kind))
      (equations relation_equations : list (name * flambda_type))
      (menv' : meet_env),
      (∀ binding : variable * flambda_kind,
         binding ∈ kept ->
         binding
         ∈ Bindings_in_target_env.existential_variables_in_order
             (Join_env.bindings s))
      ∧ Join_env.add_env_extension ops
          (variables_defined ops menv
             (Bindings_in_target_env.imported_variables_in_order
                (Join_env.bindings s)
              ++ kept))
          (Env_extension equations) mh
        = Some menv'
      ∧ Join_env.add_env_extension ops menv' (Env_extension relation_equations)
          mh
        = Some target
      ∧ ∀ (index : Index.t) (use : Typing_env.t) (statics : static_env)
          (valuation : env),
          Join_env.joined_env s index = Some use ->
          typing_env_satisfied_strictly statics valuation use ->
          tags_at s use statics valuation ->
          aliases_have_values s index use valuation ->
          relation_scrutinees_have_values s relations index use valuation ->
          equations_true_at statics (target_valuation s index use valuation)
            equations
          ∧ equations_true_at statics
              (target_valuation s index use valuation) relation_equations
          ∧ definitions_hold definitions index valuation
              (target_valuation s index use valuation).
