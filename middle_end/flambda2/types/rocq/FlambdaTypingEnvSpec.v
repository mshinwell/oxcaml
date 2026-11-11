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


(* HEADER TO COME *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaEnvAliasesSpec FlambdaTypingEnv.
Import ListNotations.

(* [kind_eqb] tells whether two kinds are the same. (To be the core's,
   with [kind_eqb]: see FlambdaTypingEnv.v.) *)
Definition kind_eqb_decides_equality_statement : Prop :=
  decides_equality kind_eqb.

(* ======================================================================== *)
(* What satisfies a typing environment                                      *)
(* ======================================================================== *)

(* A valuation is an environment of values, like the machine's, that is
   to give a value to every variable that a typing environment knows:
   also to those that have no value at run time. *)

(* What is asked of the value of a name whose type is [ty]: it is the
   poison constant of the kind of the type, and then nothing more is
   asked of it; or it has the type. *)
(* CR mshinwell: nothing is asked of the type of a name whose value is
   poison. That is a decision of the model, which the compiler does not
   state. Unboxing gives the parameters that stand for the fields of an
   inactive case of a variant their types on every path, and passes
   poison for them (simplify/unboxing/unboxing_epa.ml,
   build_unboxing_denv.ml). It relies on there being no strict use of
   such a parameter where it holds poison, and no meet of its type to
   bottom there; nothing checks either. Decision D26. *)
Definition satisfied_unless_poison (statics : static_env) (valuation : env)
    (v : value) (ty : flambda_type) : Prop :=
  v = Value_const (Poison (kind ty)) ∨ type_satisfied statics valuation v ty.

(* Every name that the typing environment has a type for has a value in
   the valuation, of that type unless it is poison. *)
Definition names_have_their_types (statics : static_env) (valuation : env)
    (tenv : Typing_env.t) : Prop :=
  ∀ (n : name) (ty : flambda_type)
    (binding_time_and_mode : Binding_time.With_name_mode.t),
    Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
    = Some (ty, binding_time_and_mode) ->
    ∃ v : value,
      value_of_name valuation n = Some v
      ∧ satisfied_unless_poison statics valuation v ty.

(* A valuation satisfies a typing environment: the environment is not
   bottom, its names have their types, and names that are aliases have
   the same value. *)
Definition typing_env_satisfied (statics : static_env) (valuation : env)
    (tenv : Typing_env.t) : Prop :=
  Typing_env.is_bottom tenv = false
  ∧ names_have_their_types statics valuation tenv
  ∧ aliases_respected (Typing_env.aliases tenv) valuation.

(* A variable may occur in a term simplified under the typing
   environment: it is bound there, with the normal name mode, and is not
   out of scope. This is the compiler's
   [Typing_env.mem ~min_name_mode:Name_mode.normal]. *)
Definition in_scope_in_terms (tenv : Typing_env.t) (x : variable) : Prop :=
  Typing_env.mem (Some Name_mode.normal) tenv (Name_var x) = true.

(* A valuation gives the variables that may occur in terms the values
   that the machine has for them. *)
Definition agrees_in_terms (tenv : Typing_env.t) (valuation vars : env)
    : Prop :=
  ∀ x : variable,
    in_scope_in_terms tenv x -> lookup x valuation = lookup x vars.

(* The static environment and the variables of a state of the machine
   satisfy a typing environment: some valuation satisfies it that gives
   the variables in scope the values that the machine has for them. The
   other variables of the typing environment (those of name mode
   [In_types] or [Phantom], and those that are out of scope) have the
   values that the valuation chooses, whatever the machine has. *)
Definition env_satisfies (tenv : Typing_env.t) (statics : static_env)
    (vars : env) : Prop :=
  ∃ valuation : env,
    typing_env_satisfied statics valuation tenv
    ∧ agrees_in_terms tenv valuation vars.

(* What is asked of a value fixes its kind, poison or not; and a value
   that is not poison has the type. *)
Definition satisfied_unless_poison_kind_statement : Prop :=
  ∀ (statics : static_env) (valuation : env) (v : value) (ty : flambda_type),
    satisfied_unless_poison statics valuation v ty ->
    kind_of_value v = kind ty.

Definition satisfied_unless_poison_not_poison_statement : Prop :=
  ∀ (statics : static_env) (valuation : env) (v : value) (ty : flambda_type),
    satisfied_unless_poison statics valuation v ty ->
    (∀ k : flambda_kind, v <> Value_const (Poison k)) ->
    type_satisfied statics valuation v ty.

(* ======================================================================== *)
(* What every environment satisfies, and what none does                     *)
(* ======================================================================== *)

(* The environment that knows nothing is satisfied by everything. *)
Definition create_satisfied_statement : Prop :=
  ∀ (statics : static_env) (vars : env),
    env_satisfies Typing_env.create statics vars.

(* An environment that is bottom is satisfied by nothing: a program
   point whose environment is bottom is not reached. *)
Definition bottom_not_satisfied_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars : env),
    Typing_env.is_bottom tenv = true -> ~ env_satisfies tenv statics vars.

Definition make_bottom_not_satisfied_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars : env),
    ~ env_satisfies (Typing_env.make_bottom tenv) statics vars.

(* The variables of the machine that give every name its type satisfy
   the environment: no other valuation need be found. *)
Definition typing_env_satisfied_env_satisfies_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars : env),
    typing_env_satisfied statics vars tenv -> env_satisfies tenv statics vars.

(* Whether the machine satisfies an environment depends only on the
   values of the variables in scope. *)
Definition env_satisfies_coincide_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars vars' : env),
    (∀ x : variable,
      in_scope_in_terms tenv x -> lookup x vars = lookup x vars') ->
    env_satisfies tenv statics vars ->
    env_satisfies tenv statics vars'.

(* ======================================================================== *)
(* Looking a name up                                                        *)
(* ======================================================================== *)

(* The type that the environment gives a name is the type of its value,
   unless that is poison, under a valuation that satisfies the
   environment. *)
Definition find_satisfied_statement : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t)
    (n : name) (kind : option flambda_kind) (ty : flambda_type),
    typing_env_satisfied statics valuation tenv ->
    Typing_env.find tenv n kind = Some ty ->
    ∃ v : value,
      value_of_name valuation n = Some v
      ∧ satisfied_unless_poison statics valuation v ty.

(* The type found is of the kind asked for. *)
Definition find_kind_statement : Prop :=
  ∀ (tenv : Typing_env.t) (n : name) (kind : flambda_kind)
    (ty : flambda_type),
    Typing_env.find tenv n (Some kind) = Some ty ->
    FlambdaTypeGrammar.kind ty = kind.

(* A name that is bound has a type. *)
Definition mem_find_statement : Prop :=
  ∀ (tenv : Typing_env.t) (min_name_mode : option Name_mode.t) (n : name),
    Typing_env.mem min_name_mode tenv n = true ->
    ∃ ty : flambda_type, Typing_env.find tenv n None = Some ty.

(* In the machine, a variable in scope has a value, of the kind of its
   type. *)
Definition in_scope_in_terms_bound_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars : env)
    (x : variable) (ty : flambda_type),
    env_satisfies tenv statics vars ->
    in_scope_in_terms tenv x ->
    Typing_env.find tenv (Name_var x) None = Some ty ->
    ∃ v : value,
      lookup x vars = Some v
      ∧ kind_of_value v = FlambdaTypeGrammar.kind ty.

(* The type of a variable in scope is the type of the value that the
   machine has for it, unless that is poison, if the type mentions only
   variables in scope. (A type that mentions others is about the values
   that the valuation gives them: [find_satisfied_statement].) *)
Definition find_variable_in_terms_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars : env)
    (x : variable) (kind : option flambda_kind) (ty : flambda_type),
    env_satisfies tenv statics vars ->
    in_scope_in_terms tenv x ->
    Typing_env.find tenv (Name_var x) kind = Some ty ->
    (∀ y : variable, y ∈ free_variables ty -> in_scope_in_terms tenv y) ->
    ∃ v : value,
      lookup x vars = Some v ∧ satisfied_unless_poison statics vars v ty.

(* The type of a symbol is the type of the pointer that the symbol is,
   which is not poison: it says what the static environment binds the
   symbol to. *)
Definition find_symbol_in_terms_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars : env) (s : symbol)
    (kind : option flambda_kind) (ty : flambda_type),
    env_satisfies tenv statics vars ->
    Typing_env.find tenv (Name_symbol s) kind = Some ty ->
    (∀ y : variable, y ∈ free_variables ty -> in_scope_in_terms tenv y) ->
    type_satisfied statics vars (Value_symbol s) ty.

(* ======================================================================== *)
(* Canonical elements                                                       *)
(* ======================================================================== *)

(* The canonical element of a [Simple] has the value of the [Simple]. *)
Definition canonical_ignoring_name_mode_satisfied_statement : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t)
    (s : simple),
    typing_env_satisfied statics valuation tenv ->
    eval_simple valuation
      (Typing_env.get_canonical_simple_ignoring_name_mode tenv s)
    = eval_simple valuation s.

Definition get_canonical_simple_satisfied_statement : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t)
    (min_name_mode name_mode_of_existing_simple : option Name_mode.t)
    (s canonical : simple),
    typing_env_satisfied statics valuation tenv ->
    Typing_env.get_canonical_simple_exn tenv min_name_mode
      name_mode_of_existing_simple s
    = Some (Some canonical) ->
    eval_simple valuation canonical = eval_simple valuation s.

(* The canonical element of the alias that a type is: a value of the
   type is the value of that element. *)
Definition get_alias_then_canonical_simple_satisfied_statement : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t)
    (min_name_mode name_mode_of_existing_simple : option Name_mode.t)
    (typ : flambda_type) (canonical : simple) (v : value),
    typing_env_satisfied statics valuation tenv ->
    Typing_env.get_alias_then_canonical_simple_exn tenv min_name_mode
      name_mode_of_existing_simple typ
    = Some (Some canonical) ->
    type_satisfied statics valuation v typ ->
    eval_simple valuation canonical = Some v.

(* The type of a [Simple] that occurs in a term: the [Simple] has a
   value, of the type, and the canonical element answered has the same
   value. *)
Definition type_simple_in_term_satisfied_statement : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t)
    (min_name_mode : option Name_mode.t) (s canonical : simple)
    (ty : flambda_type),
    typing_env_satisfied statics valuation tenv ->
    Typing_env.type_simple_in_term_exn tenv min_name_mode s
    = Some (Some (ty, canonical)) ->
    eval_simple valuation canonical = eval_simple valuation s
    ∧ ∃ v : value,
        eval_simple valuation s = Some v
        ∧ type_satisfied statics valuation v ty.

(* In the machine: a [Simple] of a term may be replaced by the canonical
   element that the environment answers for the normal name mode. This
   is what Simplify does to every [Simple]
   ([Simplify_simple.simplify_simple]). *)
Definition type_simple_in_term_canonical_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars : env)
    (s canonical : simple) (ty : flambda_type),
    env_satisfies tenv statics vars ->
    Typing_env.mem_simple (Some Name_mode.normal) tenv s = true ->
    Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal) s
    = Some (Some (ty, canonical)) ->
    eval_simple vars canonical = eval_simple vars s.
