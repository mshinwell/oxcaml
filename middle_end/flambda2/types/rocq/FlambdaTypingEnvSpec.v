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


(* What it is for the values of a run to satisfy a typing environment,
   and what looking a name up in the environment says of its value.

   This file is to be reviewed: [typing_env_satisfied] and
   [env_satisfies], with what they are made of, and the statements.
   Every later statement about types that is relative to an environment
   (meet, join, the provers, the rewrites of Simplify) takes one of the
   two as a premise. So they have to be true of the environments that
   Simplify builds, or those statements say nothing of real programs;
   and strong enough that the type found for a name is a fact about its
   value. The environment itself is FlambdaTypingEnv.v, which is to be
   read against middle_end/flambda2/types/env/typing_env.ml; what a
   type means is FlambdaTypeMeaningSpec.v; the aliases are
   FlambdaEnvAliasesSpec.v. Examples, with environments of the machine
   that do and do not satisfy an environment, are
   FlambdaTypingEnvExamplesSpec.v.

   The compiler has no such definition to compare with. What an
   environment means there is what its users take it to mean, and those
   are what to read this against: [Typing_env.find] and
   [type_simple_in_term_exn] as Simplify calls them
   (simplify/simplify_simple.ml), [Expand_head.expand_head] and the
   provers; how Simplify extends the environment as it goes under
   binders (simplify/env/downwards_env.ml: [define_variable],
   [add_variable], [add_parameters], [enter_set_of_closures]); and how
   the environment of a handler is made from those of its uses
   (simplify/join_points.ml, types/join_levels_old.ml and
   types/env/join_env.ml).

   Valuations. An environment knows variables that have no value where
   the term runs:
   - those of name mode [In_types]: the variables that a join makes
     existential ([Meet_env.add_env_extension_from_level], and the
     n-way join, which defines them with
     [add_variable_definition ... In_types]), and those of an extension
     with extra variables. Such a variable stands for the value that a
     variable bound in the body of a [Let_cont] had at the use that
     jumped to the handler;
   - those of name mode [Phantom], which are for debugging information;
   - those that are out of scope. In the body of a function the
     environment is that of the place where the closure is made, with
     [min_binding_time] moved to the present
     ([Typing_env.closure_env]): its variables are still there, and
     the types of the value slots are aliases to them, but the machine
     runs the body with the parameters and the closure and nothing
     else. Such a variable stands for the value it had where the
     closure was made.
   So an environment is satisfied by a valuation: an environment of
   values, like the machine's, that gives a value to every variable the
   typing environment knows ([typing_env_satisfied]). The machine
   satisfies a typing environment when some valuation does that agrees
   with the machine on the variables in scope ([env_satisfies]). Which
   variables are in scope is the compiler's own test
   ([in_scope_in_terms]). Statements about types (meet, join, the
   provers) are to be made of valuations, as the types of an
   environment mention variables that are not in scope; statements
   about terms are to be made of the machine. FlambdaTypeMeaningSpec.v
   needs nothing else of the environment, and what it calls [vars] is
   the valuation.

   What it is to satisfy an environment, and what was decided.
   - Names. Every name that has a type ([names_to_types]) has a value
     in the valuation, and the value has the type
     ([names_have_their_types]). The type of a name is the one that this
     map has for it: the one that the last [replace_equation] gave it.
     The equations of the levels are the history of the environment and
     are not read. A value that has a type has the kind of the type
     (FlambdaTypeMeaningSpec.v), so every name has a value of its kind.
   - A name with no value at run time has one in the valuation, and
     that is all: the machine may have no value for it, or another.
   - Symbols. A symbol is a value by itself, a pointer, so it always has
     a value; its type says what the static environment binds it to. A
     symbol that is defined and has no equation ([defined_symbols]) has
     the type of the values that are not null, which a pointer is: so
     nothing is asked of it, not even that the static environment binds
     it.
   - Code. Nothing is asked. A function type says which code id a
     closure has (FlambdaTypeMeaningSpec.v); that the static environment
     binds the code id, and to what, is not part of an environment of
     types. (Simplify keeps the code in its own environment,
     [Downwards_env.all_code].)
   - Poison. Nothing is asked of the type of a name whose value is the
     poison constant of the kind of the type ([satisfied_unless_poison];
     there is a CR there). Typing facts are about values that are not
     poison: a name that is not poison has its type
     ([find_not_poison_statement]), and a use of a fact has the other
     case to deal with. Inside a type nothing changes: the fields of a
     block that is not poison have their types as
     FlambdaTypeMeaningSpec.v says, poison or not.
     The exemption is by the value that the valuation gives, for every
     name. It cannot be only for the names in scope: a parameter that
     holds poison may be captured by a closure, and is out of scope in
     its body; and a variable that exists only in types may stand for
     one that a term bound at a use of a continuation, where it held
     poison. The environment does not record which is which. A side
     effect: a valuation may give poison to a variable that exists only
     in types and that nothing else constrains, so that to satisfy an
     environment is not to have found a value of the type of each such
     variable. There is a CR at [typing_env_satisfied].
   - Aliases are exact, poison or not: names in one class of the
     aliases have the same value ([aliases_respected],
     FlambdaEnvAliasesSpec.v). The compiler reads canonical elements
     from the aliases, not from the alias types, so this is asked of
     the aliases themselves. That the two agree is for the invariant of
     an environment.
   - An environment that is bottom is satisfied by nothing.
   - The levels, the scopes, the binding times and
     [next_binding_time] are not read: they are what the functions
     that build an environment and cut it need, and are for the
     invariant of an environment. Name modes and [min_binding_time]
     are read only to say which variables are in scope.

   Is it true of what Simplify builds? Where Simplify defines a
   variable and gives it a type, the machine binds the variable to a
   value of that type; a handler runs under the variables of the place
   of its definition; the body of a function, and the variables that a
   join makes existential, are what valuations are for. Where it is not
   known to be true, and a statement that takes it as a premise says
   nothing:
   - Lifting. Simplify gives a variable the type "is this symbol" when
     it lifts the block or the closure that the variable is bound to,
     and gives the symbol its type, at a place where the term as it was
     has bound no such symbol: only the term that Simplify produces
     binds it, earlier. The values of a run of the first term do not
     satisfy that environment. This is for the workstream on lifting
     (S5), which has two runs to relate; the environment is satisfied
     by the values of the second.
   - Relations on a name that holds poison: until a relation says
     nothing of such a name (FlambdaTypeMeaningSpec.v is to change so),
     the types that unboxing gives the [Is_int] and tag parameters of a
     field of an inactive case of a variant are not true.
   - Kinds. That the machine binds a variable to a value of the kind it
     is defined with is a premise wherever a variable is defined; it is
     for the semantics to give (workstream C2).
   - What FlambdaTypeMeaningSpec.v leaves out: code age (a type that
     names code), allocation modes.

   What is stated: what satisfies the empty environment and a bottom
   one; that satisfaction by the machine depends only on the variables
   in scope; what [find] and [mem] say of a name; what the canonical
   element of a simple is, with [type_simple_in_term_exn], which is
   what Simplify does to every simple of a term. No statement here has
   a premise on the environment (an invariant): they hold of every
   environment. What the functions that build an environment do to
   satisfaction, binders, the invariant and the renaming of names are
   to follow.

   The proofs are in FlambdaTypingEnvProofs.v, which needs no review. *)

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
(* CR mshinwell: a valuation may give poison to a variable that exists
   only in types, of which nothing is then asked: the exemption of
   poison is by the value, for every name, and not only for the names
   that a term binds. The alternative is to exempt only the variables
   in scope, those that a closure has captured and those that a join
   has made existential from a variable of a use; the environment does
   not record the last two. Nothing is known to go wrong with the
   choice made; what is lost is that a variable that exists only in
   types, and that nothing else constrains, has a value of its type.
   Decision D26. *)
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

(* So a name whose value is not poison has the type found for it. *)
Definition find_not_poison_statement : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t)
    (n : name) (kind : option flambda_kind) (ty : flambda_type) (v : value),
    typing_env_satisfied statics valuation tenv ->
    Typing_env.find tenv n kind = Some ty ->
    value_of_name valuation n = Some v ->
    (∀ k : flambda_kind, v <> Value_const (Poison k)) ->
    type_satisfied statics valuation v ty.

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
