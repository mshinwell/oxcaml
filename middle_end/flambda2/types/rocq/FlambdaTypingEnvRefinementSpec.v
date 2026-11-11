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


(* Refinement of terms relative to a typing environment.

   This file is to be reviewed: the definitions and the statements. The
   typing environment is FlambdaTypingEnv.v; what it is for the machine
   to satisfy one is FlambdaTypingEnvSpec.v ([env_satisfies_strictly]);
   the invariant is FlambdaTypingEnvInvariantSpec.v; refinement of
   states is ../../rocq/FlambdaSemanticsSpec.v.

   Simplify rewrites a term by what its typing environment says of the
   names in scope. Such a rewrite is not right under every environment
   of the machine, only under those that the typing environment
   describes: [expr_refines_under tenv source target] is refinement
   under every state of the machine whose variables and static
   environment satisfy [tenv] strictly. It is to replace
   [expr_refines_in] of FlambdaTypesSpec.v, which is stated of the
   first, naive model of types; that file stays until what uses it has
   moved.

   Strict satisfaction is the notion that the statements about types
   are made of (meet, join, the provers), so a rewrite that reads a
   type is justified under it. After variant unboxing the environments
   that Simplify builds are satisfied only where poison is exempt
   (decision D26), and the statements here do not apply there; the two
   about canonical elements do not read a type and hold of that weaker
   notion too ([type_simple_in_term_canonical_statement] has it as its
   premise).

   The statements:
   - how the notion compares with refinement under all environments,
     and that nothing is asked under an environment that is bottom;
   - a [Simple] may be replaced by the canonical element that the
     environment answers for it at the normal name mode, in the
     arguments of an [Apply_cont] and in a [Let], and a [Switch] on a
     [Simple] whose canonical element is a constant is its arm;
   - in the machine, what defining a variable, defining parameters and
     giving a variable in scope a type do to satisfaction: the three
     steps by which Simplify's environment follows the term;
   - going under a [Let]: the body is rewritten under the environment
     with the variable defined, at the kind of the value that the
     machine binds it to, and with a type if every such value has it;
   - going into the body of a [Let_cont] changes nothing; going into a
     handler defines its parameters.

   Kinds. A [Let] gives the kind of its variable and a handler the
   kinds of its parameters (../../rocq/FlambdaModel.v), and the machine
   looks at neither: it binds the value that it is given, of whatever
   kind. So no statement here reads those kinds. The body of a [Let]
   is rewritten under the environment with the variable defined at the
   kind of the value that the defining expression gives, which is a
   premise; a handler under the environments at every choice of kinds
   for its parameters, since any values may be passed to it. Simplify
   defines a variable at the kind that its binder gives
   ([Typing_env.add_variable_definition] is a fatal error otherwise):
   that is the statement about a [Let] where the two kinds are the
   same, and one of the choices for a handler. That the value bound is
   of the kind that the binder gives is so in the runs of a term that
   passes the check of ../../rocq/FlambdaWellKindedSpec.v; it is not
   known of the terms of the compiler, and it is not a premise here.

   The variable of a [Let] and the parameters of a handler are not to
   be bound in the environment: a binder that shadowed would invalidate
   what is known. That is Simplify's rule that bound names are fresh.

   The proofs are in FlambdaTypingEnvRefinementProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvInvariantSpec.
Import ListNotations.

(* ======================================================================== *)
(* Refinement relative to a typing environment                              *)
(* ======================================================================== *)

Definition expr_refines_under (tenv : Typing_env.t) (source target : expr)
    : Prop :=
  ∀ (vars : env) (conts : cont_env) (statics : static_env),
    env_satisfies_strictly tenv statics vars ->
    refines (State source vars conts statics)
      (State target vars conts statics).

Definition expr_equivalent_under (tenv : Typing_env.t) (e e' : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env) (statics : static_env),
    env_satisfies_strictly tenv statics vars ->
    equivalent (State e vars conts statics) (State e' vars conts statics).

(* Refinement under all environments is refinement under any typing
   environment. *)
Definition expr_refines_under_weaken_statement : Prop :=
  ∀ (tenv : Typing_env.t) (source target : expr),
    expr_refines source target -> expr_refines_under tenv source target.

Definition expr_equivalent_under_refines_statement : Prop :=
  ∀ (tenv : Typing_env.t) (e e' : expr),
    expr_equivalent_under tenv e e' -> expr_refines_under tenv e e'.

Definition expr_refines_under_trans_statement : Prop :=
  ∀ (tenv : Typing_env.t) (e e' e'' : expr),
    expr_refines_under tenv e e' ->
    expr_refines_under tenv e' e'' ->
    expr_refines_under tenv e e''.

(* Nothing has to be preserved under an environment that is bottom:
   nothing satisfies it. *)
Definition bottom_refines_under_statement : Prop :=
  ∀ (tenv : Typing_env.t) (e e' : expr),
    Typing_env.is_bottom tenv = true -> expr_equivalent_under tenv e e'.

(* ======================================================================== *)
(* Canonical elements                                                       *)
(* ======================================================================== *)

(* The canonical element that the environment answers for a [Simple] of
   a term, at the normal name mode ([Simplify_simple.simplify_simple]). *)
Definition canonical_in_terms (tenv : Typing_env.t) (s canonical : simple)
    : Prop :=
  Typing_env.mem_simple (Some Name_mode.normal) tenv s = true
  ∧ ∃ ty : flambda_type,
      Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal) s
      = Some (Some (ty, canonical)).

Definition apply_cont_canonical_statement : Prop :=
  ∀ (tenv : Typing_env.t) (k : continuation) (args args' : list simple),
    Forall2 (canonical_in_terms tenv) args args' ->
    expr_equivalent_under tenv (Apply_cont (Apply_cont_expr k args))
      (Apply_cont (Apply_cont_expr k args')).

Definition let_simple_canonical_statement : Prop :=
  ∀ (tenv : Typing_env.t) (x : variable) (kind : flambda_kind)
    (s canonical : simple) (body : expr),
    canonical_in_terms tenv s canonical ->
    expr_equivalent_under tenv (Let x kind (Simple s) body)
      (Let x kind (Simple canonical) body).

(* A [Switch] whose scrutinee is known to be a constant is its arm for
   that constant. *)
Definition switch_known_statement : Prop :=
  ∀ (tenv : Typing_env.t) (scrutinee : simple) (i : Z)
    (arms : list (Z * apply_cont)) (ac : apply_cont),
    canonical_in_terms tenv scrutinee (Const (Naked_immediate i)) ->
    find_arm i arms = Some ac ->
    expr_equivalent_under tenv (Switch scrutinee arms) (Apply_cont ac).

(* ======================================================================== *)
(* The environment follows the term                                         *)
(* ======================================================================== *)

(* A variable is defined, and the machine binds it to a value of the
   kind. *)
Definition add_variable_definition_env_satisfies_strictly_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars : env) (x : variable)
    (kind : flambda_kind) (v : value),
    typing_env_well_formed tenv = true ->
    Typing_env.mem None tenv (Name_var x) = false ->
    kind_of_value v = kind ->
    env_satisfies_strictly tenv statics vars ->
    env_satisfies_strictly
      (Typing_env.add_variable_definition tenv x kind Name_mode.normal)
      statics ((x, v) :: vars).

(* Parameters are defined, and the machine binds them, each to a value
   of its kind. *)
Definition add_definitions_of_params_env_satisfies_strictly_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars vars' : env)
    (params : list (variable * flambda_kind)) (vs : list value),
    typing_env_invariant tenv ->
    distinct (map fst params) = true ->
    (∀ x : variable,
      x ∈ map fst params -> Typing_env.mem None tenv (Name_var x) = false) ->
    Forall2 (fun param v => kind_of_value v = snd param) params vs ->
    bind_params (map fst params) vs vars = Some vars' ->
    env_satisfies_strictly tenv statics vars ->
    env_satisfies_strictly (Typing_env.add_definitions_of_params tenv params)
      statics vars'.

(* A variable in scope is given a type that the value that the machine
   has for it has. The type speaks only of variables in scope, so that
   it says the same of the machine's values and of a valuation's. *)
Definition replace_equation_env_satisfies_strictly_statement : Prop :=
  ∀ (tenv : Typing_env.t) (statics : static_env) (vars : env) (x : variable)
    (ty : flambda_type),
    in_scope_in_terms tenv x ->
    (∀ y : variable, y ∈ free_variables ty -> in_scope_in_terms tenv y) ->
    (∀ v : value, lookup x vars = Some v -> type_satisfied statics vars v ty)
    ->
    env_satisfies_strictly tenv statics vars ->
    env_satisfies_strictly (Typing_env.replace_equation tenv (Name_var x) ty)
      statics vars.

(* ======================================================================== *)
(* Going under binders                                                      *)
(* ======================================================================== *)

(* Under a [Let] the body is rewritten with the variable defined, at
   the kind of the value that the defining expression gives. The kind
   that the [Let] gives its variable, [declared], is not read: the
   machine does not look at it. (Simplify defines the variable at that
   kind: the case where [kind] is [declared].) *)
Definition let_refines_under_statement : Prop :=
  ∀ (tenv : Typing_env.t) (x : variable) (declared : flambda_kind)
    (defining_expr : named) (body body' : expr) (kind : flambda_kind),
    typing_env_well_formed tenv = true ->
    Typing_env.mem None tenv (Name_var x) = false ->
    (∀ (statics : static_env) (vars : env) (v : value),
      env_satisfies_strictly tenv statics vars ->
      eval_named statics vars defining_expr = Some v ->
      kind_of_value v = kind) ->
    expr_refines_under
      (Typing_env.add_variable_definition tenv x kind Name_mode.normal) body
      body' ->
    expr_refines_under tenv (Let x declared defining_expr body)
      (Let x declared defining_expr body').

(* The same with a type, if every value that the defining expression
   gives has it; the variable is defined at the kind of the type. The
   type speaks of variables in scope where the [Let] is. *)
Definition let_typed_refines_under_statement : Prop :=
  ∀ (tenv : Typing_env.t) (x : variable) (declared : flambda_kind)
    (defining_expr : named) (body body' : expr) (ty : flambda_type),
    typing_env_well_formed tenv = true ->
    Typing_env.mem None tenv (Name_var x) = false ->
    (∀ y : variable, y ∈ free_variables ty -> in_scope_in_terms tenv y) ->
    (∀ (statics : static_env) (vars : env) (v : value),
      env_satisfies_strictly tenv statics vars ->
      eval_named statics vars defining_expr = Some v ->
      type_satisfied statics vars v ty) ->
    expr_refines_under
      (Typing_env.replace_equation
         (Typing_env.add_variable_definition tenv x
            (FlambdaTypeGrammar.kind ty) Name_mode.normal)
         (Name_var x) ty)
      body body' ->
    expr_refines_under tenv (Let x declared defining_expr body)
      (Let x declared defining_expr body').

(* The body of a [Let_cont] runs where the [Let_cont] is. *)
Definition let_cont_body_refines_under_statement : Prop :=
  ∀ (tenv : Typing_env.t) (k : continuation) (handler : continuation_handler)
    (body body' : expr),
    expr_refines_under tenv body body' ->
    expr_refines_under tenv (Let_cont_non_recursive k handler body)
      (Let_cont_non_recursive k handler body').

Definition let_cont_recursive_body_refines_under_statement : Prop :=
  ∀ (tenv : Typing_env.t)
    (handlers : list (continuation * continuation_handler))
    (body body' : expr),
    expr_refines_under tenv body body' ->
    expr_refines_under tenv (Let_cont_recursive handlers body)
      (Let_cont_recursive handlers body').

(* A handler runs later, any number of times, under the variables of
   the place of its definition, whose values do not change, with its
   parameters bound to the arguments of a use, and under a static
   environment that may have grown. What was known where the [Let_cont]
   is is known in it, with its parameters defined; nothing is known of
   a parameter but its kind, which is that of the argument, whatever it
   is: the kinds that the handler gives its parameters, in [metadata],
   are not read. (The types of the arguments at the uses are joined by
   the join of environments, which is not here.) *)
Definition let_cont_handler_refines_under_statement : Prop :=
  ∀ (tenv : Typing_env.t) (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler handler' body : expr),
    typing_env_invariant tenv ->
    distinct params = true ->
    (∀ x : variable,
      x ∈ params -> Typing_env.mem None tenv (Name_var x) = false) ->
    (∀ kinds : list flambda_kind,
      length kinds = length params ->
      expr_refines_under
        (Typing_env.add_definitions_of_params tenv (combine params kinds))
        handler handler') ->
    expr_refines_under tenv
      (Let_cont_non_recursive k (Handler params metadata handler) body)
      (Let_cont_non_recursive k (Handler params metadata handler') body).
