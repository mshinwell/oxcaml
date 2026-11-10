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

(* Flambda types and typing environments: a first, naive model, and
   refinement relative to a typing environment.

   This file is to be reviewed, against middle_end/flambda2/types/: the
   types ([Type_grammar.t]), the environment ([Typing_env.t]), what it
   means for an environment of values to satisfy a typing environment,
   and the statements.

   The simplifier rewrites a term by what it knows of the variables in
   scope, which it keeps in a typing environment. A rewrite of this kind is
   not sound under every environment of values, only under those the
   typing environment describes; so its statement of correctness is a
   refinement relative to a typing environment ([expr_refines_in]), where
   those of ../../rocq/ are under all environments.

   The model is naive on purpose. A type is unknown, bottom or an alias to
   a [Simple] ([Equals], which is how the compiler says that a variable is
   another variable or a constant). A typing environment is a list of
   variables with types, all of which hold. There are no kinds, no types
   of blocks, closures or boxed numbers, no meet or join, no levels,
   binding times or canonical aliases, no environment extensions, and
   nothing about symbols or continuation parameters' types at their uses.
   What the model does fix is the meaning of a type ([type_satisfied]) and
   of an environment ([env_satisfies]): a richer grammar is to give more
   cases to the first and keep the second.

   The statements:
   - an alias may be followed ([canonical_simple_sound_statement], after
     [Typing_env.get_canonical_simple_exn]), in the arguments of an
     [Apply_cont], in a [Let] and at the scrutinee of a [Switch];
   - nothing has to be preserved where a type is bottom
     ([bottom_statement]);
   - going under a [Let] adds what is known of its variable
     ([let_refines_in_statement], [let_simple_refines_in_statement]), and
     going into the body of a [Let_cont] changes nothing. The variable
     must not occur in the typing environment: a binder that shadowed
     would invalidate what is known, which is the reason for the
     simplifier's invariant that bound names are fresh;
   - going into a handler keeps what is known where the [Let_cont] is and
     adds its parameters ([let_cont_handler_refines_in_statement],
     [let_cont_recursive_handler_refines_in_statement]). A handler runs
     later, any number of times, but under the variables of the place of
     its definition, whose values do not change; what was learnt in the
     body of the [Let_cont] is not known in it. Nothing is known of a
     parameter but that it is bound: the types of the arguments at the
     uses of the continuation are not joined;
   - [let_const_apply_cont_statement] puts these together with the removal
     of an unused [Let]: a constant is propagated to its use.

   The proofs are in FlambdaTypesProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaNominalSpec.
Import ListNotations.

(* ======================================================================== *)
(* Types and typing environments                                            *)
(* ======================================================================== *)

(* [Type_grammar.t], with nothing known of the head of a type: [Equals] is
   [alias_type_of]. *)
Inductive flambda_type : Type :=
  | Unknown
  | Bottom
  | Equals (s : simple).

(* [Typing_env.t]: the variables in scope with what is known of each. A
   variable may be listed more than once, and then all its types hold. *)
Definition typing_env : Type := list (variable * flambda_type).

(* A value has a type, under an environment giving values to the variables
   the type mentions. *)
Definition type_satisfied (vars : env) (v : value) (t : flambda_type)
    : Prop :=
  match t with
  | Unknown => True
  | Bottom => False
  | Equals s => eval_simple vars s = Some v
  end.

(* An environment of values is one of those a typing environment
   describes: every variable listed is bound, to a value of the type. *)
Definition env_satisfies (tenv : typing_env) (vars : env) : Prop :=
  ∀ (x : variable) (t : flambda_type),
    (x, t) ∈ tenv ->
    ∃ v : value, lookup x vars = Some v ∧ type_satisfied vars v t.

(* A variable occurs in a typing environment: it is listed, or is what
   another variable is an alias of. *)
Definition var_in_typing_env (x : variable) (tenv : typing_env) : Prop :=
  ∃ (y : variable) (t : flambda_type),
    (y, t) ∈ tenv
    ∧ (x = y ∨ ∃ s : simple, t = Equals s ∧ var_free_in_simple x s).

(* ======================================================================== *)
(* Refinement relative to a typing environment                              *)
(* ======================================================================== *)

Definition expr_refines_in (tenv : typing_env) (source target : expr)
    : Prop :=
  ∀ (vars : env) (conts : cont_env),
    env_satisfies tenv vars ->
    refines (State source vars conts) (State target vars conts).

Definition expr_equivalent_in (tenv : typing_env) (e e' : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env),
    env_satisfies tenv vars ->
    equivalent (State e vars conts) (State e' vars conts).

(* With nothing known it is refinement under all environments, which
   implies refinement relative to any typing environment. *)
Definition expr_refines_in_empty_statement : Prop :=
  ∀ source target : expr,
    expr_refines_in [] source target <-> expr_refines source target.

Definition expr_refines_weaken_statement : Prop :=
  ∀ (tenv : typing_env) (source target : expr),
    expr_refines source target -> expr_refines_in tenv source target.

(* Nothing has to be preserved under a typing environment that no
   environment of values satisfies. *)
Definition bottom_statement : Prop :=
  ∀ (tenv : typing_env) (x : variable) (e e' : expr),
    (x, Bottom) ∈ tenv -> expr_equivalent_in tenv e e'.

(* ======================================================================== *)
(* Following aliases                                                        *)
(* ======================================================================== *)

Fixpoint find_alias (tenv : typing_env) (x : variable) : option simple :=
  match tenv with
  | [] => None
  | (y, Equals s) :: tenv =>
    if Pos.eqb x y then Some s else find_alias tenv x
  | _ :: tenv => find_alias tenv x
  end.

(* One step of [Typing_env.get_canonical_simple_exn], which goes on to the
   canonical element of the alias class. *)
Definition canonical_simple (tenv : typing_env) (s : simple) : simple :=
  match s with
  | Var x =>
    match find_alias tenv x with
    | Some alias => alias
    | None => s
    end
  | Const _ => s
  end.

Definition canonical_simple_sound_statement : Prop :=
  ∀ (tenv : typing_env) (vars : env) (s : simple),
    env_satisfies tenv vars ->
    eval_simple vars (canonical_simple tenv s) = eval_simple vars s.

Definition apply_cont_canonical_statement : Prop :=
  ∀ (tenv : typing_env) (k : continuation) (args : list simple),
    expr_equivalent_in tenv (Apply_cont (Apply_cont_expr k args))
      (Apply_cont (Apply_cont_expr k (map (canonical_simple tenv) args))).

Definition let_simple_canonical_statement : Prop :=
  ∀ (tenv : typing_env) (x : variable) (s : simple) (body : expr),
    expr_equivalent_in tenv (Let x (Simple s) body)
      (Let x (Simple (canonical_simple tenv s)) body).

(* A [Switch] whose scrutinee is known to be a constant is its arm for that
   constant. *)
Definition switch_known_statement : Prop :=
  ∀ (tenv : typing_env) (scrutinee : simple) (i : Z)
    (arms : list (Z * apply_cont)) (ac : apply_cont),
    canonical_simple tenv scrutinee = Const (Naked_immediate i) ->
    find_arm i arms = Some ac ->
    expr_equivalent_in tenv (Switch scrutinee arms) (Apply_cont ac).

(* ======================================================================== *)
(* Going under binders                                                      *)
(* ======================================================================== *)

(* Under a [Let], the body is rewritten knowing nothing new of the
   variable... *)
Definition let_refines_in_statement : Prop :=
  ∀ (tenv : typing_env) (x : variable) (defining_expr : named)
    (body body' : expr),
    ~ var_in_typing_env x tenv ->
    expr_refines_in ((x, Unknown) :: tenv) body body' ->
    expr_refines_in tenv (Let x defining_expr body)
      (Let x defining_expr body').

(* ... or, when it is bound to a [Simple], knowing that it is that. *)
Definition let_simple_refines_in_statement : Prop :=
  ∀ (tenv : typing_env) (x : variable) (s : simple) (body body' : expr),
    ~ var_in_typing_env x tenv ->
    ~ var_free_in_simple x s ->
    expr_refines_in ((x, Equals s) :: tenv) body body' ->
    expr_refines_in tenv (Let x (Simple s) body) (Let x (Simple s) body').

Definition let_cont_body_refines_in_statement : Prop :=
  ∀ (tenv : typing_env) (k : continuation) (handler : continuation_handler)
    (body body' : expr),
    expr_refines_in tenv body body' ->
    expr_refines_in tenv (Let_cont_non_recursive k handler body)
      (Let_cont_non_recursive k handler body').

Definition let_cont_recursive_body_refines_in_statement : Prop :=
  ∀ (tenv : typing_env)
    (handlers : list (continuation * continuation_handler))
    (body body' : expr),
    expr_refines_in tenv body body' ->
    expr_refines_in tenv (Let_cont_recursive handlers body)
      (Let_cont_recursive handlers body').

(* [Typing_env.add_definitions_of_params]: the parameters of a handler come
   into scope, with nothing known of them. *)
Definition add_definitions_of_params (tenv : typing_env)
    (params : list variable) : typing_env :=
  map (fun param => (param, Unknown)) params ++ tenv.

(* Into a handler, of a non-recursive [Let_cont] and of a recursive one:
   what is known at the [Let_cont] is known in the handler, with its
   parameters. *)
Definition let_cont_handler_refines_in_statement : Prop :=
  ∀ (tenv : typing_env) (k : continuation) (params : list variable)
    (handler handler' body : expr),
    (∀ param : variable, param ∈ params -> ~ var_in_typing_env param tenv) ->
    expr_refines_in (add_definitions_of_params tenv params) handler handler'
    ->
    expr_refines_in tenv
      (Let_cont_non_recursive k (Handler params handler) body)
      (Let_cont_non_recursive k (Handler params handler') body).

Definition let_cont_recursive_handler_refines_in_statement : Prop :=
  ∀ (tenv : typing_env)
    (before : list (continuation * continuation_handler)) (k : continuation)
    (params : list variable) (handler handler' : expr)
    (after : list (continuation * continuation_handler)) (body : expr),
    (∀ param : variable, param ∈ params -> ~ var_in_typing_env param tenv) ->
    expr_refines_in (add_definitions_of_params tenv params) handler handler'
    ->
    expr_refines_in tenv
      (Let_cont_recursive (before ++ (k, Handler params handler) :: after)
         body)
      (Let_cont_recursive (before ++ (k, Handler params handler') :: after)
         body).

(* ======================================================================== *)
(* An example: propagating a constant                                       *)
(* ======================================================================== *)

Definition let_const_apply_cont_statement : Prop :=
  ∀ (x : variable) (c : const) (k : continuation),
    expr_refines
      (Let x (Simple (Const c)) (Apply_cont (Apply_cont_expr k [Var x])))
      (Apply_cont (Apply_cont_expr k [Const c])).
