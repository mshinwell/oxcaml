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

(* Execution of the control-flow fragment of Flambda 2 (FlambdaModel.v), and
   what it means for two terms to behave alike.

   This file is to be reviewed: [eval_named], [apply_continuation] and the
   rules of [step], then [behaves], [equivalent] and [refines].

   The semantics is an abstract machine. A state is an expression with an
   environment giving values to variables and one giving closures to
   continuations; [step] is a function, so execution is deterministic by
   construction. A continuation closure keeps the environments of its
   definition, so no substitution is involved and binders may shadow.

   A continuation with no binding stands for a way out of the term: the
   return or exception continuation of the enclosing function or unit.
   Applying one ends execution, and the continuation and its arguments are
   what is observed ([Exit]). This is the only observation so far; there is
   no memory and there are no effects.

   Execution is undefined ([Undefined]) at [Invalid], at an unbound variable,
   at a continuation applied to the wrong number of arguments, at a [Switch]
   whose scrutinee is not a naked immediate with an arm, and where a
   primitive has no value. A transformation may do anything to a term whose
   execution is undefined: that is [refines], the statement of correctness
   to use for a transformation; [equivalent] is the stronger, symmetric one.
   [refines_defined_statement] and [refines_antisymmetric_statement] say how
   the two are related.

   The primitives are abstract: [eval_prim] is a parameter, with no axioms.
   A law of a primitive (say, that an addition commutes) is to be stated
   about [eval_prim], either as an axiom or, once primitives are defined,
   as a lemma.

   The lemmas and the proofs are in FlambdaSemanticsProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel.
Import ListNotations.

(* ======================================================================== *)
(* Values and environments                                                  *)
(* ======================================================================== *)

(* The values of variables. Only constants so far: there are no blocks and no
   closures. *)
Inductive value : Type :=
  | Value_const (c : const).

(* The value of a primitive applied to the values of its arguments, if it has
   one. *)
Parameter eval_prim : prim -> list value -> option value.

(* The first binding of a name. *)
Fixpoint lookup {A : Type} (name : positive) (bindings : list (positive * A))
    : option A :=
  match bindings with
  | [] => None
  | (bound, a) :: bindings =>
    if Pos.eqb name bound then Some a else lookup name bindings
  end.

Definition env : Type := list (variable * value).

(* A continuation handler with the environments of its definition. For a
   handler of a recursive [Let_cont], [recursive] is all the handlers of
   that [Let_cont], which are in scope in the handler; it is empty for a
   non-recursive one. (The warning silenced is about induction schemes
   through the pairs of the list, which nothing uses yet.) *)
#[local] Set Warnings "-register-all".
Inductive cont_value : Type :=
  | Closure (h : continuation_handler) (vars : env)
      (conts : list (continuation * cont_value))
      (recursive : list (continuation * continuation_handler)).

Definition cont_env : Type := list (continuation * cont_value).

(* The closures of the handlers of a recursive [Let_cont] defined under
   [vars] and [conts]. *)
Definition rec_closures
    (handlers : list (continuation * continuation_handler)) (vars : env)
    (conts : cont_env) : cont_env :=
  map (fun '(k, h) => (k, Closure h vars conts handlers)) handlers.

(* ======================================================================== *)
(* Evaluation                                                               *)
(* ======================================================================== *)

Definition eval_simple (vars : env) (s : simple) : option value :=
  match s with
  | Var x => lookup x vars
  | Const c => Some (Value_const c)
  end.

Fixpoint eval_simples (vars : env) (args : list simple)
    : option (list value) :=
  match args with
  | [] => Some []
  | s :: args =>
    let* v := eval_simple vars s in
    let* vs := eval_simples vars args in
    Some (v :: vs)
  end.

Definition eval_named (vars : env) (defining_expr : named) : option value :=
  match defining_expr with
  | Simple s => eval_simple vars s
  | Prim p args =>
    let* vs := eval_simples vars args in
    eval_prim p vs
  end.

(* Binds parameters to arguments; there must be as many of each. *)
Fixpoint bind_params (params : list variable) (vs : list value) (vars : env)
    : option env :=
  match params, vs with
  | [], [] => Some vars
  | x :: params, v :: vs => bind_params params vs ((x, v) :: vars)
  | _, _ => None
  end.

Fixpoint find_arm (i : Z) (arms : list (Z * apply_cont)) : option apply_cont :=
  match arms with
  | [] => None
  | (discriminant, ac) :: arms =>
    if Z.eqb i discriminant then Some ac else find_arm i arms
  end.

(* ======================================================================== *)
(* Steps                                                                    *)
(* ======================================================================== *)

Inductive state : Type :=
  | State (e : expr) (vars : env) (conts : cont_env).

(* What one step of a state, or a bounded run, comes to: another state, the
   application of an unbound continuation, or undefined behaviour. *)
Inductive step_result : Type :=
  | Step (s : state)
  | Exit (k : continuation) (vs : list value)
  | Undefined.

(* Applying a bound continuation runs its handler under the environments of
   its definition, with its parameters bound and, for a recursive one, the
   handlers defined with it in scope again. *)
Definition apply_continuation (k : continuation) (vs : list value)
    (conts : cont_env) : step_result :=
  match lookup k conts with
  | None => Exit k vs
  | Some (Closure (Handler params handler) def_vars def_conts recursive) =>
    match bind_params params vs def_vars with
    | Some handler_vars =>
      Step (State handler handler_vars
        (rec_closures recursive def_vars def_conts ++ def_conts))
    | None => Undefined
    end
  end.

Definition step (s : state) : step_result :=
  match s with
  | State (Let x defining_expr body) vars conts =>
    match eval_named vars defining_expr with
    | Some v => Step (State body ((x, v) :: vars) conts)
    | None => Undefined
    end
  | State (Let_cont_non_recursive k h body) vars conts =>
    Step (State body vars ((k, Closure h vars conts []) :: conts))
  | State (Let_cont_recursive handlers body) vars conts =>
    Step (State body vars (rec_closures handlers vars conts ++ conts))
  | State (Apply_cont ac) vars conts =>
    match eval_simples vars (ac_args ac) with
    | Some vs => apply_continuation (ac_continuation ac) vs conts
    | None => Undefined
    end
  | State (Switch scrutinee arms) vars conts =>
    match eval_simple vars scrutinee with
    | Some (Value_const (Naked_immediate i)) =>
      match find_arm i arms with
      | Some ac => Step (State (Apply_cont ac) vars conts)
      | None => Undefined
      end
    | _ => Undefined
    end
  | State Invalid _ _ => Undefined
  end.

(* At most [fuel] steps: the state reached, or how execution ended. *)
Fixpoint run (fuel : nat) (s : state) : step_result :=
  match fuel with
  | O => Step s
  | S fuel =>
    match step s with
    | Step s' => run fuel s'
    | result => result
    end
  end.

(* ======================================================================== *)
(* Behaviours                                                               *)
(* ======================================================================== *)

Inductive behaviour : Type :=
  | Exits (k : continuation) (vs : list value)
  | Goes_wrong
  | Diverges.

Definition behaves (s : state) (b : behaviour) : Prop :=
  match b with
  | Exits k vs => ∃ fuel : nat, run fuel s = Exit k vs
  | Goes_wrong => ∃ fuel : nat, run fuel s = Undefined
  | Diverges => ∀ fuel : nat, ∃ s' : state, run fuel s = Step s'
  end.

(* A state has at most one behaviour. (That it has one is not provable
   without the excluded middle.) *)
Definition behaviour_unique_statement : Prop :=
  ∀ (s : state) (b b' : behaviour), behaves s b -> behaves s b' -> b = b'.

Definition equivalent (s s' : state) : Prop :=
  ∀ b : behaviour, behaves s b <-> behaves s' b.

(* The target behaves as the source does, unless the source goes wrong: an
   exit of the source is one of the target, and the way the target ends, if
   it does, is the way the source ends, unless the source goes wrong. With
   the excluded middle this is to say that every behaviour of the target is
   one of the source unless the source goes wrong; it is stated of the
   behaviours that end so that it can be proved without. *)
Definition refines (source target : state) : Prop :=
  (∀ (k : continuation) (vs : list value),
    behaves source (Exits k vs) -> behaves target (Exits k vs))
  ∧ (∀ b : behaviour,
      b <> Diverges ->
      behaves target b -> behaves source b ∨ behaves source Goes_wrong).

(* What [refines] comes to: a source that does not go wrong and its target
   are equivalent, divergence included; and two states that refine each
   other are equivalent. *)
Definition refines_defined_statement : Prop :=
  ∀ source target : state,
    refines source target ->
    ~ behaves source Goes_wrong ->
    equivalent source target.

Definition refines_antisymmetric_statement : Prop :=
  ∀ s s' : state, refines s s' -> refines s' s -> equivalent s s'.

(* The same for expressions: under every pair of environments. *)
Definition expr_equivalent (e e' : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env),
    equivalent (State e vars conts) (State e' vars conts).

Definition expr_refines (source target : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env),
    refines (State source vars conts) (State target vars conts).

(* A step does not change the behaviour. *)
Definition step_equivalent_statement : Prop :=
  ∀ s s' : state, step s = Step s' -> equivalent s s'.
