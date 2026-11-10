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

(* Execution of the terms of FlambdaModel.v, and what it means for two
   terms to behave alike.

   This file is to be reviewed: [eval_named], [eval_static_bindings],
   [apply_cont_value], [call_function] and the rules of [step], then
   [behaves], [equivalent] and [refines].

   The semantics is an abstract machine. A state is an expression with an
   environment giving values to variables, one giving closures to
   continuations, and the static environment; [step] is a function, so
   execution is deterministic by construction. A continuation closure keeps
   the environments of its definition, so no substitution is involved and
   binders may shadow.

   The static environment is what [Let_static] has bound so far: the code
   of code ids, and the objects that symbols point to. It is global: it is
   not kept in closures, and only grows. A symbol is a value by itself, a
   pointer ([Value_symbol]), whether or not it is bound; what it points to
   is looked up where it is used, as a closure to call or to project
   from. So a group of bindings may be recursive, and static data cyclic.
   A [Let_static] is executed where it stands; nothing lifts it.

   A continuation with no binding stands for a way out of the term: the
   return or exception continuation of the enclosing unit. Applying one
   ends execution, and the continuation and its arguments are what is
   observed ([Exit]). This is the only observation so far; there is no
   mutable memory and there are no effects.

   A function call ([call_function]) runs the body of the code of the
   closure called, with the code's return and exception continuations
   standing for the caller's. There is no stack.

   Execution is undefined ([Undefined]) at [Invalid], at an unbound variable,
   at a continuation or a function applied to the wrong number of
   arguments, at a [Switch] whose scrutinee is not a naked immediate with
   an arm, where a primitive has no value, at a call of what is not a
   closure, of a closure whose code is not bound, or directly of a closure
   of other code than the one named, and at the projection of a value slot
   from what is not a closure with that slot. A transformation may do
   anything to a term whose
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

(* The values of variables: constants, closures made by a [Let], and
   pointers to what symbols are bound to. A closure is the code of its
   function and the values of its value slots. (The warning silenced is
   about induction schemes through the pairs of lists, which nothing uses
   yet.) *)
#[local] Set Warnings "-register-all".
Inductive value : Type :=
  | Value_const (c : const)
  | Value_closure (code : code_id) (value_slots : list (value_slot * value))
  | Value_symbol (s : symbol).

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

(* What a symbol points to. *)
Inductive static_object : Type :=
  | Object_closure (code : code_id) (value_slots : list (value_slot * value))
  | Object_block (tag : Z) (fields : list value)
  | Object_boxed_number (contents : value)
  | Object_string (bytes : list Z).

(* The static environment: the code and the objects bound so far. *)
Record static_env : Type := Static_env {
  static_code : list (code_id * code);
  static_objects : list (symbol * static_object)
}.

Definition empty_static_env : static_env := Static_env [] [].

(* What a continuation is. [Closure] is a continuation handler with the
   environments of its definition. For a handler of a recursive
   [Let_cont], [recursive] is all the handlers of that [Let_cont], which
   are in scope in the handler; it is empty for a non-recursive one.
   [Outer] is a way out of the whole term, by the continuation named. *)
Inductive cont_value : Type :=
  | Closure (h : continuation_handler) (vars : env)
      (conts : list (continuation * cont_value))
      (recursive : list (continuation * continuation_handler))
  | Outer (k : continuation).

Definition cont_env : Type := list (continuation * cont_value).

(* What a continuation name stands for: a continuation with no binding is
   a way out of the term. *)
Definition resolve (k : continuation) (conts : cont_env) : cont_value :=
  match lookup k conts with
  | Some c => c
  | None => Outer k
  end.

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
  | Symbol sym => Some (Value_symbol sym)
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

Fixpoint eval_value_slots (vars : env)
    (value_slots : list (value_slot * simple))
    : option (list (value_slot * value)) :=
  match value_slots with
  | [] => Some []
  | (slot, s) :: value_slots =>
    let* v := eval_simple vars s in
    let* vs := eval_value_slots vars value_slots in
    Some ((slot, v) :: vs)
  end.

(* A value as a closure: one made by a [Let], or a symbol bound to one. *)
Definition closure_of (statics : static_env) (v : value)
    : option (code_id * list (value_slot * value)) :=
  match v with
  | Value_closure code value_slots => Some (code, value_slots)
  | Value_symbol s =>
    match lookup s (static_objects statics) with
    | Some (Object_closure code value_slots) => Some (code, value_slots)
    | _ => None
    end
  | Value_const _ => None
  end.

Definition eval_named (statics : static_env) (vars : env)
    (defining_expr : named) : option value :=
  match defining_expr with
  | Simple s => eval_simple vars s
  | Prim p args =>
    let* vs := eval_simples vars args in
    eval_prim p vs
  | Set_of_closures code value_slots =>
    let* vs := eval_value_slots vars value_slots in
    Some (Value_closure code vs)
  | Project_value_slot slot closure =>
    let* v := eval_simple vars closure in
    let* called := closure_of statics v in
    lookup slot (snd called)
  end.

Definition eval_static_const (vars : env) (const : static_const)
    : option static_object :=
  match const with
  | Static_set_of_closures code value_slots =>
    let* vs := eval_value_slots vars value_slots in
    Some (Object_closure code vs)
  | Static_block tag fields =>
    let* vs := eval_simples vars fields in
    Some (Object_block tag vs)
  | Static_boxed_number contents =>
    let* v := eval_simple vars contents in
    Some (Object_boxed_number v)
  | Static_immutable_string bytes => Some (Object_string bytes)
  end.

(* The static environment with a group of bindings added. Deleted code is
   not bound. *)
Fixpoint eval_static_bindings (vars : env) (bindings : list static_binding)
    (statics : static_env) : option static_env :=
  match bindings with
  | [] => Some statics
  | Bind_code id c :: bindings =>
    eval_static_bindings vars bindings
      (Static_env ((id, c) :: static_code statics) (static_objects statics))
  | Bind_deleted_code _ :: bindings =>
    eval_static_bindings vars bindings statics
  | Bind_symbol s const :: bindings =>
    let* object := eval_static_const vars const in
    eval_static_bindings vars bindings
      (Static_env (static_code statics)
         ((s, object) :: static_objects statics))
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

(* What a [Switch] may be on. *)
Definition naked_immediate_of_value (v : value) : option Z :=
  match v with
  | Value_const (Naked_immediate i) => Some i
  | _ => None
  end.

(* ======================================================================== *)
(* Steps                                                                    *)
(* ======================================================================== *)

Inductive state : Type :=
  | State (e : expr) (vars : env) (conts : cont_env) (statics : static_env).

(* What one step of a state, or a bounded run, comes to: another state, the
   application of an unbound continuation, or undefined behaviour. *)
Inductive step_result : Type :=
  | Step (s : state)
  | Exit (k : continuation) (vs : list value)
  | Undefined.

(* Applying a handler runs it under the environments of its definition,
   with its parameters bound and, for a recursive one, the handlers defined
   with it in scope again. Applying a way out ends execution. *)
Definition apply_cont_value (c : cont_value) (vs : list value)
    (statics : static_env) : step_result :=
  match c with
  | Outer k => Exit k vs
  | Closure (Handler params handler) def_vars def_conts recursive =>
    match bind_params params vs def_vars with
    | Some handler_vars =>
      Step (State handler handler_vars
        (rec_closures recursive def_vars def_conts ++ def_conts) statics)
    | None => Undefined
    end
  end.

Definition apply_continuation (k : continuation) (vs : list value)
    (conts : cont_env) (statics : static_env) : step_result :=
  apply_cont_value (resolve k conts) vs statics.

(* Calling a closure runs the body of its code. The only variables are the
   parameters and the closure itself; the only continuations are the
   return and exception continuations of the code, which stand for what
   the caller's stand for. So there is no stack: to return is to apply the
   continuation the caller gave. A direct call must be to a closure of the
   code named. *)
Definition call_function (callee : value) (kind : call_kind)
    (vs : list value) (return_to exn_to : cont_value) (statics : static_env)
    : step_result :=
  match closure_of statics callee with
  | Some (called, _) =>
    let expected :=
      match kind with
      | Direct named => Pos.eqb called named
      | Indirect => true
      end
    in
    match expected, lookup called (static_code statics) with
    | true, Some c =>
      match bind_params (code_params c) vs [(code_my_closure c, callee)] with
      | Some callee_vars =>
        Step (State (code_body c) callee_vars
          [(code_return_continuation c, return_to);
           (code_exn_continuation c, exn_to)]
          statics)
      | None => Undefined
      end
    | _, _ => Undefined
    end
  | None => Undefined
  end.

Definition step (s : state) : step_result :=
  match s with
  | State (Let x defining_expr body) vars conts statics =>
    match eval_named statics vars defining_expr with
    | Some v => Step (State body ((x, v) :: vars) conts statics)
    | None => Undefined
    end
  | State (Let_static bindings body) vars conts statics =>
    match eval_static_bindings vars bindings statics with
    | Some statics' => Step (State body vars conts statics')
    | None => Undefined
    end
  | State (Let_cont_non_recursive k h body) vars conts statics =>
    Step (State body vars ((k, Closure h vars conts []) :: conts) statics)
  | State (Let_cont_recursive handlers body) vars conts statics =>
    Step (State body vars (rec_closures handlers vars conts ++ conts) statics)
  | State (Apply ap) vars conts statics =>
    match eval_simple vars (ap_callee ap), eval_simples vars (ap_args ap) with
    | Some callee, Some vs =>
      call_function callee (ap_call_kind ap) vs
        (resolve (ap_continuation ap) conts)
        (resolve (ap_exn_continuation ap) conts) statics
    | _, _ => Undefined
    end
  | State (Apply_cont ac) vars conts statics =>
    match eval_simples vars (ac_args ac) with
    | Some vs => apply_continuation (ac_continuation ac) vs conts statics
    | None => Undefined
    end
  | State (Switch scrutinee arms) vars conts statics =>
    match eval_simple vars scrutinee with
    | Some v =>
      match naked_immediate_of_value v with
      | Some i =>
        match find_arm i arms with
        | Some ac => Step (State (Apply_cont ac) vars conts statics)
        | None => Undefined
        end
      | None => Undefined
      end
    | None => Undefined
    end
  | State Invalid _ _ _ => Undefined
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

(* The same for expressions: under all environments. *)
Definition expr_equivalent (e e' : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env) (statics : static_env),
    equivalent (State e vars conts statics) (State e' vars conts statics).

Definition expr_refines (source target : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env) (statics : static_env),
    refines (State source vars conts statics)
      (State target vars conts statics).

(* A step does not change the behaviour. *)
Definition step_equivalent_statement : Prop :=
  ∀ s s' : state, step s = Step s' -> equivalent s s'.
