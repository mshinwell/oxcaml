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

   This file is to be reviewed: [closure_of], [closure_in_set],
   [project_value_slot], [project_function_slot], [eval_named],
   [eval_static_bindings],
   [apply_cont_value], [call_function] and the rules of [step], then
   [behaves], [equivalent] and [refines]. The values, the static
   environment and the reading of allocated values are in
   FlambdaValueSpec.v, and what the primitives compute is in
   FlambdaPrimitiveSpec.v; this file exports both.

   The semantics is an abstract machine. A state is an expression with an
   environment giving values to variables, one giving closures to
   continuations, and the static environment; [step] is a function, so
   execution is deterministic by construction. A continuation closure keeps
   the environments of its definition, so no substitution is involved and
   binders may shadow.

   The static environment is what [Let_static] has bound so far: the code
   of code ids, and the values that symbols point to. It is global: it is
   not kept in closures, and only grows. A symbol is a value by itself, a
   pointer ([Value_symbol]), whether or not it is bound; what it points to
   is looked up where it is used, as a closure to call or to project
   from. So a group of bindings may be recursive, and static data cyclic.
   A [Let_static] is executed where it stands; nothing lifts it.

   Flambda permits a [Let_static] at the toplevel of a compilation unit
   only: FlambdaWellFormedSpec.v has the condition. The machine keeps
   static bindings out of the two places where one could be executed more
   than once: calling code whose body binds something static is
   undefined, and so is a [Let_cont_recursive] one of whose handlers does
   ([binds_statics]). It also makes undefined binding a code id or a
   symbol that is bound already. So what a name is bound to never changes
   in a run, and what is known of the static environment where a handler
   is defined still holds where it runs. The rest of the condition, that
   the handler of a non-recursive continuation with static bindings
   postdominates its body, is not the machine's to check.

   A continuation with no binding stands for a way out of the term: the
   return or exception continuation of the enclosing unit. Applying one
   ends execution, and the continuation and its arguments are what is
   observed ([Exit]). This is the only observation so far; there is no
   mutable memory and there are no effects.

   A function call ([call_function]) runs the body of the code of the
   closure called, with the code's return and exception continuations
   standing for the caller's. There is no stack.

   A set of closures has functions, each the code of a function slot, and
   value slots, which the functions share. Each closure of the set is a
   value of its own: the set and the function slot the closure is at
   ([Value_closure_of_set]). The closures of one set differ in that slot
   only; a closure does not hold the others. Calling a closure runs the
   code of its slot with [my_closure] bound to that closure, so the
   functions of a set have each their own [my_closure], and reach one
   another by projecting a function slot from it
   ([project_function_slot]): that is how a set is recursive, and no value
   is cyclic. The closures of a static set are symbols, each bound to its
   closure with the symbols of the others ([Static_closure_of_set]);
   projecting a function slot from a symbol gives the symbol of that
   slot. A closure has no identity: two sets made alike are equal.

   The closures of a set of one function whose function slot is not named
   ([Value_closure], [Static_closure]) are those of the fragment before
   function slots. They are read as the closure at
   [unnamed_function_slot] of a set with that one function.

   These definitions can express sets of closures that the compiler does
   not make. In a set the compiler makes, every closure is at a function
   slot of the set, no function slot and no value slot is given twice,
   the functions have each their own code, and the symbols of a static
   set are bound together, each to the closure at its slot. What the
   machine does with the other sets is a choice, not a model of the
   compiler:
   - a closure at a function slot that is not among those of its set is
     not made: making one is undefined
     ([closure_of_set_made_statement],
     [static_closure_of_set_made_statement]). A value of that shape may
     still be in an environment given to a statement; it is not a closure
     ([closure_in_set]), so calling it or projecting from it is undefined;
   - where a function slot or a value slot is given twice, the first of
     the two is the one found, as everywhere in FlambdaMapSpec.v. The
     second is not removed: every value slot is evaluated where the set
     is made, so a second one that has no value makes that undefined,
     and the closure holds both lists as they were given;
   - a set in which two function slots have the same code is made, and
     each of its closures runs that code; so are two static sets of one
     group that have the same code;
   - a closure of code that is not bound is made, and calling it is
     undefined, as for the closures of the fragment before;
   - nothing checks that the symbols a static closure names as those of
     the closures of its set are bound to them. A projection from it
     gives the symbol named, bound or not, as a symbol is a value whether
     or not it is bound. FlambdaClosuresSpec.v says what holds of a set
     whose symbols are bound as [bind_closures] binds them
     ([static_set_bound]).
   A unit that makes only sets such as the compiler's is well-formed
   (FlambdaWellFormedSpec.sets_well_formed, a check, which does not look
   at value slots). The statements of this file are about every term and
   every environment, those that no well-formed unit reaches included;
   FlambdaClosuresSpec.v says what more holds of the run of a
   well-formed unit.

   Execution is undefined ([Undefined]) at [Invalid], at an unbound variable,
   at a continuation or a function applied to the wrong number of
   arguments, at a function called at arities that are not those of its
   code or with arguments that are not of the kinds of the call's arity,
   at a [Switch] whose scrutinee is not a naked immediate with
   an arm, where a primitive has no value, at a call of what is not a
   closure, of a closure whose code is not bound, or directly of a closure
   of other code than the one named, at the projection of a value slot
   from what is not a closure with that slot, at the projection of a
   value slot or of a function slot that names the function slot it
   projects from, from what is not a closure at that function slot of a
   set with the slot asked for, and where a closure is made, by a [Let] or
   statically, at a function slot that is not among those of its set.
   A transformation may do anything to a term whose
   execution is undefined: that is [refines], the statement of correctness
   to use for a transformation; [equivalent] is the stronger, symmetric one.
   [refines_defined_statement] and [refines_antisymmetric_statement] say how
   the two are related.

   Kinds. The kinds and arities that terms carry (FlambdaModel.v) have
   no effect on execution, with one exception: a call ([call_function])
   is undefined unless it agrees with the code called, in the three ways
   given there. Simplify assumes each of them, and a well-typed program
   whose types are refined by a GADT can break the second and the third
   in a branch that is never run.

   The primitives are those of FlambdaPrimitiveModel.v, and
   [FlambdaPrimitiveSpec.eval_prim] says what each computes. A law of a
   primitive (say, that an addition commutes) is a lemma about it.

   The lemmas and the proofs are in FlambdaSemanticsProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2 Require Export FlambdaValueSpec FlambdaPrimitiveSpec.
Import ListNotations.

(* ======================================================================== *)
(* Environments                                                             *)
(* ======================================================================== *)

(* An environment is a finite map of FlambdaMapSpec.v: an association
   list, of which [lookup] finds the first binding of a name. *)
Definition env : Type := list (variable * value).

(* What a continuation is. [Closure] is a continuation handler with the
   environments of its definition. For a handler of a recursive
   [Let_cont], [recursive] is all the handlers of that [Let_cont], which
   are in scope in the handler; it is empty for a non-recursive one.
   [Outer] is a way out of the whole term, by the continuation named. *)
#[local] Set Warnings "-register-all".
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

(* [closure_of] and [closure_in_set] see the same closures: the code of a
   closure is the code of the function slot it is at. *)
Definition closure_in_set_of_statement : Prop :=
  ∀ (statics : static_env) (v : value) (code : code_id)
    (value_slots : list (value_slot * value)),
    closure_of statics v = Some (code, value_slots)
    <-> ∃ (slot : function_slot)
          (function_decls : list (function_slot * code_id)),
          closure_in_set statics v = Some (slot, function_decls, value_slots)
          ∧ lookup slot function_decls = Some code.

(* A closure is at one of the function slots of its set. *)
Definition closure_in_set_slot_statement : Prop :=
  ∀ (statics : static_env) (v : value) (slot : function_slot)
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * value)),
    closure_in_set statics v = Some (slot, function_decls, value_slots) ->
    is_bound slot function_decls = true.

(* A value slot is projected only from a closure at [project_from], and is
   then the value of the slot. *)
Definition project_value_slot_defined_statement : Prop :=
  ∀ (statics : static_env) (project_from : function_slot)
    (slot : value_slot) (v w : value),
    project_value_slot statics project_from slot v = Some w
    <-> ∃ (function_decls : list (function_slot * code_id))
          (value_slots : list (value_slot * value)),
          closure_in_set statics v
          = Some (project_from, function_decls, value_slots)
          ∧ lookup slot value_slots = Some w.

(* A function slot is projected only from a closure at [move_from] of a
   set that has [move_to]. These are necessary conditions: from a symbol
   the projection also needs the set to name a symbol for [move_to]. *)
Definition project_function_slot_defined_statement : Prop :=
  ∀ (statics : static_env) (move_from move_to : function_slot)
    (v w : value),
    project_function_slot statics move_from move_to v = Some w ->
    ∃ (function_decls : list (function_slot * code_id))
      (value_slots : list (value_slot * value)) (code code' : code_id),
      closure_in_set statics v = Some (move_from, function_decls, value_slots)
      ∧ lookup move_from function_decls = Some code
      ∧ lookup move_to function_decls = Some code'.

(* From a closure made by a [Let] it gives the closure of the same set at
   the other slot. *)
Definition project_function_slot_of_set_statement : Prop :=
  ∀ (statics : static_env) (move_from move_to : function_slot)
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * value)) (code code' : code_id),
    lookup move_from function_decls = Some code ->
    lookup move_to function_decls = Some code' ->
    project_function_slot statics move_from move_to
      (Value_closure_of_set move_from function_decls value_slots)
    = Some (Value_closure_of_set move_to function_decls value_slots).

(* CR mshinwell: Making a closure at a function slot that is not among
   those of its set is undefined: the first line of the case
   [Closure_of_set] here, and of [Static_const_closure_of_set] in
   [eval_static_const]. No term of the compiler makes one, and
   FlambdaWellFormedSpec.well_formed_unit refuses a unit that would. The
   other choice is to make the value, which nothing then reads as a
   closure ([closure_of] and [closure_in_set] have no value on it), and
   to leave it to well-formedness. Decision D20. *)

(* CR mshinwell: the projection of a value slot from what is not a closure,
   or from a closure that has not got the slot, is undefined (the cases
   [Project_value_slot] and [Project_value_slot_from] of [eval_named]).
   Simplify makes such a projection [Invalid] where the type of the
   closure shows it. Not certain: whether a term that the compiler builds
   can project, in code that runs, a slot that the closure has not got.
   Decision D3, which is about function slots; this is the same question
   for value slots. *)
Definition eval_named (statics : static_env) (vars : env)
    (defining_expr : named) : option value :=
  match defining_expr with
  | Simple s => eval_simple vars s
  | Prim p args =>
    let* vs := eval_simples vars args in
    eval_prim statics p vs
  | Set_of_closures code value_slots =>
    let* vs := eval_value_slots vars value_slots in
    Some (Value_closure code vs)
  | Closure_of_set slot function_decls value_slots =>
    let* _ := lookup slot function_decls in
    let* vs := eval_value_slots vars value_slots in
    Some (Value_closure_of_set slot function_decls vs)
  | Project_value_slot slot closure =>
    let* v := eval_simple vars closure in
    let* called := closure_of statics v in
    lookup slot (snd called)
  | Project_value_slot_from project_from slot closure =>
    let* v := eval_simple vars closure in
    project_value_slot statics project_from slot v
  | Project_function_slot move_from move_to closure =>
    let* v := eval_simple vars closure in
    project_function_slot statics move_from move_to v
  end.

(* CR mshinwell: As for [Closure_of_set] in [eval_named]: the constant of
   a closure at a function slot that is not among those of its set has
   no value (the first line of the case [Static_const_closure_of_set]),
   so the group that binds it is undefined. Decision D20. *)
Definition eval_static_const (vars : env) (const : static_const)
    : option statically_allocated_value :=
  match const with
  | Static_const_set_of_closures code value_slots =>
    let* vs := eval_value_slots vars value_slots in
    Some (Static_closure code vs)
  | Static_const_closure_of_set slot closure_symbols function_decls
      value_slots =>
    let* _ := lookup slot function_decls in
    let* vs := eval_value_slots vars value_slots in
    Some (Static_closure_of_set slot closure_symbols function_decls vs)
  | Static_const_block tag fields =>
    let* vs := eval_simples vars fields in
    Some (Static_block tag vs)
  | Static_const_boxed_number contents =>
    let* v := eval_simple vars contents in
    Some (Static_boxed_number v)
  | Static_const_immutable_string bytes => Some (Static_string bytes)
  end.

(* What is made at a function slot of a set, by a [Let] or statically, is
   a closure at that slot of that set: a closure at a slot that its set
   has not got is not made. *)
Definition closure_of_set_made_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (slot : function_slot)
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) (v : value),
    eval_named statics vars (Closure_of_set slot function_decls value_slots)
    = Some v ->
    ∃ slot_values : list (value_slot * value),
      eval_value_slots vars value_slots = Some slot_values
      ∧ closure_in_set statics v = Some (slot, function_decls, slot_values).

Definition static_closure_of_set_made_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (slot : function_slot)
    (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) (s : symbol)
    (allocated : statically_allocated_value),
    eval_static_const vars
      (Static_const_closure_of_set slot closure_symbols function_decls
         value_slots)
    = Some allocated ->
    lookup s (static_values statics) = Some allocated ->
    ∃ slot_values : list (value_slot * value),
      eval_value_slots vars value_slots = Some slot_values
      ∧ closure_in_set statics (Value_symbol s)
        = Some (slot, function_decls, slot_values).

(* CR mshinwell: binding a code id or a symbol that is bound already is
   undefined (the two cases of [eval_static_bindings] that find the name),
   so that what a name is bound to never changes. A well-formed unit never
   does it (FlambdaWellFormedSpec.v). Not certain that every unit the
   compiler builds is such: nothing there checks, across a unit, that a
   symbol or a code id is bound once. Discrepancy C0-4; no decision is
   asked yet. *)

(* The static environment with a group of bindings added. Deleted code is
   not bound. A code id or a symbol is bound once: binding one that is
   bound already, by this group or by an earlier one, is undefined. So
   what a name is bound to never changes (FlambdaWellFormedSpec.v). *)
Fixpoint eval_static_bindings (vars : env) (bindings : list static_binding)
    (statics : static_env) : option static_env :=
  match bindings with
  | [] => Some statics
  | Bind_code id c :: bindings =>
    match lookup id (static_code statics) with
    | Some _ => None
    | None =>
      eval_static_bindings vars bindings
        (Static_env ((id, c) :: static_code statics) (static_values statics))
    end
  | Bind_deleted_code _ :: bindings =>
    eval_static_bindings vars bindings statics
  | Bind_symbol s const :: bindings =>
    match lookup s (static_values statics) with
    | Some _ => None
    | None =>
      let* allocated := eval_static_const vars const in
      eval_static_bindings vars bindings
        (Static_env (static_code statics)
           ((s, allocated) :: static_values statics))
    end
  end.

(* CR mshinwell: a call of code whose body binds something static is
   undefined, and so is a recursive [Let_cont] one of whose handlers does
   ([call_function] and [step], by [binds_statics]). For a binding of a
   symbol this follows the compiler, which stops on one that is not at
   toplevel. For a group that binds only code the compiler has no such
   check (simplify/simplify_named.ml, the case [Static_consts]). So if a
   pass leaves code bound inside a function or a loop, the model calls
   undefined a term that the compiler runs. Discrepancy C0-3; no decision
   yet. *)

(* Whether an expression has a [Let_static] that binds something, in its
   body or in a handler. The code that a [Let_static] binds is not looked
   into: it is checked when it is called. *)
Definition binding_binds (binding : static_binding) : bool :=
  match binding with
  | Bind_deleted_code _ => false
  | Bind_code _ _ | Bind_symbol _ _ => true
  end.

Fixpoint binds_statics (e : expr) : bool :=
  match e with
  | Let _ _ _ body => binds_statics body
  | Let_static bindings body =>
    existsb binding_binds bindings || binds_statics body
  | Let_cont_non_recursive _ h body =>
    handler_binds_statics h || binds_statics body
  | Let_cont_recursive handlers body =>
    existsb (fun '(_, h) => handler_binds_statics h) handlers
    || binds_statics body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => false
  end
with handler_binds_statics (h : continuation_handler) : bool :=
  match h with
  | Handler _ _ handler => binds_statics handler
  end.

Definition handlers_bind_statics
    (handlers : list (continuation * continuation_handler)) : bool :=
  existsb (fun '(_, h) => handler_binds_statics h) handlers.

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

(* A state of the machine: the expression to run, the values of its
   variables, what its continuations stand for, and the static
   environment. It is a record, so that a property of a state can name the
   components it is about ([state_statics s]) and say nothing of the
   others. *)
Record state : Type := State {
  state_expr : expr;
  state_vars : env;
  state_conts : cont_env;
  state_statics : static_env
}.

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
  | Closure (Handler params _ handler) def_vars def_conts recursive =>
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
   code named. The body must bind nothing static: it would do so at each
   call.

   The call must agree with the code, in three ways. Simplify assumes
   each: it replaces by [Invalid] a call that fails one
   (simplify/simplify_apply_expr.ml).
   - The values of the arguments are of the kinds that the call's own
     arity gives, unarized ([simplify_apply_shared], which compares the
     kinds of the arguments with [Flambda_arity.unarize] of
     [Apply.args_arity]; the reason is
     [Application_argument_kind_mismatch]). This is the one place where
     the machine looks at the kind of a value. A poison constant has the
     kind it carries, and an allocated value or a symbol, bound or not,
     has kind [Value]: so poison of the right kind passes, and that is
     intended.
   - The arity of the arguments is that of the parameters of the code,
     each parameter unarized ([arity_mismatch], on
     [Flambda_arity.unarize_per_parameter];
     [Direct_application_parameter_kind_mismatch]). One parameter that
     is an unboxed pair is not two parameters; how products are nested
     inside one parameter does not count.
   - The arity of the results that the call expects is that of the
     results of the code, unboxed products and all
     ([simplify_direct_function_call], by
     [Flambda_arity.equal_ignoring_subkinds];
     [Application_result_kind_mismatch]).
   A call with fewer or more arguments than the code has parameters
   fails the second and is undefined. Where the compiler takes such a
   call for a partial application or an over-application, that is an
   omission of this fragment and not undefined behaviour of the program:
   FlambdaWellKindedSpec.v says which calls those are
   ([partial_or_over_application]). *)

(* CR mshinwell: two calls are undefined in [call_function] on trust.
   - A call of a closure whose code is not bound, or is deleted
     ([call_function] finds no code), while the closure itself is made,
     by every form of closure. It cannot be undefined where the closure
     is made, as a group may bind a symbol to a closure before it binds
     the code. It is right if code is deleted only when it is never
     called, which nothing checks; for the term after Simplify it is the
     safe side. It is not decided whether well-formedness is to ask that
     the code of every closure is bound by the time it is called, as it
     is to ask of the symbols a term mentions (decision D8). Decision
     D20.
   - A direct call of a closure of other code than the one named. The
     backend would run the code named, with that closure. Not certain
     where the two code ids are versions of one function: the compiler
     relates them by its code age relation, which the model has not got.
     Discrepancy C0-1; no decision yet. *)
Definition call_function (callee : value) (kind : call_kind)
    (vs : list value) (args_arity return_arity : arity)
    (return_to exn_to : cont_value) (statics : static_env) : step_result :=
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
      if binds_statics (code_body c) then Undefined
      else if
        negb
          (kinds_eqb (map kind_of_value vs) (unarize args_arity)
           && kinds_per_parameter_eqb (unarize_per_parameter args_arity)
                (unarize_per_parameter (code_params_arity c))
           && arity_eqb return_arity (code_result_arity c))
      then Undefined
      else
        match
          bind_params (code_params c) vs [(code_my_closure c, callee)]
        with
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

(* CR mshinwell: a variable bound to a value of another kind than the
   one its binder gives (by a [Let], or as a parameter of a handler) is
   not undefined: the machine does not test it. Nor does it test the
   kind of a field of a static block or of a value slot. (The fields of
   a block that a primitive makes are tested, as arguments of the
   primitive: FlambdaPrimitiveSpec.eval_variadic_primitive.) The
   compiler stops on a term in which it sees such a mismatch, so
   Simplify never turns one into [Invalid], and no well-typed program
   is known to produce one.
   Should a mismatch of kinds be undefined wherever it is executed, the
   machine would test the kind of a value wherever a variable is bound,
   and the rewrites that remove or move a binding would be refinements,
   or equivalences only of bindings whose kind is known. Decision D10. *)

Definition step (s : state) : step_result :=
  match s with
  | State (Let x _ defining_expr body) vars conts statics =>
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
    if handlers_bind_statics handlers then Undefined
    else
      Step
        (State body vars (rec_closures handlers vars conts ++ conts) statics)
  | State (Apply ap) vars conts statics =>
    match eval_simple vars (ap_callee ap), eval_simples vars (ap_args ap) with
    | Some callee, Some vs =>
      call_function callee (ap_call_kind ap) vs (ap_args_arity ap)
        (ap_return_arity ap) (resolve (ap_continuation ap) conts)
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
(* Where a state holds values                                               *)
(* ======================================================================== *)

(* An invariant of a run that is about values (they are well formed, the
   symbols in them are bound) has to hold of every value that a state
   holds. This is where they are, said once: a new place for values, such
   as a heap, is added here.

   [P] is asked of every value that an environment binds, shadowed
   bindings included. *)
Definition env_values_all (P : value -> Prop) (vars : env) : Prop :=
  Forall (fun binding => P (snd binding)) vars.

(* A continuation holds the values of the environment that its closure
   keeps, and those that the continuations it keeps hold. A way out holds
   none. *)
Fixpoint cont_values_all (P : value -> Prop) (c : cont_value) : Prop :=
  match c with
  | Outer _ => True
  | Closure _ vars conts _ =>
    env_values_all P vars
    ∧ fold_right
        (fun binding rest => cont_values_all P (snd binding) ∧ rest) True
        conts
  end.

Definition conts_values_all (P : value -> Prop) (conts : cont_env) : Prop :=
  fold_right (fun binding rest => cont_values_all P (snd binding) ∧ rest)
    True conts.

(* A state holds values in its variables, in the environments that its
   continuations keep, and in its static environment. [P] is asked of
   the values of the first two and [Q] of what each symbol is bound to;
   what is to hold of the values inside a statically allocated value is
   for [Q] to say. Both may depend on the static environment of the
   state. The arguments of an exit are not in a state: the statement
   covers them. *)
Definition state_values_all (P : static_env -> value -> Prop)
    (Q : static_env -> statically_allocated_value -> Prop) (s : state)
    : Prop :=
  env_values_all (P (state_statics s)) (state_vars s)
  ∧ conts_values_all (P (state_statics s)) (state_conts s)
  ∧ Forall (fun binding => Q (state_statics s) (snd binding))
      (static_values (state_statics s)).

(* A step keeps it, and the arguments of an exit satisfy [P], given of
   the state at hand:
   - at a [Let], [P] of the value of the defining expression;
   - at a [Let_static] whose bindings evaluate, that [P] is kept by the
     static environment that results, and [Q] of everything bound in it;
   - at an [Apply] and at an [Apply_cont], [P] of the values of the
     simples that the step reads and passes on: the callee and the
     arguments. The value of a variable satisfies [P] already; this is
     for the constants and the symbols among them, of which [P] need
     not hold in general (a symbol that is not bound).
   What a call or the application of a continuation binds are those
   values, so nothing more is asked for them. *)
Definition step_values_all_statement : Prop :=
  ∀ (P : static_env -> value -> Prop)
    (Q : static_env -> statically_allocated_value -> Prop) (s : state),
    state_values_all P Q s ->
    (∀ (x : variable) (kind : flambda_kind) (defining_expr : named)
       (body : expr) (v : value),
      state_expr s = Let x kind defining_expr body ->
      eval_named (state_statics s) (state_vars s) defining_expr = Some v ->
      P (state_statics s) v) ->
    (∀ (bindings : list static_binding) (body : expr)
       (statics' : static_env),
      state_expr s = Let_static bindings body ->
      eval_static_bindings (state_vars s) bindings (state_statics s)
      = Some statics' ->
      (∀ v : value, P (state_statics s) v -> P statics' v)
      ∧ Forall (fun binding => Q statics' (snd binding))
          (static_values statics')) ->
    (∀ (ap : apply_expr) (callee : value) (vs : list value),
      state_expr s = Apply ap ->
      eval_simple (state_vars s) (ap_callee ap) = Some callee ->
      eval_simples (state_vars s) (ap_args ap) = Some vs ->
      P (state_statics s) callee ∧ Forall (P (state_statics s)) vs) ->
    (∀ (ac : apply_cont) (vs : list value),
      state_expr s = Apply_cont ac ->
      eval_simples (state_vars s) (ac_args ac) = Some vs ->
      Forall (P (state_statics s)) vs) ->
    match step s with
    | Step s' => state_values_all P Q s'
    | Exit _ vs => Forall (P (state_statics s)) vs
    | Undefined => True
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
