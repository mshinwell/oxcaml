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


(* Sets of closures of several functions: first facts.

   This file is to be reviewed: the statements, against the meaning given
   to the closures of a set in FlambdaSemanticsSpec.v ([closure_of],
   [closure_in_set], [project_function_slot]), against the two derived
   forms of FlambdaModel.v ([let_closures], [bind_closures]) and what they
   stand for in the compiler (the [Let] with the bound pattern
   [Bound_pattern.Set_of_closures], and the static binding with the
   pattern [Bound_static.Pattern.Set_of_closures]), and against what
   Simplify knows of a set (simplify/simplify_set_of_closures.ml, where
   each closure gets the type [T.exactly_this_closure], in which the
   closure at every slot of the set is the name bound to it).

   - [let_closures] binds each of its variables to the closure of the set
     at that variable's slot ([let_closures_runs_statement]), in as many
     steps as there are variables; it is undefined where a value slot has
     no value ([let_closures_undefined_statement]).
   - [bind_closures] binds each of its symbols to the closure of the set at
     that symbol's slot ([bind_closures_binds_statement]); once so bound
     ([static_set_bound]) the set stays bound, as nothing static is bound
     twice, and the projection of a function slot from one of its symbols
     is the symbol of that slot ([project_static_set_statement]).
   - The projection of a function slot from a closure whose set is in
     sight is what is bound at that slot: a variable of the [Let]
     ([project_function_slot_let_closures_statement]), a symbol of the
     static binding ([project_function_slot_static_statement]); and the
     projection of a value slot is what the set gives the slot
     ([project_value_slot_static_statement]). This is what Simplify does
     to a projection from a closure of known type.
   - A call of the closure projected from a closure of a set is a direct
     call of the code of the slot ([apply_sibling_statement]): how a
     function of a set calls another, through [my_closure].
   - In a set whose functions have each their own code, the code of a
     closure says which slot it is at
     ([closure_code_determines_slot_statement]). It does not say which
     set: two sets may have the same code.
   - Two units in which two functions call each other through their set
     and read a value slot of it, one with the set made by a [Let] and
     one static, end as they should ([parity_let_statement],
     [parity_static_statement]): the statements above are not about terms
     that are all undefined. Both units are well-formed
     ([parity_well_formed_statement]). A third binds one only of the two
     symbols of the static set, and is not
     ([partial_static_set_statement]).

   The static statements ask that the set is bound as [bind_closures]
   binds it. The semantics does not enforce that of a static environment:
   a symbol may be bound to a closure that names, as the symbol of
   another slot, a symbol bound to anything, or to nothing. A well-formed
   unit (FlambdaWellFormedSpec.well_formed_unit) does not do that:
   - in every state of its run, the symbols of every static set are bound
     to the closures of the set ([well_formed_sets_bound_statement],
     [static_sets_bound]), and then the projection of a function slot,
     where it has a value, is a closure of the same set at the slot asked
     for ([project_function_slot_bound_statement]);
   - it never makes a closure at a function slot that its set has not
     got, which the machine makes undefined
     ([well_formed_makes_closures_statement]).
   Statements about all environments, such as those above with
   [expr_equivalent], hold also of environments that no well-formed unit
   reaches. There they say what the machine does, which is a choice
   (FlambdaSemanticsSpec.v); they need no premise to be true, and a
   statement that is true only of sets that are bound takes
   [static_set_bound] or [static_sets_bound] as a premise.

   Such environments may also hold values of the shape of a closure of a
   set that no term makes: at a function slot that its set has not got,
   or of a set in which a function slot or a code id is given twice. A
   value is valid ([value_valid]) when no closure in it is so, and what a
   symbol is bound to is valid ([allocated_valid]) when the values in it
   are and, for a closure of a static set, the set is so made and names a
   symbol for each of its function slots. This is about the shape of
   values only, not about whether the code or the symbols they name are
   bound.
   - A valid value that is a closure is at a function slot of a set whose
     function slots are distinct and whose functions have each their own
     code ([closure_in_set_valid_statement]); so the code it runs says
     which slot it is at ([closure_code_determines_slot_statement]).
   - Where what the symbols are bound to is valid, the projection of a
     function slot from a closure at the slot named has a value whenever
     the set has the slot asked for
     ([project_function_slot_valid_statement]).
   - Evaluation makes valid values out of valid ones: a defining
     expression whose set is well-formed ([eval_named_valid_statement]),
     a static constant whose binding passes the check of static sets
     ([eval_static_const_valid_statement]).
   - Every state of the run of a well-formed unit holds valid values
     only, and the run ends with valid values
     ([well_formed_values_valid_statement],
     [well_formed_exit_valid_statement]). So a well-formed unit never
     holds a value of the shapes above, and the facts about valid values
     hold wherever it goes. In particular a closure that it calls is at
     the only slot of its set that has the code called
     ([well_formed_closure_slot_statement]).
   - A call binds [my_closure] to the closure called, where [my_closure]
     is not also a parameter of the code
     ([call_binds_my_closure_statement]). [well_formed_unit] does not ask
     that yet, so that [my_closure] is at the slot of the code that runs
     is said here of such code only.

   The proofs are in FlambdaClosuresProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaWellFormedSpec.
Import ListNotations.

(* ======================================================================== *)
(* A set of closures made by a [Let]                                        *)
(* ======================================================================== *)

(* What [let_closures] adds to the environment: each variable bound to the
   closure at the slot of the function in its position, the last bound
   first. *)
Definition closures_bound (bound_vars : list variable)
    (function_decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value)) : env :=
  rev
    (map
       (fun '(x, (slot, _)) =>
          (x, Value_closure_of_set slot function_decls slot_values))
       (combine bound_vars function_decls)).

Definition let_closures_runs_statement : Prop :=
  ∀ (bound_vars : list variable)
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) (body e : expr) (vars : env)
    (conts : cont_env) (statics : static_env)
    (slot_values : list (value_slot * value)),
    let_closures bound_vars function_decls value_slots body = Some e ->
    distinct bound_vars = true ->
    eval_value_slots vars value_slots = Some slot_values ->
    run (length bound_vars) (State e vars conts statics)
    = Step
        (State body
           (closures_bound bound_vars function_decls slot_values ++ vars)
           conts statics).

Definition let_closures_undefined_statement : Prop :=
  ∀ (bound_vars : list variable)
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) (body e : expr) (vars : env)
    (conts : cont_env) (statics : static_env),
    let_closures bound_vars function_decls value_slots body = Some e ->
    eval_value_slots vars value_slots = None ->
    step (State e vars conts statics) = Undefined.

(* In the scope of the [Let] of a set, the projection of a function slot
   from one of its closures is the variable bound at that slot. *)
Definition project_function_slot_let_closures_statement : Prop :=
  ∀ (bound_vars : list variable)
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple))
    (move_from move_to : function_slot) (x_from x_to y : variable)
    (kind : flambda_kind) (code code' : code_id) (i j : nat)
    (body e e' : expr),
    distinct bound_vars = true ->
    nth_error bound_vars i = Some x_from ->
    nth_error function_decls i = Some (move_from, code) ->
    nth_error bound_vars j = Some x_to ->
    nth_error function_decls j = Some (move_to, code') ->
    let_closures bound_vars function_decls value_slots
      (Let y kind (Project_function_slot move_from move_to (Var x_from))
         body)
    = Some e ->
    let_closures bound_vars function_decls value_slots
      (Let y kind (Simple (Var x_to)) body)
    = Some e' ->
    expr_equivalent e e'.

(* A call of the closure projected from a closure of a set made by a
   [Let] is a direct call of the code of the slot projected. *)
Definition apply_sibling_statement : Prop :=
  ∀ (x : variable) (kind : flambda_kind)
    (move_from move_to : function_slot) (closure : simple)
    (args : list simple) (k exn : continuation)
    (args_arity return_arity : arity)
    (function_decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value)) (code : code_id) (vars : env)
    (conts : cont_env) (statics : static_env),
    eval_simple vars closure
    = Some (Value_closure_of_set move_from function_decls slot_values) ->
    lookup move_to function_decls = Some code ->
    equivalent
      (State
         (Let x kind (Project_function_slot move_from move_to closure)
            (Apply
               (Apply_expr (Var x) Indirect args k exn args_arity
                  return_arity)))
         vars conts statics)
      (State
         (Let x kind (Project_function_slot move_from move_to closure)
            (Apply
               (Apply_expr (Var x) (Direct code) args k exn args_arity
                  return_arity)))
         vars conts statics).

(* ======================================================================== *)
(* A static set of closures                                                 *)
(* ======================================================================== *)

(* A static environment binds the symbols of a set to its closures, each
   to the closure at its slot. *)
Definition static_set_bound (statics : static_env)
    (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value)) : Prop :=
  ∀ (slot : function_slot) (s : symbol),
    (slot, s) ∈ closure_symbols ->
    lookup s (static_values statics)
    = Some
        (Static_closure_of_set slot closure_symbols function_decls
           slot_values).

Definition bind_closures_binds_statement : Prop :=
  ∀ (vars : env) (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple))
    (slot_values : list (value_slot * value)) (statics extended : static_env),
    eval_value_slots vars value_slots = Some slot_values ->
    eval_static_bindings vars
      (bind_closures closure_symbols function_decls value_slots) statics
    = Some extended ->
    static_set_bound extended closure_symbols function_decls slot_values.

Definition static_set_bound_extend_statement : Prop :=
  ∀ (statics statics' : static_env)
    (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value)),
    static_set_bound statics closure_symbols function_decls slot_values ->
    statics_extend statics statics' ->
    static_set_bound statics' closure_symbols function_decls slot_values.

(* The projection of a function slot from a symbol of a set that is bound
   is the symbol of that slot, which is the closure of the set there. *)
Definition project_static_set_statement : Prop :=
  ∀ (statics : static_env)
    (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value))
    (move_from move_to : function_slot) (s s' : symbol)
    (code code' : code_id),
    static_set_bound statics closure_symbols function_decls slot_values ->
    (move_from, s) ∈ closure_symbols ->
    lookup move_to closure_symbols = Some s' ->
    lookup move_from function_decls = Some code ->
    lookup move_to function_decls = Some code' ->
    project_function_slot statics move_from move_to (Value_symbol s)
    = Some (Value_symbol s')
    ∧ closure_in_set statics (Value_symbol s')
      = Some (move_to, function_decls, slot_values).

(* The same of terms, with the binding of the set in sight. *)
Definition project_function_slot_static_statement : Prop :=
  ∀ (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple))
    (move_from move_to : function_slot) (s s' : symbol)
    (code code' : code_id) (x : variable) (kind : flambda_kind)
    (body : expr),
    (move_from, s) ∈ closure_symbols ->
    lookup move_to closure_symbols = Some s' ->
    lookup move_from function_decls = Some code ->
    lookup move_to function_decls = Some code' ->
    expr_equivalent
      (Let_static (bind_closures closure_symbols function_decls value_slots)
         (Let x kind (Project_function_slot move_from move_to (Symbol s))
            body))
      (Let_static (bind_closures closure_symbols function_decls value_slots)
         (Let x kind (Simple (Symbol s')) body)).

(* The projection of a value slot from a symbol of a static set, with
   the binding of the set in sight, is what the set gives the slot. *)
Definition project_value_slot_static_statement : Prop :=
  ∀ (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple))
    (project_from : function_slot) (s : symbol) (code : code_id)
    (slot : value_slot) (contents : simple) (x : variable)
    (kind : flambda_kind) (body : expr),
    (project_from, s) ∈ closure_symbols ->
    lookup project_from function_decls = Some code ->
    lookup slot value_slots = Some contents ->
    expr_equivalent
      (Let_static (bind_closures closure_symbols function_decls value_slots)
         (Let x kind (Project_value_slot_from project_from slot (Symbol s))
            body))
      (Let_static (bind_closures closure_symbols function_decls value_slots)
         (Let x kind (Simple contents) body)).

(* In a set whose functions have each their own code, as those of a
   well-formed unit have, the code that a closure runs says which
   function slot the closure is at. *)
Definition closure_code_determines_slot_statement : Prop :=
  ∀ (statics : static_env) (v : value) (slot slot' : function_slot)
    (function_decls : list (function_slot * code_id))
    (value_slots value_slots' : list (value_slot * value)) (code : code_id),
    closure_in_set statics v = Some (slot, function_decls, value_slots) ->
    distinct (map snd function_decls) = true ->
    closure_of statics v = Some (code, value_slots') ->
    lookup slot' function_decls = Some code ->
    slot' = slot.

(* ======================================================================== *)
(* The sets of a well-formed unit                                           *)
(* ======================================================================== *)

(* The state is one at which the machine is undefined because the closure
   to be made is at a function slot that its set has not got. *)
Definition makes_closure_outside_set (s : state) : bool :=
  match state_expr s with
  | Let _ _ (Closure_of_set slot function_decls _) _ =>
    negb (is_bound slot function_decls)
  | Let_static bindings _ =>
    existsb
      (fun binding =>
         match binding with
         | Bind_symbol _
             (Static_const_closure_of_set slot _ function_decls _) =>
           negb (is_bound slot function_decls)
         | _ => false
         end)
      bindings
  | _ => false
  end.

Definition well_formed_makes_closures_statement : Prop :=
  ∀ (unit_exn : continuation) (e : expr) (n : nat) (s : state),
    well_formed_unit unit_exn e = true ->
    run n (State e [] [] empty_static_env) = Step s ->
    makes_closure_outside_set s = false.

(* Every symbol bound to a closure of a static set is the symbol that the
   set has for the slot of that closure, and the symbols of the set are
   bound to its closures. *)
Definition static_sets_bound (statics : static_env) : Prop :=
  ∀ (s : symbol) (slot : function_slot)
    (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value)),
    lookup s (static_values statics)
    = Some
        (Static_closure_of_set slot closure_symbols function_decls
           slot_values) ->
    lookup slot closure_symbols = Some s
    ∧ static_set_bound statics closure_symbols function_decls slot_values.

Definition well_formed_sets_bound_statement : Prop :=
  ∀ (unit_exn : continuation) (e : expr) (n : nat) (s : state),
    well_formed_unit unit_exn e = true ->
    run n (State e [] [] empty_static_env) = Step s ->
    static_sets_bound (state_statics s).

(* Where the static sets are bound, the projection of a function slot is
   a closure of the same set, at the slot asked for. *)
Definition project_function_slot_bound_statement : Prop :=
  ∀ (statics : static_env) (move_from move_to : function_slot)
    (v w : value),
    static_sets_bound statics ->
    project_function_slot statics move_from move_to v = Some w ->
    ∃ (function_decls : list (function_slot * code_id))
      (slot_values : list (value_slot * value)),
      closure_in_set statics v = Some (move_from, function_decls, slot_values)
      ∧ closure_in_set statics w = Some (move_to, function_decls, slot_values).

(* ======================================================================== *)
(* Valid values                                                             *)
(* ======================================================================== *)

(* A value is valid when every closure of a set in it is at a function
   slot of its set, whose function slots are distinct and whose functions
   have each their own code ([set_well_formed]), and so on through the
   values of the value slots of a closure and the fields of a block. A
   symbol is valid whatever it is bound to, and whether or not it is
   bound: what a symbol is bound to is asked to be valid where it is
   bound ([allocated_valid]). So this says nothing of whether the symbols
   or the code that a value names are bound. *)
Fixpoint value_valid (v : value) : bool :=
  match v with
  | Value_const _ | Value_symbol _ | Value_boxed_number _ => true
  | Value_closure _ value_slots =>
    forallb (fun '(_, contents) => value_valid contents) value_slots
  | Value_closure_of_set slot function_decls value_slots =>
    set_well_formed slot function_decls
    && forallb (fun '(_, contents) => value_valid contents) value_slots
  | Value_block _ fields => forallb value_valid fields
  end.

(* What a symbol is bound to is valid when the values in it are, and, if
   it is a closure of a set, when it is at a function slot of its set,
   whose function slots are distinct and whose functions have each their
   own code, and the set names a symbol for each of its function slots,
   in their order. *)
Definition allocated_valid (allocated : statically_allocated_value) : bool :=
  match allocated with
  | Static_closure _ value_slots =>
    forallb (fun '(_, contents) => value_valid contents) value_slots
  | Static_closure_of_set slot closure_symbols function_decls value_slots =>
    set_well_formed slot function_decls
    && (if
          list_eq_dec Pos.eq_dec (map fst closure_symbols)
            (map fst function_decls)
        then true
        else false)
    && forallb (fun '(_, contents) => value_valid contents) value_slots
  | Static_block _ fields => forallb value_valid fields
  | Static_boxed_number contents => value_valid contents
  | Static_string _ => true
  end.

(* Every value of the environment is valid, those that a later binding of
   the same variable hides included. *)
Definition env_valid (vars : env) : Prop :=
  env_values_all (fun v => value_valid v = true) vars.

(* Everything that a symbol is bound to is valid. *)
Definition statics_valid (statics : static_env) : Prop :=
  Forall (fun binding => allocated_valid (snd binding) = true)
    (static_values statics).

(* Every value that the state holds is valid: those of its variables and
   of the environments that its continuations keep, and what each symbol
   is bound to (FlambdaSemanticsSpec.state_values_all, which says where a
   state holds values). *)
Definition state_valid (s : state) : Prop :=
  state_values_all (fun _ v => value_valid v = true)
    (fun _ allocated => allocated_valid allocated = true) s.

(* A valid value that is a closure, made by a [Let] or bound to a symbol,
   is at a function slot of a set whose function slots are distinct and
   whose functions have each their own code, and the values of its value
   slots are valid. *)
Definition closure_in_set_valid_statement : Prop :=
  ∀ (statics : static_env) (v : value) (slot : function_slot)
    (function_decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value)),
    statics_valid statics ->
    value_valid v = true ->
    closure_in_set statics v = Some (slot, function_decls, slot_values) ->
    set_well_formed slot function_decls = true
    ∧ ∀ (w : value_slot) (contents : value),
        (w, contents) ∈ slot_values -> value_valid contents = true.

(* Where what the symbols are bound to is valid, the projection of a
   function slot from a closure has a value whenever the closure is at
   the slot named and its set has the slot asked for: from a symbol too,
   as a valid static set names a symbol for each of its function slots.
   [project_function_slot_bound_statement] says what the value is. *)
Definition project_function_slot_valid_statement : Prop :=
  ∀ (statics : static_env) (move_from move_to : function_slot) (v : value)
    (function_decls : list (function_slot * code_id))
    (slot_values : list (value_slot * value)),
    statics_valid statics ->
    closure_in_set statics v = Some (move_from, function_decls, slot_values) ->
    is_bound move_to function_decls = true ->
    ∃ w : value, project_function_slot statics move_from move_to v = Some w.

(* The value of a defining expression is valid, where the values of the
   environment and what the symbols are bound to are, and the set of a
   closure that the expression makes is well-formed. A primitive gives a
   valid value because it makes its value out of its arguments
   (FlambdaPrimitiveSpec.eval_prim_preserves_statement). *)
Definition eval_named_valid_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (d : named) (v : value),
    named_sets_well_formed d = true ->
    env_valid vars ->
    statics_valid statics ->
    eval_named statics vars d = Some v ->
    value_valid v = true.

(* What a static constant allocates is valid, where the values of the
   environment are and the binding of the constant passes the check of
   static sets ([static_set_whole], whatever the group). *)
Definition eval_static_const_valid_statement : Prop :=
  ∀ (bindings : list static_binding) (s : symbol) (const : static_const)
    (vars : env) (allocated : statically_allocated_value),
    static_set_whole bindings (Bind_symbol s const) = true ->
    env_valid vars ->
    eval_static_const vars const = Some allocated ->
    allocated_valid allocated = true.

(* ======================================================================== *)
(* The values of a well-formed unit                                         *)
(* ======================================================================== *)

(* Every state of the run of a well-formed unit holds valid values only,
   and if the run ends, it ends with valid values. *)
Definition well_formed_values_valid_statement : Prop :=
  ∀ (unit_exn : continuation) (e : expr) (n : nat) (s : state),
    well_formed_unit unit_exn e = true ->
    run n (State e [] [] empty_static_env) = Step s ->
    state_valid s.

Definition well_formed_exit_valid_statement : Prop :=
  ∀ (unit_exn : continuation) (e : expr) (n : nat) (k : continuation)
    (vs : list value),
    well_formed_unit unit_exn e = true ->
    run n (State e [] [] empty_static_env) = Exit k vs ->
    ∀ v : value, v ∈ vs -> value_valid v = true.

(* In the run of a well-formed unit, a closure that a simple stands for
   is at the only function slot of its set that has the code which a
   call of it runs. Of the callee of a call this says that the closure
   called is at the slot of the code called, whichever closure of the
   set it is. It does not say which set that is: two sets may have the
   same code.

   It says nothing by itself of [my_closure] in the body of that code.
   A call binds [my_closure] to the closure called and then the
   parameters to the arguments (FlambdaSemanticsSpec.call_function), so
   a parameter of the same name as [my_closure] hides it, and
   [well_formed_unit] does not ask today that there is none: that the
   binders of code are distinct is a condition of well-formedness still
   to come. Where [my_closure] is not a parameter, the body starts with
   it bound to the closure called ([call_binds_my_closure_statement]),
   and then [my_closure] is at the slot of the code that runs. *)
Definition well_formed_closure_slot_statement : Prop :=
  ∀ (unit_exn : continuation) (e : expr) (n : nat) (s : state)
    (closure : simple) (v : value) (slot slot' : function_slot)
    (function_decls : list (function_slot * code_id))
    (slot_values slot_values' : list (value_slot * value)) (code : code_id),
    well_formed_unit unit_exn e = true ->
    run n (State e [] [] empty_static_env) = Step s ->
    eval_simple (state_vars s) closure = Some v ->
    closure_in_set (state_statics s) v
    = Some (slot, function_decls, slot_values) ->
    closure_of (state_statics s) v = Some (code, slot_values') ->
    lookup slot' function_decls = Some code ->
    slot' = slot.

(* A call that has a step runs the body of the code of the closure
   called, and, where [my_closure] is not also a parameter of that code,
   with [my_closure] bound to the closure called. *)
Definition call_binds_my_closure_statement : Prop :=
  ∀ (callee : value) (kind : call_kind) (vs : list value)
    (args_arity return_arity : arity) (return_to exn_to : cont_value)
    (statics : static_env) (s : state) (called : code_id)
    (slot_values : list (value_slot * value)) (c : code),
    call_function callee kind vs args_arity return_arity return_to exn_to
      statics
    = Step s ->
    closure_of statics callee = Some (called, slot_values) ->
    lookup called (static_code statics) = Some c ->
    among (code_my_closure c) (code_params c) = false ->
    state_expr s = code_body c
    ∧ lookup (code_my_closure c) (state_vars s) = Some callee.

(* ======================================================================== *)
(* An example: two functions that call each other                           *)
(* ======================================================================== *)

(* The parity of a number from 0 to 3, by two functions of one set that
   call each other: [even n] is 1 at 0 and [odd (n - 1)] otherwise, and
   [odd n] is 0 at 0 and [even (n - 1)] otherwise. There is no arithmetic
   (the primitives are abstract): the [Switch] gives the predecessor. A
   function reaches the other by projecting its function slot from
   [my_closure], and reads its answer at 0 from a value slot of the set,
   also through [my_closure]. Numbers and answers are naked immediates,
   and the code, the handlers and the calls say so. *)
Section Parity.

Let n : variable := 1%positive.
Let my_closure : variable := 2%positive.
Let predecessor : variable := 3%positive.
Let other_closure : variable := 4%positive.
Let answer_at_zero : variable := 5%positive.
Let ret : continuation := 1%positive.
Let exn : continuation := 2%positive.
Let call_other : continuation := 3%positive.
Let at_zero : continuation := 4%positive.

Definition parity_kind : flambda_kind := Naked_number Kind_naked_immediate.

Definition parity_arity : arity := [Singleton parity_kind].

Definition parity_code (this other : function_slot)
    (answer_slot : value_slot) : code :=
  Code [n] my_closure ret exn (make_code_metadata parity_arity parity_arity)
    (Let_cont_non_recursive call_other
       (Handler [predecessor] (make_handler_metadata [parity_kind])
          (Let other_closure Value
             (Project_function_slot this other (Var my_closure))
             (Apply
                (Apply_expr (Var other_closure) Indirect [Var predecessor]
                   ret exn parity_arity parity_arity))))
       (Let_cont_non_recursive at_zero
          (Handler [] (make_handler_metadata [])
             (Let answer_at_zero parity_kind
                (Project_value_slot_from this answer_slot (Var my_closure))
                (Apply_cont (Apply_cont_expr ret [Var answer_at_zero]))))
          (Switch (Var n)
             [(0%Z, Apply_cont_expr at_zero []);
              (1%Z, Apply_cont_expr call_other [Const (Naked_immediate 0)]);
              (2%Z, Apply_cont_expr call_other [Const (Naked_immediate 1)]);
              (3%Z, Apply_cont_expr call_other [Const (Naked_immediate 2)])]))).

Definition even_slot : function_slot := 1%positive.
Definition odd_slot : function_slot := 2%positive.
Definition even_code : code_id := 1%positive.
Definition odd_code : code_id := 2%positive.
Definition even_at_zero : value_slot := 1%positive.
Definition odd_at_zero : value_slot := 2%positive.

Definition parity_decls : list (function_slot * code_id) :=
  [(even_slot, even_code); (odd_slot, odd_code)].

Definition parity_value_slots : list (value_slot * simple) :=
  [(even_at_zero, Const (Naked_immediate 1));
   (odd_at_zero, Const (Naked_immediate 0))].

Definition parity_code_bindings : list static_binding :=
  [Bind_code even_code (parity_code even_slot odd_slot even_at_zero);
   Bind_code odd_code (parity_code odd_slot even_slot odd_at_zero)].

Let even : variable := 1%positive.
Let odd : variable := 2%positive.
Let done : continuation := 1%positive.
Let error : continuation := 2%positive.

(* The set made by a [Let], and [odd] called on [i]. *)
Definition parity_let (i : Z) : option expr :=
  option_map (Let_static parity_code_bindings)
    (let_closures [even; odd] parity_decls parity_value_slots
       (Apply
          (Apply_expr (Var odd) Indirect [Const (Naked_immediate i)] done
             error parity_arity parity_arity))).

Definition even_symbol : symbol := 1%positive.
Definition odd_symbol : symbol := 2%positive.

(* The set bound statically, and [odd] called on [i]. *)
Definition parity_static (i : Z) : expr :=
  Let_static
    (parity_code_bindings
     ++ bind_closures [(even_slot, even_symbol); (odd_slot, odd_symbol)]
          parity_decls parity_value_slots)
    (Apply
       (Apply_expr (Symbol odd_symbol) (Direct odd_code)
          [Const (Naked_immediate i)] done error parity_arity
          parity_arity)).

(* Run on their own, both say that 3 is odd and that 2 is not. *)
Definition parity_let_statement : Prop :=
  ∀ (i answer : Z),
    (i, answer) ∈ [(3%Z, 1%Z); (2%Z, 0%Z)] ->
    ∃ e : expr,
      parity_let i = Some e
      ∧ behaves (State e [] [] empty_static_env)
          (Exits done [Value_const (Naked_immediate answer)]).

Definition parity_static_statement : Prop :=
  ∀ (i answer : Z),
    (i, answer) ∈ [(3%Z, 1%Z); (2%Z, 0%Z)] ->
    behaves (State (parity_static i) [] [] empty_static_env)
      (Exits done [Value_const (Naked_immediate answer)]).

(* Both are well-formed units: the statements about well-formed units
   are about some unit with a set of two functions. The argument [i] is
   a naked immediate of the unit, so it has to be one: a well-formed
   unit has its numbers in range. *)
Definition parity_well_formed_statement : Prop :=
  ∀ i : Z,
    ocaml_int_in_range i = true ->
    well_formed_unit error (parity_static i) = true
    ∧ ∃ e : expr, parity_let i = Some e ∧ well_formed_unit error e = true.

(* The static set with one of its two symbols bound, and the other
   projected from it. *)
Definition parity_partial : expr :=
  Let_static
    (parity_code_bindings
     ++ [Bind_symbol even_symbol
           (Static_const_closure_of_set even_slot
              [(even_slot, even_symbol); (odd_slot, odd_symbol)] parity_decls
              parity_value_slots)])
    (Let odd Value
       (Project_function_slot even_slot odd_slot (Symbol even_symbol))
       (Apply_cont (Apply_cont_expr done [Var odd]))).

(* The machine gives the symbol that the set names for the other slot,
   which is bound to nothing. The unit is not well-formed. *)
Definition partial_static_set_statement : Prop :=
  behaves (State parity_partial [] [] empty_static_env)
    (Exits done [Value_symbol odd_symbol])
  ∧ well_formed_unit error parity_partial = false.

End Parity.
