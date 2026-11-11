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

(* The terms of Flambda 2 as the semantics sees them: a fragment.

   This file is to be reviewed, against middle_end/flambda2/terms/flambda.mli
   and the modules it refers to. It holds definitions only. The fragment has
   - the constants ([Reg_width_const.t]), in full but for the string of
     [Poison]; the kinds ([Flambda_kind.t]) are in FlambdaKindModel.v;
   - [Let] of one variable, bound to a [Simple], a primitive application, a
     closure of a new set of closures, or the projection of a value slot
     or of a function slot; the primitives ([Flambda_primitive.t]) are in
     FlambdaPrimitiveModel.v, a fragment of their own;
   - [Let] with the bound pattern [Static] ("let symbol"), here
     [Let_static]: a group of bindings of code ids to code and of symbols
     to static constants;
   - [Let_cont], non-recursive and recursive;
   - [Apply] of a function, direct or indirect, with a return continuation
     and an exception continuation;
   - [Apply_cont];
   - [Switch];
   - [Invalid].

   What is left out, and is to be added in later steps:
   - of a set of closures: a function slot whose code is deleted
     ([Function_declarations.Deleted]), the allocation mode (a set on the
     stack is not told from one on the heap), [only_full_applications],
     and everything about its layout in memory;
   - the static constants that are arrays or float blocks, and mutable
     blocks and strings;
   - [Rec_info];
   - the other call kinds (methods, C calls, effects), [Never_returns],
     partial and over-application, and the modes, arities and inlining
     attributes of an [Apply];
   - trap actions on [Apply_cont], and the [is_exn_handler] and [is_cold]
     flags of continuation handlers;
   - the kinds of bound parameters and of results, subkinds, debuginfo, and
     every annotation that has no effect on execution. The kinds are
     defined, and a constant has one ([kind_of_const]), but no term
     carries a kind yet and nothing is said to be well-kinded.

   Differences of presentation from the compiler:
   - Variables and continuations are plain names. The compiler works up to
     alpha-equivalence ([Name_abstraction]); here a binder shadows, and the
     semantics (FlambdaSemanticsSpec.v) uses environments and closures, so
     no substitution and no freshness condition is needed to define
     execution. Symbols and code ids are plain names in the compiler too.
   - The two forms of [Let_cont] are two constructors of [expr], and the
     [Let] of static constants a third, [Let_static].
   - A [Let_static] pairs each name with what it is bound to
     ([static_binding]), where the compiler has a [Bound_static.t] and a
     [Static_const_group.t] side by side.
   - A recursive [Let_cont] in the compiler has [invariant_params] shared
     by all its handlers; here every handler lists all its parameters, the
     invariant ones first.
   - A primitive application is a primitive with a list of arguments, where
     [Flambda_primitive.t] holds the arguments by arity. A primitive
     applied to the wrong number of arguments has no value
     (FlambdaPrimitiveSpec.v).
   - [Project_value_slot] and [Project_function_slot], unary primitives in
     the compiler, are forms of [named] of their own, as their meaning is
     fixed by that of closures.
   - A set of closures has two presentations. [Set_of_closures] and
     [Static_const_set_of_closures] are a set of one function, whose
     function slot is not named; [Project_value_slot] projects from a
     closure whatever function slot it is at. [Closure_of_set] and
     [Static_const_closure_of_set] are a set of any number of functions,
     each at a named function slot; [Project_value_slot_from] is the
     compiler's projection of a value slot, which names the function slot
     of the closure it projects from ([project_from]).
   - A [Let] binds one variable. The compiler's [Let] of a set of closures
     binds one variable to each closure of the set
     ([Bound_pattern.Set_of_closures]); here it is [let_closures]: a [Let]
     of the first closure, and for each other closure a [Let] of its
     projection from the first. Closures have no identity, so this is the
     same.
   - Likewise a [Let_static] binds one symbol to each closure of a static
     set by a [Bind_symbol] of its own, which repeats the set and says
     which symbols its other closures are bound to; the compiler binds
     them all with one pattern ([Bound_static.Pattern.Set_of_closures]).
   - Of the names in the forms of a set, a renaming acts on the variables
     only: those of the value slots and of the closure projected from,
     and the variables that [let_closures] binds, each by a [Let].
     Function slots and value slots are not renamed, here or in the
     compiler. Nor are the code ids of the functions and the symbols of
     the closures of a static set, like every code id and symbol of the
     model: the compiler's [Bound_pattern.Static] does not permute the
     names it binds either.
   - The callee of an [Apply] is always given, where the compiler may omit
     it for a direct call.
   - The numbers in constants are integers: those of the floats and
     vectors are bit patterns, as in the compiler. No type here
     restricts one to its range, nor a tag, nor any other number of a
     term: FlambdaPrimitiveSpec.v says what the ranges are, and
     FlambdaWellFormedSpec.numbers_in_range is the check that every
     number of a term is in its range. *)

From Stdlib Require Import ZArith List.
From OxCamlFlambda2 Require Export FlambdaKindModel FlambdaPrimitiveModel.
Import ListNotations.

(* [Variable.t], [Continuation.t], [Symbol.t], [Code_id.t], [Value_slot.t]
   and [Function_slot.t]. *)
Definition variable : Type := positive.
Definition continuation : Type := positive.
Definition symbol : Type := positive.
Definition code_id : Type := positive.
Definition value_slot : Type := positive.
Definition function_slot : Type := positive.

(* ======================================================================== *)
(* Constants                                                                *)
(* ======================================================================== *)

(* [Reg_width_const.t]. *)
Inductive const : Type :=
  | Naked_immediate (i : Z)
  | Tagged_immediate (i : Z)
  | Naked_float32 (bits : Z)
  | Naked_float (bits : Z)
  | Naked_int8 (i : Z)
  | Naked_int16 (i : Z)
  | Naked_int32 (i : Z)
  | Naked_int64 (i : Z)
  | Naked_nativeint (i : Z)
  | Naked_vec128 (bits : Z)
  | Naked_vec256 (bits : Z)
  | Naked_vec512 (bits : Z)
  | Naked_mask (bits : Z)
  | Null
  | Poison (kind : flambda_kind).

(* [Reg_width_const.kind]. *)
Definition kind_of_const (c : const) : flambda_kind :=
  match c with
  | Naked_immediate _ => Naked_number Kind_naked_immediate
  | Tagged_immediate _ => Value
  | Naked_float32 _ => Naked_number Kind_naked_float32
  | Naked_float _ => Naked_number Kind_naked_float
  | Naked_int8 _ => Naked_number Kind_naked_int8
  | Naked_int16 _ => Naked_number Kind_naked_int16
  | Naked_int32 _ => Naked_number Kind_naked_int32
  | Naked_int64 _ => Naked_number Kind_naked_int64
  | Naked_nativeint _ => Naked_number Kind_naked_nativeint
  | Naked_vec128 _ => Naked_number Kind_naked_vec128
  | Naked_vec256 _ => Naked_number Kind_naked_vec256
  | Naked_vec512 _ => Naked_number Kind_naked_vec512
  | Naked_mask _ => Naked_number Kind_naked_mask
  | Null => Value
  | Poison kind => kind
  end.

(* ======================================================================== *)
(* Terms                                                                    *)
(* ======================================================================== *)

(* [Simple.t], without coercions. *)
Inductive simple : Type :=
  | Var (x : variable)
  | Symbol (s : symbol)
  | Const (c : const).

(* [Flambda.named]. A [Set_of_closures] has one function, given by its
   code, and the values of its value slots.

   [Closure_of_set] is the closure at [slot] of a new set of closures
   ([Set_of_closures.t]): [function_decls] are its functions, the code of
   each function slot in the order of [Function_declarations.funs_in_order],
   and [value_slots] the values of its value slots, which its functions
   share. [Project_value_slot_from] is the value of a value slot of the
   set of which [closure] is the closure at [project_from], and
   [Project_function_slot] the closure at [move_to] of the set of which
   [closure] is the closure at [move_from]. *)
Inductive named : Type :=
  | Simple (s : simple)
  | Prim (p : prim) (args : list simple)
  | Set_of_closures (code : code_id)
      (value_slots : list (value_slot * simple))
  | Closure_of_set (slot : function_slot)
      (function_decls : list (function_slot * code_id))
      (value_slots : list (value_slot * simple))
  | Project_value_slot (slot : value_slot) (closure : simple)
  | Project_value_slot_from (project_from : function_slot)
      (slot : value_slot) (closure : simple)
  | Project_function_slot (move_from move_to : function_slot)
      (closure : simple).

(* [Static_const.t]: what a symbol may be bound to. Its fields are
   [Simple]s, where the compiler has, for a boxed number, a constant or a
   variable. A block is immutable.

   [Static_const_closure_of_set] is the closure at [slot] of a static set
   of closures; [closure_symbols] are the symbols that the closures of the
   set are bound to ([Bound_static.Pattern.Set_of_closures]), this one
   included. *)
Inductive static_const : Type :=
  | Static_const_set_of_closures (code : code_id)
      (value_slots : list (value_slot * simple))
  | Static_const_closure_of_set (slot : function_slot)
      (closure_symbols : list (function_slot * symbol))
      (function_decls : list (function_slot * code_id))
      (value_slots : list (value_slot * simple))
  | Static_const_block (tag : Z) (fields : list simple)
  | Static_const_boxed_number (contents : simple)
  | Static_const_immutable_string (bytes : list Z).

(* Whether two simples, or two static constants, are the same. *)
Definition simple_eq_dec : forall s s' : simple, {s = s'} + {s <> s'}.
Proof.
  decide equality; try apply Pos.eq_dec.
  decide equality; try apply Z.eq_dec. repeat decide equality.
Defined.

Definition static_const_eq_dec :
  forall const const' : static_const, {const = const'} + {const <> const'}.
Proof.
  decide equality;
    try apply Pos.eq_dec; try apply Z.eq_dec; try apply simple_eq_dec;
    apply list_eq_dec; try apply Z.eq_dec; try apply simple_eq_dec;
    decide equality; try apply Pos.eq_dec; apply simple_eq_dec.
Defined.

(* [Apply_cont_expr.t]. *)
Record apply_cont : Type := Apply_cont_expr {
  ac_continuation : continuation;
  ac_args : list simple
}.

(* [Call_kind.Function_call.t]: the code called is known, or it is that of
   whatever closure the callee turns out to be. *)
Inductive call_kind : Type :=
  | Direct (code : code_id)
  | Indirect.

(* [Apply_expr.t]. *)
Record apply_expr : Type := Apply_expr {
  ap_callee : simple;
  ap_call_kind : call_kind;
  ap_args : list simple;
  ap_continuation : continuation;
  ap_exn_continuation : continuation
}.

(* [Flambda.expr], [Flambda.continuation_handler],
   [Flambda.static_const_or_code] with the name it is bound to, and
   [Function_params_and_body], the code of a function.

   The arms of a [Switch] are a [Target_ocaml_int.Map.t] in the compiler;
   here they are an association list, of which the first arm with a given
   discriminant counts.

   The body of code runs with the parameters and the closure called
   ([my_closure]) as its only variables, and the return and exception
   continuations as its only continuations. *)
Inductive expr : Type :=
  | Let (x : variable) (defining_expr : named) (body : expr)
  | Let_static (bindings : list static_binding) (body : expr)
  | Let_cont_non_recursive (k : continuation)
      (handler : continuation_handler) (body : expr)
  | Let_cont_recursive (handlers : list (continuation * continuation_handler))
      (body : expr)
  | Apply (ap : apply_expr)
  | Apply_cont (ac : apply_cont)
  | Switch (scrutinee : simple) (arms : list (Z * apply_cont))
  | Invalid
with continuation_handler : Type :=
  | Handler (params : list variable) (handler : expr)
with static_binding : Type :=
  | Bind_code (id : code_id) (c : code)
  | Bind_deleted_code (id : code_id)
  | Bind_symbol (s : symbol) (const : static_const)
with code : Type :=
  | Code (params : list variable) (my_closure : variable)
      (return_continuation exn_continuation : continuation) (body : expr).

Definition code_params (c : code) : list variable :=
  match c with Code params _ _ _ _ => params end.

Definition code_my_closure (c : code) : variable :=
  match c with Code _ my_closure _ _ _ => my_closure end.

Definition code_return_continuation (c : code) : continuation :=
  match c with Code _ _ return_continuation _ _ => return_continuation end.

Definition code_exn_continuation (c : code) : continuation :=
  match c with Code _ _ _ exn_continuation _ => exn_continuation end.

Definition code_body (c : code) : expr :=
  match c with Code _ _ _ _ body => body end.

(* ======================================================================== *)
(* Sets of closures of several functions                                    *)
(* ======================================================================== *)

(* Each variable bound to the projection of its function slot from the
   closure [base], which is at [base_slot]. *)
Fixpoint let_projections (base : variable) (base_slot : function_slot)
    (bound : list (variable * function_slot)) (body : expr) : expr :=
  match bound with
  | [] => body
  | (x, slot) :: bound =>
    Let x (Project_function_slot base_slot slot (Var base))
      (let_projections base base_slot bound body)
  end.

(* The compiler's [Let] of a set of closures: the variables [bound_vars]
   ([Bound_pattern.Set_of_closures]) are bound, in the order of the
   functions of the set, to its closures. The first closure is made and
   the others are projected from it. There must be as many variables as
   functions, and at least one; otherwise there is no such term. *)
Definition let_closures (bound_vars : list variable)
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) (body : expr)
    : option expr :=
  match bound_vars, function_decls with
  | x :: bound_vars, (slot, _) :: other_decls =>
    if Nat.eqb (length bound_vars) (length other_decls)
    then
      Some
        (Let x (Closure_of_set slot function_decls value_slots)
           (let_projections x slot
              (combine bound_vars (map fst other_decls)) body))
    else None
  | _, _ => None
  end.

(* The static set of closures whose closures are bound to
   [closure_symbols], as the bindings of a [Let_static]: one for each
   symbol. *)
Definition bind_closures (closure_symbols : list (function_slot * symbol))
    (function_decls : list (function_slot * code_id))
    (value_slots : list (value_slot * simple)) : list static_binding :=
  map
    (fun '(slot, s) =>
       Bind_symbol s
         (Static_const_closure_of_set slot closure_symbols function_decls
            value_slots))
    closure_symbols.
