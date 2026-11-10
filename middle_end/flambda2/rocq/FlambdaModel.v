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
   - the kinds ([Flambda_kind.t]) and the constants ([Reg_width_const.t]),
     in full but for the string of [Poison];
   - [Let] of one variable, bound to a [Simple], a primitive application, a
     closure or the projection of a value slot;
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
   - sets of closures of several functions, with [Project_function_slot],
     the bound pattern of [Let] for them, and static sets of closures
     binding several symbols;
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
     [Flambda_primitive.t] holds the arguments by arity. The primitives
     themselves are abstract ([prim]): this fragment is parametric in them,
     and FlambdaSemanticsSpec.v gives them an abstract evaluation, about
     which laws can be stated without defining it.
   - [Project_value_slot], a unary primitive in the compiler, is a form of
     [named] of its own, as its meaning is fixed by that of closures.
   - The callee of an [Apply] is always given, where the compiler may omit
     it for a direct call.
   - The numbers in constants are integers: those of the floats and
     vectors are bit patterns, as in the compiler, and none is yet
     restricted to its range. *)

From Stdlib Require Import ZArith List.
Import ListNotations.

(* [Variable.t], [Continuation.t], [Symbol.t], [Code_id.t] and
   [Value_slot.t]. *)
Definition variable : Type := positive.
Definition continuation : Type := positive.
Definition symbol : Type := positive.
Definition code_id : Type := positive.
Definition value_slot : Type := positive.

(* ======================================================================== *)
(* Kinds and constants                                                      *)
(* ======================================================================== *)

(* [Flambda_kind.Naked_number_kind.t]. The constructors are prefixed, as
   the constants have the compiler's names. *)
Inductive naked_number_kind : Type :=
  | Kind_naked_immediate
  | Kind_naked_float32
  | Kind_naked_float
  | Kind_naked_int8
  | Kind_naked_int16
  | Kind_naked_int32
  | Kind_naked_int64
  | Kind_naked_nativeint
  | Kind_naked_vec128
  | Kind_naked_vec256
  | Kind_naked_vec512
  | Kind_naked_mask.

(* [Flambda_kind.t]. *)
Inductive flambda_kind : Type :=
  | Value
  | Naked_number (k : naked_number_kind)
  | Region
  | Rec_info.

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

(* [Flambda_primitive.t] without its arguments. *)
Parameter prim : Type.

(* [Flambda.named]. A [Set_of_closures] has one function, given by its
   code, and the values of its value slots. *)
Inductive named : Type :=
  | Simple (s : simple)
  | Prim (p : prim) (args : list simple)
  | Set_of_closures (code : code_id)
      (value_slots : list (value_slot * simple))
  | Project_value_slot (slot : value_slot) (closure : simple).

(* [Static_const.t]: what a symbol may be bound to. Its fields are
   [Simple]s, where the compiler has, for a boxed number, a constant or a
   variable. A block is immutable. *)
Inductive static_const : Type :=
  | Static_const_set_of_closures (code : code_id)
      (value_slots : list (value_slot * simple))
  | Static_const_block (tag : Z) (fields : list simple)
  | Static_const_boxed_number (contents : simple)
  | Static_const_immutable_string (bytes : list Z).

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

   The arms of a [Switch] are a [Targetint_31_63.Map.t] in the compiler;
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
