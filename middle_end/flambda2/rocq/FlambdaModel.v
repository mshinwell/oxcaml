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

(* The terms of Flambda 2 as the semantics sees them: a first fragment, the
   control flow.

   This file is to be reviewed, against middle_end/flambda2/terms/flambda.mli
   and the modules it refers to. It holds definitions only. The fragment has
   - [Let] of a [Simple] or of a primitive application to one variable;
   - [Let_cont], non-recursive and recursive;
   - [Apply_cont];
   - [Switch];
   - [Invalid].

   - [Apply] of a function, direct or indirect, with a return continuation
     and an exception continuation;
   - closures: a [Set_of_closures] of one function, and the projection of
     a value slot from a closure;
   - [code], the parameters and body of a function. Code is not bound in
     terms: the program's code is one fixed table, a parameter of the
     semantics (FlambdaSemanticsSpec.v).

   What is left out, and is to be added in later steps:
   - sets of closures of several functions, with [Project_function_slot],
     and the bound pattern of [Let] for them;
   - code bound by [Let] with the bound pattern [Static], and the other
     static constants; [Rec_info];
   - the other call kinds (methods, C calls, effects), [Never_returns],
     partial and over-application, and the modes, arities and inlining
     attributes of an [Apply];
   - trap actions on [Apply_cont], and the [is_exn_handler] and [is_cold]
     flags of continuation handlers;
   - kinds, debuginfo, and every annotation that has no effect on execution;
   - the constants other than immediates, and symbols as [Simple]s.

   Differences of presentation from the compiler:
   - Variables and continuations are plain names. The compiler works up to
     alpha-equivalence ([Name_abstraction]); here a binder shadows, and the
     semantics (FlambdaSemanticsSpec.v) uses environments and closures, so
     no substitution and no freshness condition is needed to define
     execution.
   - The two forms of [Let_cont] are two constructors of [expr].
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
     it for a direct call. *)

From Stdlib Require Import ZArith List.
Import ListNotations.

(* [Variable.t], [Continuation.t], [Code_id.t] and [Value_slot.t]. *)
Definition variable : Type := positive.
Definition continuation : Type := positive.
Definition code_id : Type := positive.
Definition value_slot : Type := positive.

(* [Reg_width_const.t], the immediates only. The integers are not yet
   restricted to the range of [Target_ocaml_int.t]. *)
Inductive const : Type :=
  | Naked_immediate (i : Z)
  | Tagged_immediate (i : Z).

(* [Simple.t], without symbols and coercions. *)
Inductive simple : Type :=
  | Var (x : variable)
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

(* [Flambda.expr] and [Flambda.continuation_handler]. The arms of a [Switch]
   are a [Targetint_31_63.Map.t] in the compiler; here they are an association
   list, of which the first arm with a given discriminant counts. *)
Inductive expr : Type :=
  | Let (x : variable) (defining_expr : named) (body : expr)
  | Let_cont_non_recursive (k : continuation)
      (handler : continuation_handler) (body : expr)
  | Let_cont_recursive (handlers : list (continuation * continuation_handler))
      (body : expr)
  | Apply (ap : apply_expr)
  | Apply_cont (ac : apply_cont)
  | Switch (scrutinee : simple) (arms : list (Z * apply_cont))
  | Invalid
with continuation_handler : Type :=
  | Handler (params : list variable) (handler : expr).

(* [Function_params_and_body]: the code of a function. Its body runs with
   the parameters and the closure called ([my_closure]) as its only
   variables, and the return and exception continuations as its only
   continuations. *)
Record code : Type := Code {
  code_params : list variable;
  code_my_closure : variable;
  code_return_continuation : continuation;
  code_exn_continuation : continuation;
  code_body : expr
}.
