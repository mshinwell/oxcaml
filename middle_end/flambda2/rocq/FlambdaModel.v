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

   What is left out, and is to be added in later steps:
   - [Apply] (function calls), and with it code, closures and sets of
     closures;
   - the other bound patterns of [Let] ([Set_of_closures], [Static]) and the
     other forms of [named] ([Set_of_closures], [Static_consts], [Rec_info]);
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
     which laws can be stated without defining it. *)

From Stdlib Require Import ZArith List.
Import ListNotations.

(* [Variable.t] and [Continuation.t]. *)
Definition variable : Type := positive.
Definition continuation : Type := positive.

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

(* [Flambda.named]. *)
Inductive named : Type :=
  | Simple (s : simple)
  | Prim (p : prim) (args : list simple).

(* [Apply_cont_expr.t]. *)
Record apply_cont : Type := Apply_cont_expr {
  ac_continuation : continuation;
  ac_args : list simple
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
  | Apply_cont (ac : apply_cont)
  | Switch (scrutinee : simple) (arms : list (Z * apply_cont))
  | Invalid
with continuation_handler : Type :=
  | Handler (params : list variable) (handler : expr).
