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

(* The abbreviations of modules that
   middle_end/flambda2/simplify/simplified_expr.ml
   makes itself, for Simplified_expr.v (GUIDE.md, section 7, ABBREVIATIONS OF
   MODULES). The OCaml text at the head of that file has the same lines,
   [module A = P]. Every such library has the name Port_abbreviations: Rocq
   writes [open Port_abbreviations] in an extracted file that needs it, and
   runtime/port_abbreviations.ml is that (empty) module. This file follows
   no other file of the compiler. *)

From SimplifyPort.decl Require Common_subexpression_elimination
  Continuation_extra_params_and_args Flambda2_types Lifted_constant_state.

Module CSE := Common_subexpression_elimination.
Module EPA := Continuation_extra_params_and_args.
Module T := Flambda2_types.
Module TE := T.Typing_env.
Module LCS := Lifted_constant_state.
