(******************************************************************************
 *                                  OxCaml                                    *
 *                       Mark Shinwell, Jane Street                           *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2024 Jane Street Group LLC                                   *
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

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Inlined_debuginfo], after its interface
   middle_end/flambda2/term_basics/inlined_debuginfo.mli
   (Git blob 21876a2d144f23879b3bcbf37c36bcaf75c59ed9). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Debuginfo Format.

(* inlined_debuginfo.mli:46  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Inlined_debuginfo.t".
(* inlined_debuginfo.mli:48  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Inlined_debuginfo.print".
(* inlined_debuginfo.mli:52  val none : t *)
Parameter none : t.
Extract Inlined Constant none => "Inlined_debuginfo.none".
(* inlined_debuginfo.mli:59  val create : called_code_id:Code_id.t -> apply_dbg:Debuginfo.t -> t *)
Parameter create : Code_id.t -> Debuginfo.t -> M t.
Extract Inlined Constant create => "Inlined_debuginfo.create".
(* inlined_debuginfo.mli:63  val merge : t -> from_apply_expr:t -> t *)
Parameter merge : t -> t -> M t.
Extract Inlined Constant merge => "Inlined_debuginfo.merge".
(* inlined_debuginfo.mli:173  val rewrite : t -> Debuginfo.t -> Debuginfo.t *)
Parameter rewrite : t -> Debuginfo.t -> M Debuginfo.t.
Extract Inlined Constant rewrite => "Inlined_debuginfo.rewrite".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Inlined_debuginfo. End Inlined_debuginfo.
