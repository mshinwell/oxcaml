(******************************************************************************
 *                                  OxCaml                                    *
 *                        Basile Clément, OCamlPro                            *
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
   Simplify uses of the compiler's module [Switch_arm], after its interface
   middle_end/flambda2/terms/switch_arm.mli
   (Git blob cc6ecf7a0e73f870ea4ab9f39121017e50a13896). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_expr Branch_annotations.

(* switch_arm.mli:29  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Switch_arm.t".
(* switch_arm.mli:35  val create : annotations:Branch_annotations.t -> Apply_cont_expr.t -> t *)
Parameter create : Branch_annotations.t -> Apply_cont_expr.t -> M t.
Extract Inlined Constant create => "Switch_arm.create".
(* switch_arm.mli:39  val annotations : t -> Branch_annotations.t *)
Parameter annotations : t -> M Branch_annotations.t.
Extract Inlined Constant annotations => "Switch_arm.annotations".
(* switch_arm.mli:41  val action : t -> Apply_cont_expr.t *)
Parameter action : t -> M Apply_cont_expr.t.
Extract Inlined Constant action => "Switch_arm.action".
(* switch_arm.mli:47  val is_cold : t -> bool *)
Parameter is_cold : t -> M bool.
Extract Inlined Constant is_cold => "Switch_arm.is_cold".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Switch_arm. End Switch_arm.
