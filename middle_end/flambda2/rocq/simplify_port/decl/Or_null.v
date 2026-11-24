(******************************************************************************
 *                                  OxCaml                                    *
 *                       Basile Clément, OCamlPro                             *
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
   Simplify uses of the compiler's module [Or_null], after its interface
   middle_end/flambda2/algorithms/or_null.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* or_null.mli:29  type 'a t = | Null | This of 'a [@@or_null] *)
Inductive t (A : Type) : Type :=
| Null : t A
| This : A -> t A.
Arguments Null {A}.
Arguments This {A}.
Extract Inductive t => "Or_null.t" [ "Or_null.Null" "Or_null.This" ].
(* or_null.mli:38  val null : 'a t *)
Parameter null : forall {A : Type}, t A.
Extract Inlined Constant null => "Or_null.null".
(* or_null.mli:40  val this : 'a -> 'a t *)
Parameter this : forall {A : Type}, A -> M (t A).
Extract Inlined Constant this => "Or_null.this".
(* or_null.mli:48  val of_option : 'a option -> 'a t *)
Parameter of_option : forall {A : Type}, option A -> M (t A).
Extract Inlined Constant of_option => "Or_null.of_option".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Or_null. End Or_null.
