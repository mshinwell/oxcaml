(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                         The OCaml programmers                          *)
(*                                                                        *)
(*   Copyright 2018 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Int], after its interface
   stdlib/int.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/int.mli  val neg : int -> int *)
Parameter neg : int -> M int.
Extract Inlined Constant neg => "Int.neg".
(* stdlib/int.mli  val add : int -> int -> int *)
Parameter add : int -> int -> M int.
Extract Inlined Constant add => "Int.add".
(* stdlib/int.mli  val sub : int -> int -> int *)
Parameter sub : int -> int -> M int.
Extract Inlined Constant sub => "Int.sub".
(* stdlib/int.mli  val mul : int -> int -> int *)
Parameter mul : int -> int -> M int.
Extract Inlined Constant mul => "Int.mul".
(* stdlib/int.mli  val div : int -> int -> int *)
Parameter div : int -> int -> M int.
Extract Inlined Constant div => "Int.div".
(* stdlib/int.mli  val rem : int -> int -> int *)
Parameter rem : int -> int -> M int.
Extract Inlined Constant rem => "Int.rem".
(* stdlib/int.mli  val logand : int -> int -> int *)
Parameter logand : int -> int -> M int.
Extract Inlined Constant logand => "Int.logand".
(* stdlib/int.mli  val logor : int -> int -> int *)
Parameter logor : int -> int -> M int.
Extract Inlined Constant logor => "Int.logor".
(* stdlib/int.mli  val logxor : int -> int -> int *)
Parameter logxor : int -> int -> M int.
Extract Inlined Constant logxor => "Int.logxor".
(* stdlib/int.mli  val lognot : int -> int *)
Parameter lognot : int -> M int.
Extract Inlined Constant lognot => "Int.lognot".
(* stdlib/int.mli  val shift_left : int -> int -> int *)
Parameter shift_left : int -> int -> M int.
Extract Inlined Constant shift_left => "Int.shift_left".
(* stdlib/int.mli  val shift_right : int -> int -> int *)
Parameter shift_right : int -> int -> M int.
Extract Inlined Constant shift_right => "Int.shift_right".
(* stdlib/int.mli  val shift_right_logical : int -> int -> int *)
Parameter shift_right_logical : int -> int -> M int.
Extract Inlined Constant shift_right_logical => "Int.shift_right_logical".
(* stdlib/int.mli  val compare : int -> int -> int *)
Parameter compare : int -> int -> M int.
Extract Inlined Constant compare => "Int.compare".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Int. End Int.
