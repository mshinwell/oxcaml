(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2005 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Clflags], after its interface
   utils/clflags.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* clflags.mli:223  val target_is_jsir : unit -> bool *)
Parameter target_is_jsir : unit -> M bool.
Extract Inlined Constant target_is_jsir => "Clflags.target_is_jsir".
Module Register_allocator.
  (* clflags.mli:403  type t = | Cfg | Irc | Ls | Gi *)
  Parameter t : Type.
  Extract Inlined Constant t => "Clflags.Register_allocator.t".
End Register_allocator.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Clflags. End Clflags.
