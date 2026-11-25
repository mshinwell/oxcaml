(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the standard library's module [String]. Its names and
   types are read from the compiled interface of that module in the
   standard library of the OCaml that built the compiler, not from this
   tree's stdlib/ (PROVENANCE.md, last section). The header above is that
   of this tree's file of the same name,
   stdlib/string.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Stdlib_.

(* stdlib/string.mli  type t *)
Definition t : Type := string.
Extract Inlined Constant t => "String.t".
(* stdlib/string.mli  val length : string -> int *)
Parameter length : string -> M int.
Extract Inlined Constant length => "String.length".
(* stdlib/string.mli  val equal : Stdlib__String.t -> Stdlib__String.t -> bool *)
Parameter equal : t -> t -> M bool.
Extract Inlined Constant equal => "String.equal".
(* stdlib/string.mli  val map : (char -> char) -> string -> string *)
Parameter map : (Stdlib_.char -> M Stdlib_.char) -> string -> M string.
Extract Inlined Constant map => "String.map".
(* stdlib/string.mli  val hash : Stdlib__String.t -> int *)
Parameter hash : t -> M int.
Extract Inlined Constant hash => "String.hash".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module String. End String.
