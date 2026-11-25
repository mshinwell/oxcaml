(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Gallium, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2006 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Debuginfo], after its interface
   lambda/debuginfo.mli
   (Git blob 8ef7a47eb80f4e1eb1ea266256f1a01d023deea9). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Location.

(* debuginfo.mli:97  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Debuginfo.t".
(* debuginfo.mli:99  val none : t *)
Parameter none : t.
Extract Inlined Constant none => "Debuginfo.none".
(* debuginfo.mli:113  val to_location : t -> Location.t *)
Parameter to_location : t -> M Location.t.
Extract Inlined Constant to_location => "Debuginfo.to_location".
(* debuginfo.mli:132  val print_compact : Format.formatter -> t -> unit *)
Parameter print_compact : Format.formatter -> t -> M unit.
Extract Inlined Constant print_compact => "Debuginfo.print_compact".
(* debuginfo.mli:140  val merge : into:t -> t -> t *)
Parameter merge : t -> t -> M t.
Extract Inlined Constant merge => "Debuginfo.merge".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Debuginfo. End Debuginfo.
