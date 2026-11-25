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
   Simplify uses of the compiler's module [Location], after its interface
   parsing/location.mli
   (Git blob cda2e43b0a7a00e82c46080bc967f6b2aae8cc00). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Warnings.

(* location.mli:42  type t = Warnings.loc = { loc_start: Lexing.position; loc_end: Lexing.position; loc_ghost: bool; } *)
Definition t : Type := Warnings.loc.
Extract Inlined Constant t => "Location.t".
(* location.mli:353  val prerr_warning: t -> Warnings.t -> unit *)
Parameter prerr_warning : t -> Warnings.t -> M unit.
Extract Inlined Constant prerr_warning => "Location.prerr_warning".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Location. End Location.
