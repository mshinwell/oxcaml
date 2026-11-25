(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Damien Doligez, projet Para, INRIA Rocquencourt            *)
(*                                                                        *)
(*   Copyright 1997 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the standard library's module [Lazy]. Its names and
   types are read from the compiled interface of that module in the
   standard library of the OCaml that built the compiler, not from this
   tree's stdlib/ (PROVENANCE.md, last section): the compiled interface
   that the files of the build import by the MD5 digest
   d0b8d3be22a8b5bdfc9dda1877ae006f. The header above is that of this
   tree's file of the same name,
   stdlib/lazy.mli
   (Git blob 5dd59fe587fbc75894ae0dc5176b35cf6e56831c). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* Lazy.force: in the kit (Port_monad.v). *)

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Lazy. End Lazy.
