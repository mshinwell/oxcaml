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
   Simplify uses of the standard library's module [Printexc]. Its names and
   types are read from the compiled interface of that module in the
   standard library of the OCaml that built the compiler, not from this
   tree's stdlib/ (PROVENANCE.md, last section): the compiled interface
   that the files of the build import by the MD5 digest
   e58645338ce0e91a971f2806d56d691b. The header above is that of this
   tree's file of the same name,
   stdlib/printexc.mli
   (Git blob d0eb692bd05629139d4a8edda2b8d6360bacdc80). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/printexc.mli  type raw_backtrace *)
Parameter raw_backtrace : Type.
Extract Inlined Constant raw_backtrace => "Printexc.raw_backtrace".
(* stdlib/printexc.mli  val get_raw_backtrace : unit -> Stdlib__Printexc.raw_backtrace *)
Parameter get_raw_backtrace : unit -> M raw_backtrace.
Extract Inlined Constant get_raw_backtrace => "Printexc.get_raw_backtrace".
(* stdlib/printexc.mli  val raise_with_backtrace : exn -> Stdlib__Printexc.raw_backtrace -> 'a *)
Parameter raise_with_backtrace : forall {A : Type}, exn -> raw_backtrace -> M A.
Extract Inlined Constant raise_with_backtrace => "Printexc.raise_with_backtrace".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Printexc. End Printexc.
