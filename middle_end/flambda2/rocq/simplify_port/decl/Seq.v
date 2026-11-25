(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                 Simon Cruanes                                          *)
(*                                                                        *)
(*   Copyright 2017 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the standard library's module [Seq]. Its names and
   types are read from the compiled interface of that module in the
   standard library of the OCaml that built the compiler, not from this
   tree's stdlib/ (PROVENANCE.md, last section): the compiled interface
   that the files of the build import by the MD5 digest
   1d1c31e02b77070ff0e51eaaab2af0cc. The header above is that of this
   tree's file of the same name,
   stdlib/seq.mli
   (Git blob 26e1b2b3513a3708df72cc41ac74b9a5bab03e62). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/seq.mli  type node *)
Parameter node : Type -> Type.
Extract Constant node "'a1" => "('a1) Seq.node".
(* stdlib/seq.mli  type t *)
Definition t (A : Type) : Type := unit -> M (node A).
Extract Constant t "'a1" => "('a1) Seq.t".
(* stdlib/seq.mli  val exists2 : ('a -> 'b -> bool) -> 'a Stdlib__Seq.t -> 'b Stdlib__Seq.t -> bool *)
Parameter exists2_ : forall {A B : Type}, (A -> B -> M bool) -> t A -> t B -> M bool.
Extract Inlined Constant exists2_ => "Seq.exists2".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Seq. End Seq.
