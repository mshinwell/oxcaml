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
   Simplify uses of the standard library's module [ArrayLabels]. Its names and
   types are read from the compiled interface of that module in the
   standard library of the OCaml that built the compiler, not from this
   tree's stdlib/ (PROVENANCE.md, last section): the compiled interface
   that the files of the build import by the MD5 digest
   b2e097604ac856997fec019f35f35004. The header above is that of this
   tree's file of the same name,
   stdlib/arrayLabels.mli
   (Git blob 8b10275dad3332ab75d30cdb128fbb959d2f42bc). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/arrayLabels.mli  val map : f:('a -> 'b) -> 'a array -> 'b array *)
Parameter map : forall {A B : Type}, (A -> M B) -> array A -> M (array B).
Extract Inlined Constant map => "ArrayLabels.map".
(* stdlib/arrayLabels.mli  val fold_left : f:('acc -> 'a -> 'acc) -> init:'acc -> 'a array -> 'acc *)
Parameter fold_left : forall {Acc A : Type}, (Acc -> A -> M Acc) -> Acc -> array A -> M Acc.
Extract Inlined Constant fold_left => "ArrayLabels.fold_left".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module ArrayLabels. End ArrayLabels.
