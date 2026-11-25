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
   Simplify uses of the standard library's module [ListLabels]. Its names and
   types are read from the compiled interface of that module in the
   standard library of the OCaml that built the compiler, not from this
   tree's stdlib/ (PROVENANCE.md, last section). The header above is that
   of this tree's file of the same name,
   stdlib/listLabels.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/listLabels.mli  val map : f:('a -> 'b) -> 'a list -> 'b list *)
Parameter map : forall {A B : Type}, (A -> M B) -> list A -> M (list B).
Extract Inlined Constant map => "ListLabels.map".
(* stdlib/listLabels.mli  val filter_map : f:('a -> 'b option) -> 'a list -> 'b list *)
Parameter filter_map : forall {A B : Type}, (A -> M (option B)) -> list A -> M (list B).
Extract Inlined Constant filter_map => "ListLabels.filter_map".
(* stdlib/listLabels.mli  val fold_left : f:('acc -> 'a -> 'acc) -> init:'acc -> 'a list -> 'acc *)
Parameter fold_left : forall {Acc A : Type}, (Acc -> A -> M Acc) -> Acc -> list A -> M Acc.
Extract Inlined Constant fold_left => "ListLabels.fold_left".
(* stdlib/listLabels.mli  val fold_right : f:('a -> 'acc -> 'acc) -> 'a list -> init:'acc -> 'acc *)
Parameter fold_right : forall {A Acc : Type}, (A -> Acc -> M Acc) -> list A -> Acc -> M Acc.
Extract Inlined Constant fold_right => "ListLabels.fold_right".
(* stdlib/listLabels.mli  val map2 : f:('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list *)
Parameter map2 : forall {A B C : Type}, (A -> B -> M C) -> list A -> list B -> M (list C).
Extract Inlined Constant map2 => "ListLabels.map2".
(* stdlib/listLabels.mli  val fold_left2 : f:('acc -> 'a -> 'b -> 'acc) -> init:'acc -> 'a list -> 'b list -> 'acc *)
Parameter fold_left2 : forall {Acc A B : Type}, (Acc -> A -> B -> M Acc) -> Acc -> list A -> list B -> M Acc.
Extract Inlined Constant fold_left2 => "ListLabels.fold_left2".
(* stdlib/listLabels.mli  val for_all : f:('a -> bool) -> 'a list -> bool *)
Parameter for_all : forall {A : Type}, (A -> M bool) -> list A -> M bool.
Extract Inlined Constant for_all => "ListLabels.for_all".
(* stdlib/listLabels.mli  val find_opt : f:('a -> bool) -> 'a list -> 'a option *)
Parameter find_opt : forall {A : Type}, (A -> M bool) -> list A -> M (option A).
Extract Inlined Constant find_opt => "ListLabels.find_opt".
(* stdlib/listLabels.mli  val sort : cmp:('a -> 'a -> int) -> 'a list -> 'a list *)
Parameter sort : forall {A : Type}, (A -> A -> M int) -> list A -> M (list A).
Extract Inlined Constant sort => "ListLabels.sort".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module ListLabels. End ListLabels.
