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
   Simplify uses of the compiler's module [List], after its interface
   stdlib/list.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/list.mli  val compare_lengths : 'a list -> 'b list -> int *)
Parameter compare_lengths : forall {A B : Type}, list A -> list B -> M int.
Extract Inlined Constant compare_lengths => "List.compare_lengths".
(* stdlib/list.mli  val for_all : ('a -> bool) -> 'a list -> bool *)
Parameter for_all : forall {A : Type}, (A -> M bool) -> list A -> M bool.
Extract Inlined Constant for_all => "List.for_all".
