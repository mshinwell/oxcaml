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
   Simplify uses of the compiler's module [Array], after its interface
   stdlib/array.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/array.mli  val length : 'a array -> int *)
Parameter length : forall {A : Type}, array A -> M int.
Extract Inlined Constant length => "Array.length".
(* stdlib/array.mli  val get : 'a array -> int -> 'a *)
Parameter get : forall {A : Type}, array A -> int -> M A.
Extract Inlined Constant get => "Array.get".
(* stdlib/array.mli  val to_list : 'a array -> 'a list *)
Parameter to_list : forall {A : Type}, array A -> M (list A).
Extract Inlined Constant to_list => "Array.to_list".
(* stdlib/array.mli  val of_list : 'a list -> 'a array *)
Parameter of_list : forall {A : Type}, list A -> M (array A).
Extract Inlined Constant of_list => "Array.of_list".
(* stdlib/array.mli  val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a array -> 'acc *)
Parameter fold_left : forall {Acc A : Type}, (Acc -> A -> M Acc) -> Acc -> array A -> M Acc.
Extract Inlined Constant fold_left => "Array.fold_left".
(* stdlib/array.mli  val fold_right : ('a -> 'acc -> 'acc) -> 'a array -> 'acc -> 'acc *)
Parameter fold_right : forall {A Acc : Type}, (A -> Acc -> M Acc) -> array A -> Acc -> M Acc.
Extract Inlined Constant fold_right => "Array.fold_right".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Array. End Array.
