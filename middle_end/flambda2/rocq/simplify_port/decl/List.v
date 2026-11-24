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

(* stdlib/list.mli  val length : 'a list -> int *)
Parameter length : forall {A : Type}, list A -> M int.
Extract Inlined Constant length => "List.length".
(* stdlib/list.mli  val compare_lengths : 'a list -> 'b list -> int *)
Parameter compare_lengths : forall {A B : Type}, list A -> list B -> M int.
Extract Inlined Constant compare_lengths => "List.compare_lengths".
(* stdlib/list.mli  val compare_length_with : 'a list -> int -> int *)
Parameter compare_length_with : forall {A : Type}, list A -> int -> M int.
Extract Inlined Constant compare_length_with => "List.compare_length_with".
(* stdlib/list.mli  val hd : 'a list -> 'a *)
Parameter hd : forall {A : Type}, list A -> M A.
Extract Inlined Constant hd => "List.hd".
(* stdlib/list.mli  val tl : 'a list -> 'a list *)
Parameter tl : forall {A : Type}, list A -> M (list A).
Extract Inlined Constant tl => "List.tl".
(* stdlib/list.mli  val nth : 'a list -> int -> 'a *)
Parameter nth : forall {A : Type}, list A -> int -> M A.
Extract Inlined Constant nth => "List.nth".
(* stdlib/list.mli  val rev : 'a list -> 'a list *)
Parameter rev : forall {A : Type}, list A -> M (list A).
Extract Inlined Constant rev => "List.rev".
(* stdlib/list.mli  val init : int -> (int -> 'a) -> 'a list *)
Parameter init : forall {A : Type}, int -> (int -> M A) -> M (list A).
Extract Inlined Constant init => "List.init".
(* stdlib/list.mli  val rev_append : 'a list -> 'a list -> 'a list *)
Parameter rev_append : forall {A : Type}, list A -> list A -> M (list A).
Extract Inlined Constant rev_append => "List.rev_append".
(* stdlib/list.mli  val concat : 'a list list -> 'a list *)
Parameter concat : forall {A : Type}, list (list A) -> M (list A).
Extract Inlined Constant concat => "List.concat".
(* stdlib/list.mli  val iter : ('a -> unit) -> 'a list -> unit *)
Parameter iter : forall {A : Type}, (A -> M unit) -> list A -> M unit.
Extract Inlined Constant iter => "List.iter".
(* stdlib/list.mli  val map : ('a -> 'b) -> 'a list -> 'b list *)
Parameter map : forall {A B : Type}, (A -> M B) -> list A -> M (list B).
Extract Inlined Constant map => "List.map".
(* stdlib/list.mli  val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list *)
Parameter mapi : forall {A B : Type}, (int -> A -> M B) -> list A -> M (list B).
Extract Inlined Constant mapi => "List.mapi".
(* stdlib/list.mli  val filter_map : ('a -> 'b option) -> 'a list -> 'b list *)
Parameter filter_map : forall {A B : Type}, (A -> M (option B)) -> list A -> M (list B).
Extract Inlined Constant filter_map => "List.filter_map".
(* stdlib/list.mli  val concat_map : ('a -> 'b list) -> 'a list -> 'b list *)
Parameter concat_map : forall {A B : Type}, (A -> M (list B)) -> list A -> M (list B).
Extract Inlined Constant concat_map => "List.concat_map".
(* stdlib/list.mli  val fold_left_map : ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list *)
Parameter fold_left_map : forall {Acc A B : Type}, (Acc -> A -> M (Acc * B)) -> Acc -> list A -> M (Acc * list B).
Extract Inlined Constant fold_left_map => "List.fold_left_map".
(* stdlib/list.mli  val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc *)
Parameter fold_left : forall {Acc A : Type}, (Acc -> A -> M Acc) -> Acc -> list A -> M Acc.
Extract Inlined Constant fold_left => "List.fold_left".
(* stdlib/list.mli  val fold_right : ('a -> 'acc -> 'acc) -> 'a list -> 'acc -> 'acc *)
Parameter fold_right : forall {A Acc : Type}, (A -> Acc -> M Acc) -> list A -> Acc -> M Acc.
Extract Inlined Constant fold_right => "List.fold_right".
(* stdlib/list.mli  val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit *)
Parameter iter2 : forall {A B : Type}, (A -> B -> M unit) -> list A -> list B -> M unit.
Extract Inlined Constant iter2 => "List.iter2".
(* stdlib/list.mli  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list *)
Parameter map2 : forall {A B C : Type}, (A -> B -> M C) -> list A -> list B -> M (list C).
Extract Inlined Constant map2 => "List.map2".
(* stdlib/list.mli  val fold_left2 : ('acc -> 'a -> 'b -> 'acc) -> 'acc -> 'a list -> 'b list -> 'acc *)
Parameter fold_left2 : forall {Acc A B : Type}, (Acc -> A -> B -> M Acc) -> Acc -> list A -> list B -> M Acc.
Extract Inlined Constant fold_left2 => "List.fold_left2".
(* stdlib/list.mli  val for_all : ('a -> bool) -> 'a list -> bool *)
Parameter for_all : forall {A : Type}, (A -> M bool) -> list A -> M bool.
Extract Inlined Constant for_all => "List.for_all".
(* stdlib/list.mli  val exists : ('a -> bool) -> 'a list -> bool *)
Parameter exists_ : forall {A : Type}, (A -> M bool) -> list A -> M bool.
Extract Inlined Constant exists_ => "List.exists".
(* stdlib/list.mli  val exists2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool *)
Parameter exists2_ : forall {A B : Type}, (A -> B -> M bool) -> list A -> list B -> M bool.
Extract Inlined Constant exists2_ => "List.exists2".
(* stdlib/list.mli  val find_map : ('a -> 'b option) -> 'a list -> 'b option *)
Parameter find_map : forall {A B : Type}, (A -> M (option B)) -> list A -> M (option B).
Extract Inlined Constant find_map => "List.find_map".
(* stdlib/list.mli  val split : ('a * 'b) list -> 'a list * 'b list *)
Parameter split : forall {A B : Type}, list (A * B) -> M (list A * list B).
Extract Inlined Constant split => "List.split".
(* stdlib/list.mli  val combine : 'a list -> 'b list -> ('a * 'b) list *)
Parameter combine : forall {A B : Type}, list A -> list B -> M (list (A * B)).
Extract Inlined Constant combine => "List.combine".
(* stdlib/list.mli  val sort : ('a -> 'a -> int) -> 'a list -> 'a list *)
Parameter sort : forall {A : Type}, (A -> A -> M int) -> list A -> M (list A).
Extract Inlined Constant sort => "List.sort".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module List. End List.
