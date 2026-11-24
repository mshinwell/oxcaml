(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                         The OCaml programmers                          *)
(*                                                                        *)
(*   Copyright 2018 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Option], after its interface
   stdlib/option.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/option.mli  val value : 'a option -> default:'a -> 'a *)
Parameter value : forall {A : Type}, option A -> A -> M A.
Extract Inlined Constant value => "Option.value".
(* stdlib/option.mli  val get : 'a option -> 'a *)
Parameter get : forall {A : Type}, option A -> M A.
Extract Inlined Constant get => "Option.get".
(* stdlib/option.mli  val bind : 'a option -> ('a -> 'b option) -> 'b option *)
Parameter bind : forall {A B : Type}, option A -> (A -> M (option B)) -> M (option B).
Extract Inlined Constant bind => "Option.bind".
(* stdlib/option.mli  val map : ('a -> 'b) -> 'a option -> 'b option *)
Parameter map : forall {A B : Type}, (A -> M B) -> option A -> M (option B).
Extract Inlined Constant map => "Option.map".
(* stdlib/option.mli  val is_none : 'a option -> bool *)
Parameter is_none : forall {A : Type}, option A -> M bool.
Extract Inlined Constant is_none => "Option.is_none".
(* stdlib/option.mli  val is_some : 'a option -> bool *)
Parameter is_some : forall {A : Type}, option A -> M bool.
Extract Inlined Constant is_some => "Option.is_some".
(* stdlib/option.mli  val equal : ('a -> 'a -> bool) -> 'a option -> 'a option -> bool *)
Parameter equal : forall {A : Type}, (A -> A -> M bool) -> option A -> option A -> M bool.
Extract Inlined Constant equal => "Option.equal".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Option. End Option.
