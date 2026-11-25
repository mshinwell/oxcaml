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
   Simplify uses of the standard library's module [Queue]. Its names and
   types are read from the compiled interface of that module in the
   standard library of the OCaml that built the compiler, not from this
   tree's stdlib/ (PROVENANCE.md, last section): the compiled interface
   that the files of the build import by the MD5 digest
   3b321c1bad5b935cfbf4767b238e4180. The header above is that of this
   tree's file of the same name,
   stdlib/queue.mli
   (Git blob 636456d520c9ff8e11e2ce8a579de3e075f64010). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/queue.mli  type t *)
Parameter t : Type -> Type.
Extract Constant t "'a1" => "('a1) Queue.t".
(* _none_  exception Empty *)
Parameter Empty : exception unit.
Extract Inlined Constant Empty => "((fun () -> Queue.Empty), (function Queue.Empty -> Some () | _ -> None))".
(* stdlib/queue.mli  val create : unit -> 'a Stdlib__Queue.t *)
Parameter create : forall {A : Type}, unit -> M (t A).
Extract Inlined Constant create => "Queue.create".
(* stdlib/queue.mli  val add : 'a -> 'a Stdlib__Queue.t -> unit *)
Parameter add : forall {A : Type}, A -> t A -> M unit.
Extract Inlined Constant add => "Queue.add".
(* stdlib/queue.mli  val push : 'a -> 'a Stdlib__Queue.t -> unit *)
Parameter push : forall {A : Type}, A -> t A -> M unit.
Extract Inlined Constant push => "Queue.push".
(* stdlib/queue.mli  val take : 'a Stdlib__Queue.t -> 'a *)
Parameter take : forall {A : Type}, t A -> M A.
Extract Inlined Constant take => "Queue.take".
(* stdlib/queue.mli  val pop : 'a Stdlib__Queue.t -> 'a *)
Parameter pop : forall {A : Type}, t A -> M A.
Extract Inlined Constant pop => "Queue.pop".
(* stdlib/queue.mli  val is_empty : 'a Stdlib__Queue.t -> bool *)
Parameter is_empty : forall {A : Type}, t A -> M bool.
Extract Inlined Constant is_empty => "Queue.is_empty".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Queue. End Queue.
