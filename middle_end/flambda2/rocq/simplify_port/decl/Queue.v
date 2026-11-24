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
   Simplify uses of the compiler's module [Queue], after its interface
   stdlib/queue.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

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
