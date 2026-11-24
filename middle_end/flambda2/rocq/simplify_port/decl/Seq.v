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
   Simplify uses of the compiler's module [Seq], after its interface
   stdlib/seq.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

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
