(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Guillaume Bury and Nathanaëlle Courant, OCamlPro                    *)
(*                                                                        *)
(*   Copyright 2024--2024 OCamlPro SAS                                    *)
(*   Copyright 2024--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Continuation_callsite_map], after its interface
   middle_end/flambda2/identifiers/continuation_callsite_map.mli
   (Git blob ef2fd16377e0ad02e701f4938bbf9d96d9a09021). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Continuation Format.

(* continuation_callsite_map.mli:18  type 'a t = 'a Apply_cont_rewrite_id.Map.t Continuation.Map.t *)
Definition t (A : Type) : Type := Continuation.Map.t (Apply_cont_rewrite_id.Map.t A).
Extract Constant t "'a1" => "('a1) Continuation_callsite_map.t".
(* continuation_callsite_map.mli:21  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
Extract Inlined Constant print => "Continuation_callsite_map.print".
(* continuation_callsite_map.mli:28  val find : Continuation.t -> Apply_cont_rewrite_id.t -> 'a t -> 'a *)
Parameter find : forall {A : Type}, Continuation.t -> Apply_cont_rewrite_id.t -> t A -> M A.
Extract Inlined Constant find => "Continuation_callsite_map.find".
(* continuation_callsite_map.mli:32  val add : Continuation.t -> Apply_cont_rewrite_id.t -> 'a -> 'a t -> 'a t *)
Parameter add : forall {A : Type}, Continuation.t -> Apply_cont_rewrite_id.t -> A -> t A -> M (t A).
Extract Inlined Constant add => "Continuation_callsite_map.add".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Continuation_callsite_map. End Continuation_callsite_map.
