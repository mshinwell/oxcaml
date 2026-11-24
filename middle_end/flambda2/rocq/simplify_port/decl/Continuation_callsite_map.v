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
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Continuation.

(* continuation_callsite_map.mli:18  type 'a t = 'a Apply_cont_rewrite_id.Map.t Continuation.Map.t *)
Definition t (A : Type) : Type := Continuation.Map.t (Apply_cont_rewrite_id.Map.t A).
Extract Constant t "'a1" => "('a1) Continuation_callsite_map.t".
(* continuation_callsite_map.mli:28  val find : Continuation.t -> Apply_cont_rewrite_id.t -> 'a t -> 'a *)
Parameter find : forall {A : Type}, Continuation.t -> Apply_cont_rewrite_id.t -> t A -> M A.
Extract Inlined Constant find => "Continuation_callsite_map.find".
