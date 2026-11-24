(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2019 OCamlPro SAS                                          *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Name_occurrences], after its interface
   middle_end/flambda2/nominal/name_occurrences.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation.

(* name_occurrences.mli:26  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Name_occurrences.t".
(* name_occurrences.mli:28  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Name_occurrences.empty".
(* name_occurrences.mli:194  val fold_continuations_including_in_trap_actions : t -> init:'a -> f:('a -> Continuation.t -> 'a) -> 'a *)
Parameter fold_continuations_including_in_trap_actions : forall {A : Type}, t -> A -> (A -> Continuation.t -> M A) -> M A.
Extract Inlined Constant fold_continuations_including_in_trap_actions => "Name_occurrences.fold_continuations_including_in_trap_actions".
