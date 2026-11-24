(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Trap_action], after its interface
   middle_end/flambda2/terms/trap_action.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation.

Module Raise_kind.
  (* trap_action.mli:26  type t = | Regular | Reraise | No_trace *)
  Inductive t : Type :=
  | Regular : t
  | Reraise : t
  | No_trace : t.
  Extract Inductive t => "Trap_action.Raise_kind.t" [ "Trap_action.Raise_kind.Regular" "Trap_action.Raise_kind.Reraise" "Trap_action.Raise_kind.No_trace" ].
End Raise_kind.
(* trap_action.mli:37  type t = | Push of { exn_handler : Continuation.t } | Pop of { exn_handler : Continuation.t; ( ** Note that even for [Pop], [exn_handler] might not match the target continuation in the enclosing [Apply_cont_expr]. One example is when a value is being returned from the end of the non-exceptional block of a try...with. * ) raise_kind : Raise_kind.t option } *)
Inductive t : Type :=
| Push : Continuation.t -> t
| Pop : Continuation.t -> option Trap_action.Raise_kind.t -> t.
Extract Inductive t => "Trap_action.t" [ "(fun x__1 -> (Trap_action.Push { exn_handler = x__1 } : Trap_action.t))" "(fun (x__1, x__2) -> (Trap_action.Pop { exn_handler = x__1; raise_kind = x__2 } : Trap_action.t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Trap_action.t) with Trap_action.Push { exn_handler = x__1 } -> f__1 x__1 | Trap_action.Pop { exn_handler = x__1; raise_kind = x__2 } -> f__2 x__1 x__2)".
