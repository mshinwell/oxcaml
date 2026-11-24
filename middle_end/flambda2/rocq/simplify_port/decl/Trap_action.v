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
End Raise_kind.
(* trap_action.mli:37  type t = | Push of { exn_handler : Continuation.t } | Pop of { exn_handler : Continuation.t; ( ** Note that even for [Pop], [exn_handler] might not match the target continuation in the enclosing [Apply_cont_expr]. One example is when a value is being returned from the end of the non-exceptional block of a try...with. * ) raise_kind : Raise_kind.t option } *)
Record push_payload_ : Type := { exn_handler : Continuation.t }.
(* The inline record of [Pop]: abstract (a name of its fields is taken, or it holds the type); [mk_Pop] makes one, [match_t] reads it. *)
Parameter pop_payload_ : Type.
Inductive t : Type :=
| Push : push_payload_ -> t
| Pop : pop_payload_ -> t.
Parameter mk_Push : Continuation.t -> t.
Extract Inlined Constant mk_Push => "(fun x__1 -> Trap_action.Push { exn_handler = x__1 })".
Parameter mk_Pop : Continuation.t -> option Trap_action.Raise_kind.t -> t.
Extract Inlined Constant mk_Pop => "(fun x__1 x__2 -> Trap_action.Pop { exn_handler = x__1; raise_kind = x__2 })".
Parameter match_t : forall {Res : Type}, t -> (Continuation.t -> M Res) -> (Continuation.t -> option Trap_action.Raise_kind.t -> M Res) -> M Res.
Extract Inlined Constant match_t => "(fun x__0 f__1 f__2 -> match x__0 with Trap_action.Push { exn_handler = x__1 } -> f__1 x__1 | Trap_action.Pop { exn_handler = x__1; raise_kind = x__2 } -> f__2 x__1 x__2)".
