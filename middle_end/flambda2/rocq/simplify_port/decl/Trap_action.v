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

(* trap_action.mli:37  type t = | Push of { exn_handler : Continuation.t } | Pop of { exn_handler : Continuation.t; ( ** Note that even for [Pop], [exn_handler] might not match the target continuation in the enclosing [Apply_cont_expr]. One example is when a value is being returned from the end of the non-exceptional block of a try...with. * ) raise_kind : Raise_kind.t option } *)
Parameter t : Type.
Extract Inlined Constant t => "Trap_action.t".
