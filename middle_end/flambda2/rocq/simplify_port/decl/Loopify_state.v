(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                     Nathanaëlle Courant, OCamlPro                      *)
(*                                                                        *)
(*   Copyright 2022 OCamlPro SAS                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Loopify_state], after its interface
   middle_end/flambda2/simplify/loopify_state.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Format.

(* loopify_state.mli:15  type t = private | Do_not_loopify | Loopify of Continuation.t *)
Inductive t : Type :=
| Do_not_loopify : t
| Loopify : Continuation.t -> t.
Extract Inductive t => "Loopify_state.t" [ "Loopify_state.Do_not_loopify" "Loopify_state.Loopify" ].
(* loopify_state.mli:19  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Loopify_state.print".
(* loopify_state.mli:21  val do_not_loopify : t *)
Parameter do_not_loopify : t.
Extract Inlined Constant do_not_loopify => "Loopify_state.do_not_loopify".
(* loopify_state.mli:23  val loopify : Continuation.t -> t *)
Parameter loopify : Continuation.t -> M t.
Extract Inlined Constant loopify => "Loopify_state.loopify".
