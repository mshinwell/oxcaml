(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Basile Clément, OCamlPro                         *)
(*                                                                        *)
(*   Copyright 2013--2025 OCamlPro SAS                                    *)
(*   Copyright 2014--2025 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Continuation_shortcut], after its interface
   middle_end/flambda2/simplify/continuation_shortcut.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Continuation Format Simple.

(* continuation_shortcut.mli:19  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Continuation_shortcut.t".
(* continuation_shortcut.mli:21  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Continuation_shortcut.print".
(* continuation_shortcut.mli:23  val create : params:Bound_parameters.t -> Continuation.t -> Simple.t list -> t *)
Parameter create : Bound_parameters.t -> Continuation.t -> list Simple.t -> M t.
Extract Inlined Constant create => "Continuation_shortcut.create".
(* continuation_shortcut.mli:25  val apply : t -> Simple.t list -> Continuation.t * Simple.t list *)
Parameter apply : t -> list Simple.t -> M (Continuation.t * list Simple.t).
Extract Inlined Constant apply => "Continuation_shortcut.apply".
(* continuation_shortcut.mli:27  val continuation : t -> Continuation.t *)
Parameter continuation : t -> M Continuation.t.
Extract Inlined Constant continuation => "Continuation_shortcut.continuation".
(* continuation_shortcut.mli:29  val to_alias : t -> Continuation.t option *)
Parameter to_alias : t -> M (option Continuation.t).
Extract Inlined Constant to_alias => "Continuation_shortcut.to_alias".
