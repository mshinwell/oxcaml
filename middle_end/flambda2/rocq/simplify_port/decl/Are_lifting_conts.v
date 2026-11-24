(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Are_lifting_conts], after its interface
   middle_end/flambda2/simplify/are_lifting_conts.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Continuation_uses Format.

(* are_lifting_conts.mli:51  type reason = | At_toplevel | In_speculative_inlining | In_continuation_specialization | In_recursive_continuation | In_inlinable_continuation *)
Inductive reason : Type :=
| At_toplevel : reason
| In_speculative_inlining : reason
| In_continuation_specialization : reason
| In_recursive_continuation : reason
| In_inlinable_continuation : reason.
(* are_lifting_conts.mli:59  type t = private | Not_lifting of reason | Analyzing of { continuation : Continuation.t; is_exn_handler : bool; uses : Continuation_uses.t } | Lifting_out_of of { continuation : Continuation.t } *)
Parameter t : Type.
Extract Inlined Constant t => "Are_lifting_conts.t".
(* are_lifting_conts.mli:70  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Are_lifting_conts.print".
(* are_lifting_conts.mli:73  val no_lifting : reason -> t *)
Parameter no_lifting : reason -> M t.
Extract Inlined Constant no_lifting => "Are_lifting_conts.no_lifting".
(* are_lifting_conts.mli:76  val think_about_lifting_out_of : is_exn_handler:bool -> Continuation.t -> Continuation_uses.t -> t *)
Parameter think_about_lifting_out_of : bool -> Continuation.t -> Continuation_uses.t -> M t.
Extract Inlined Constant think_about_lifting_out_of => "Are_lifting_conts.think_about_lifting_out_of".
(* are_lifting_conts.mli:80  val lift_continuations_out_of : Continuation.t -> t *)
Parameter lift_continuations_out_of : Continuation.t -> M t.
Extract Inlined Constant lift_continuations_out_of => "Are_lifting_conts.lift_continuations_out_of".
