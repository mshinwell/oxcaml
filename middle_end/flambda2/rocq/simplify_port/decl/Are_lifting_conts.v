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
   (Git blob c1e9983a7ad171967bfd45f8a10becaab682b1e5). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Continuation_uses Format.

(* are_lifting_conts.mli:51  type reason = | At_toplevel | In_speculative_inlining | In_continuation_specialization | In_recursive_continuation | In_inlinable_continuation *)
Inductive reason : Type :=
| At_toplevel : reason
| In_speculative_inlining : reason
| In_continuation_specialization : reason
| In_recursive_continuation : reason
| In_inlinable_continuation : reason.
Extract Inductive reason => "Are_lifting_conts.reason" [ "Are_lifting_conts.At_toplevel" "Are_lifting_conts.In_speculative_inlining" "Are_lifting_conts.In_continuation_specialization" "Are_lifting_conts.In_recursive_continuation" "Are_lifting_conts.In_inlinable_continuation" ].
(* are_lifting_conts.mli:59  type t = private | Not_lifting of reason | Analyzing of { continuation : Continuation.t; is_exn_handler : bool; uses : Continuation_uses.t } | Lifting_out_of of { continuation : Continuation.t } *)
Inductive t : Type :=
| Not_lifting : reason -> t
| Analyzing : Continuation.t -> bool -> Continuation_uses.t -> t
| Lifting_out_of : Continuation.t -> t.
Extract Inductive t => "Are_lifting_conts.t" [ "Are_lifting_conts.Not_lifting" "(fun (x__1, x__2, x__3) -> (Are_lifting_conts.Analyzing { continuation = x__1; is_exn_handler = x__2; uses = x__3 } : Are_lifting_conts.t))" "(fun x__1 -> (Are_lifting_conts.Lifting_out_of { continuation = x__1 } : Are_lifting_conts.t))" ] "(fun f__1 f__2 f__3 x__0 -> match (x__0 : Are_lifting_conts.t) with Are_lifting_conts.Not_lifting x__1 -> f__1 x__1 | Are_lifting_conts.Analyzing { continuation = x__1; is_exn_handler = x__2; uses = x__3 } -> f__2 x__1 x__2 x__3 | Are_lifting_conts.Lifting_out_of { continuation = x__1 } -> f__3 x__1)".
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

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Are_lifting_conts. End Are_lifting_conts.
