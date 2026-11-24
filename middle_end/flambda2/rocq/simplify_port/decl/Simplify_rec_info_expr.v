(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplify_rec_info_expr], after its interface
   middle_end/flambda2/simplify/simplify_rec_info_expr.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Downwards_acc Format Rec_info_expr.

(* simplify_rec_info_expr.mli:19  val simplify_rec_info_expr : Downwards_acc.t -> Rec_info_expr.t -> Rec_info_expr.t *)
Parameter simplify_rec_info_expr : Downwards_acc.t -> Rec_info_expr.t -> M Rec_info_expr.t.
Extract Inlined Constant simplify_rec_info_expr => "Simplify_rec_info_expr.simplify_rec_info_expr".
Module Evaluated_rec_info_expr.
  (* simplify_rec_info_expr.mli:23  type t = private { depth : int Or_infinity.t; unrolling : Rec_info_expr.Unrolling_state.t } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Simplify_rec_info_expr.Evaluated_rec_info_expr.t".
  (* simplify_rec_info_expr.mli:28  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Simplify_rec_info_expr.Evaluated_rec_info_expr.print".
End Evaluated_rec_info_expr.
(* simplify_rec_info_expr.mli:31  val evaluate_rec_info_expr : Downwards_acc.t -> Rec_info_expr.t -> Evaluated_rec_info_expr.t *)
Parameter evaluate_rec_info_expr : Downwards_acc.t -> Rec_info_expr.t -> M Simplify_rec_info_expr.Evaluated_rec_info_expr.t.
Extract Inlined Constant evaluate_rec_info_expr => "Simplify_rec_info_expr.evaluate_rec_info_expr".
(* simplify_rec_info_expr.mli:34  val depth_may_exceed : Downwards_acc.t -> Rec_info_expr.t -> int -> bool *)
Parameter depth_may_exceed : Downwards_acc.t -> Rec_info_expr.t -> int -> M bool.
Extract Inlined Constant depth_may_exceed => "Simplify_rec_info_expr.depth_may_exceed".
(* simplify_rec_info_expr.mli:36  val known_remaining_unrolling_depth : Downwards_acc.t -> Rec_info_expr.t -> int option *)
Parameter known_remaining_unrolling_depth : Downwards_acc.t -> Rec_info_expr.t -> M (option int).
Extract Inlined Constant known_remaining_unrolling_depth => "Simplify_rec_info_expr.known_remaining_unrolling_depth".
(* simplify_rec_info_expr.mli:39  val can_unroll : Downwards_acc.t -> Rec_info_expr.t -> bool *)
Parameter can_unroll : Downwards_acc.t -> Rec_info_expr.t -> M bool.
Extract Inlined Constant can_unroll => "Simplify_rec_info_expr.can_unroll".
