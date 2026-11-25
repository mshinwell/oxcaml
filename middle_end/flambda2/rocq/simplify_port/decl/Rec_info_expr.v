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
   Simplify uses of the compiler's module [Rec_info_expr], after its interface
   middle_end/flambda2/term_basics/rec_info_expr.mli
   (Git blob 17b57e86da7ef78320d87d1c9a9bd005f8ed486f). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Int_ids Or_infinity.

(* int_ids.mli:192  module Rec_info_expr : Rec_info_expr0.S with type variable = Variable.t *)
Definition variable : Type := Int_ids.Variable_.t.
Extract Inlined Constant variable => "Rec_info_expr.variable".
(* module Unrolling_state = Int_ids.Rec_info_expr.Unrolling_state: declared again here under this name. *)
Module Unrolling_state.
  (* rec_info_expr0.mli:23  type t = private | Not_unrolling ( ** Unrolling has not begun. * ) | Unrolling of { remaining_depth : int } ( ** Unrolling has begun and will continue until [remaining_depth] is zero. A subsequent [unroll_to] expression may increase the remaining depth. * ) | Do_not_unroll ( ** No unrolling may occur. [unroll_to] has no effect. * ) *)
  Definition t : Type := Int_ids.Rec_info_expr.Unrolling_state.t.
  Extract Inlined Constant t => "Rec_info_expr.Unrolling_state.t".
  (* rec_info_expr0.mli:33  val unrolling : remaining_depth:int -> t *)
  Parameter unrolling : int -> M t.
  Extract Inlined Constant unrolling => "Rec_info_expr.Unrolling_state.unrolling".
End Unrolling_state.
(* rec_info_expr0.mli:46  type t = private | Const of { depth : int Or_infinity.t; unrolling : Unrolling_state.t } | Var of variable ( ** A variable of kind [Flambda_kind.rec_info]. * ) | Succ of t ( ** The next depth. If we inline an occurrence with depth [d], then in the inlined body, recursive references will have depth [succ d]. * ) | Unroll_to of int * t *)
Definition t : Type := Int_ids.Rec_info_expr.t.
Extract Inlined Constant t => "Rec_info_expr.t".
(* rec_info_expr0.mli:60  val initial : t *)
Parameter initial : t.
Extract Inlined Constant initial => "Rec_info_expr.initial".
(* rec_info_expr0.mli:62  val unknown : t *)
Parameter unknown : t.
Extract Inlined Constant unknown => "Rec_info_expr.unknown".
(* rec_info_expr0.mli:64  val do_not_inline : t *)
Parameter do_not_inline : t.
Extract Inlined Constant do_not_inline => "Rec_info_expr.do_not_inline".
(* rec_info_expr0.mli:66  val const : depth:int Or_infinity.t -> unrolling:Unrolling_state.t -> t *)
Parameter const : Or_infinity.t int -> Rec_info_expr.Unrolling_state.t -> M t.
Extract Inlined Constant const => "Rec_info_expr.const".
(* rec_info_expr0.mli:68  val var : variable -> t *)
Parameter var : variable -> M t.
Extract Inlined Constant var => "Rec_info_expr.var".
(* rec_info_expr0.mli:70  val succ : t -> t *)
Parameter succ : t -> M t.
Extract Inlined Constant succ => "Rec_info_expr.succ".
(* rec_info_expr0.mli:72  val unroll_to : int -> t -> t *)
Parameter unroll_to : int -> t -> M t.
Extract Inlined Constant unroll_to => "Rec_info_expr.unroll_to".
(* rec_info_expr.mli:21  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Rec_info_expr.print".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Rec_info_expr. End Rec_info_expr.
