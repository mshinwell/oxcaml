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
   Simplify uses of the compiler's module [Simplify_apply_cont_expr], after its interface
   middle_end/flambda2/simplify/simplify_apply_cont_expr.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_expr Apply_cont_rewrite_id Flambda Simple Simplify_common.

(* simplify_apply_cont_expr.mli:17  val simplify_apply_cont : Flambda.Apply_cont.t Simplify_common.expr_simplifier *)
Parameter simplify_apply_cont : Simplify_common.expr_simplifier Flambda.Apply_cont.t.
Extract Inlined Constant simplify_apply_cont => "Simplify_apply_cont_expr.simplify_apply_cont".
(* simplify_apply_cont_expr.mli:19  val rebuild_apply_cont : args:Simple.t list -> rewrite_id:Apply_cont_rewrite_id.t -> Apply_cont_expr.t Simplify_common.rebuild *)
Parameter rebuild_apply_cont : list Simple.t -> Apply_cont_rewrite_id.t -> Simplify_common.rebuild Apply_cont_expr.t.
Extract Inlined Constant rebuild_apply_cont => "Simplify_apply_cont_expr.rebuild_apply_cont".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_apply_cont_expr. End Simplify_apply_cont_expr.
