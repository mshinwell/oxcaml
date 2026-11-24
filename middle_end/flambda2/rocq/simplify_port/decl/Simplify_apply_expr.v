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
   Simplify uses of the compiler's module [Simplify_apply_expr], after its interface
   middle_end/flambda2/simplify/simplify_apply_expr.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda Simplified_expr Simplify_common.

(* simplify_apply_expr.mli:19  val simplify_apply : simplify_expr:Expr.t Simplify_common.expr_simplifier -> rebuild_expr:Simplified_expr.t Simplify_common.rebuild -> Apply.t Simplify_common.expr_simplifier *)
Parameter simplify_apply : Simplify_common.expr_simplifier Flambda.Expr.t -> Simplify_common.rebuild Simplified_expr.t -> Simplify_common.expr_simplifier Flambda.Apply.t.
Extract Inlined Constant simplify_apply => "Simplify_apply_expr.simplify_apply".
(* simplify_apply_expr.mli:24  val rebuild_apply : Simplified_expr.simplified_apply Simplify_common.rebuild *)
Parameter rebuild_apply : Simplify_common.rebuild Simplified_expr.simplified_apply_.
Extract Inlined Constant rebuild_apply => "Simplify_apply_expr.rebuild_apply".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_apply_expr. End Simplify_apply_expr.
