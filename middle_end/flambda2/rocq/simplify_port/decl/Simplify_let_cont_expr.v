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
   Simplify uses of the compiler's module [Simplify_let_cont_expr], after its interface
   middle_end/flambda2/simplify/simplify_let_cont_expr.mli
   (Git blob 249cc4eb637dc3e61aa1a4b43e84ba052c9c5354). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Flambda Simplified_expr Simplify_common.

(* simplify_let_cont_expr.mli:19  val simplify_let_cont : simplify_expr:Expr.t Simplify_common.expr_simplifier -> Let_cont.t Simplify_common.expr_simplifier *)
Parameter simplify_let_cont : Simplify_common.expr_simplifier Flambda.Expr.t -> Simplify_common.expr_simplifier Flambda.Let_cont.t.
Extract Inlined Constant simplify_let_cont => "Simplify_let_cont_expr.simplify_let_cont".
(* simplify_let_cont_expr.mli:23  val simplify_as_recursive_let_cont : simplify_expr:Expr.t Simplify_common.expr_simplifier -> (Expr.t * Continuation_handler.t Continuation.Lmap.t) Simplify_common.expr_simplifier *)
Parameter simplify_as_recursive_let_cont : Simplify_common.expr_simplifier Flambda.Expr.t -> Simplify_common.expr_simplifier (Flambda.Expr.t * Continuation.Lmap.t Flambda.Continuation_handler.t).
Extract Inlined Constant simplify_as_recursive_let_cont => "Simplify_let_cont_expr.simplify_as_recursive_let_cont".
(* simplify_let_cont_expr.mli:28  val rebuild_let_cont : rebuild_body:'a Simplify_common.rebuild -> rebuild_expr:Simplified_expr.t Simplify_common.rebuild -> (Simplified_expr.simplified_let_cont_handlers * 'a) Simplify_common.rebuild *)
Parameter rebuild_let_cont : forall {A : Type}, Simplify_common.rebuild A -> Simplify_common.rebuild Simplified_expr.t -> Simplify_common.rebuild (Simplified_expr.simplified_let_cont_handlers * A).
Extract Inlined Constant rebuild_let_cont => "Simplify_let_cont_expr.rebuild_let_cont".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_let_cont_expr. End Simplify_let_cont_expr.
