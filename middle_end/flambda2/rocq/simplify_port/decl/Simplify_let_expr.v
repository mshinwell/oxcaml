(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplify_let_expr], after its interface
   middle_end/flambda2/simplify/simplify_let_expr.mli
   (Git blob a4a4ff935b427d0413fbbd359d7e7833a9653c1d). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda Rebuilt_expr Simplified_expr Simplify_common.

(* simplify_let_expr.mli:19  val simplify_let : simplify_expr:Expr.t Simplify_common.expr_simplifier -> simplify_function_body:Simplify_common.simplify_function_body -> Let.t Simplify_common.expr_simplifier *)
Parameter simplify_let : Simplify_common.expr_simplifier Flambda.Expr.t -> Simplify_common.simplify_function_body -> Simplify_common.expr_simplifier Flambda.Let.t.
Extract Inlined Constant simplify_let => "Simplify_let_expr.simplify_let".
(* simplify_let_expr.mli:24  val rebuild_let : (Simplified_expr.simplified_defining_expr * Rebuilt_expr.t) Simplify_common.rebuild *)
Parameter rebuild_let : Simplify_common.rebuild (Simplified_expr.simplified_defining_expr * Rebuilt_expr.t).
Extract Inlined Constant rebuild_let => "Simplify_let_expr.rebuild_let".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_let_expr. End Simplify_let_expr.
