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
   Simplify uses of the compiler's module [Simplify_expr], after its interface
   middle_end/flambda2/simplify/simplify_expr.mli
   (Git blob 6bf051a61a9365a07388dadc0bbd4ff6416b338c). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda Simplify_common.

(* simplify_expr.mli:46  val simplify_expr : Flambda.Expr.t Simplify_common.expr_simplifier *)
Parameter simplify_expr : Simplify_common.expr_simplifier Flambda.Expr.t.
Extract Inlined Constant simplify_expr => "Simplify_expr.simplify_expr".
(* simplify_expr.mli:51  val simplify_toplevel : Simplify_common.simplify_toplevel *)
Parameter simplify_toplevel : Simplify_common.simplify_toplevel.
Extract Inlined Constant simplify_toplevel => "Simplify_expr.simplify_toplevel".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_expr. End Simplify_expr.
