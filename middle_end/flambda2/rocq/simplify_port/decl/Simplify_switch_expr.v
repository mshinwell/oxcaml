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
   Simplify uses of the compiler's module [Simplify_switch_expr], after its interface
   middle_end/flambda2/simplify/simplify_switch_expr.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda Simplified_expr Simplify_common.

(* simplify_switch_expr.mli:17  val simplify_switch : Flambda.Switch.t Simplify_common.expr_simplifier *)
Parameter simplify_switch : Simplify_common.expr_simplifier Flambda.Switch.t.
Extract Inlined Constant simplify_switch => "Simplify_switch_expr.simplify_switch".
(* simplify_switch_expr.mli:19  val rebuild_switch : Simplified_expr.simplified_switch Simplify_common.rebuild *)
Parameter rebuild_switch : Simplify_common.rebuild Simplified_expr.simplified_switch_.
Extract Inlined Constant rebuild_switch => "Simplify_switch_expr.rebuild_switch".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_switch_expr. End Simplify_switch_expr.
