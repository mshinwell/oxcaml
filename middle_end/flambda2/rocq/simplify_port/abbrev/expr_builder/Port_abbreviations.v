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

(* This file follows middle_end/flambda2/simplify/expr_builder.ml
   (Git blob a3609b8b785da3faf9aa88fdb5f28d697ec5f50a): the abbreviations of
   modules that that file makes itself (lines 18-26), as Rocq's [Module A :=
   P.], for Expr_builder.v (GUIDE.md, section 7, ABBREVIATIONS OF MODULES). The
   OCaml text at the head of Expr_builder.v has the compiler's own lines,
   [module A = P]. What is not from that file: the [Require] lines; and the name
   of the library: every such library is named Port_abbreviations, because Rocq
   writes [open Port_abbreviations] in an extracted file that needs it, and
   runtime/port_abbreviations.ml is that (empty) module. *)

From SimplifyPort.decl Require Bound_parameter Lifted_constant
  Lifted_constant_state Flambda_primitive Rebuilt_expr Upwards_acc Upwards_env
  Downwards_acc Bound_var.

Module BP := Bound_parameter.
Module LC := Lifted_constant.
Module LCS := Lifted_constant_state.
Module P := Flambda_primitive.
Module RE := Rebuilt_expr.
Module UA := Upwards_acc.
Module UE := Upwards_env.
Module DA := Downwards_acc.
Module VB := Bound_var.
