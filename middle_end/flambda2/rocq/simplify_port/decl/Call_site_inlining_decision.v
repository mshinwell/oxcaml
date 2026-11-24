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
   Simplify uses of the compiler's module [Call_site_inlining_decision], after its interface
   middle_end/flambda2/simplify/inlining/call_site_inlining_decision.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Call_site_inlining_decision_type Downwards_acc Flambda Flambda2_types Flambda_arity Rec_info_expr Simplified_expr Simplify_common.

(* call_site_inlining_decision.mli:19  val make_decision : Downwards_acc.t -> simplify_expr:Expr.t Simplify_common.expr_simplifier -> rebuild_expr:Simplified_expr.t Simplify_common.rebuild -> function_type:Flambda2_types.Function_type.t -> apply:Apply.t -> return_arity:[`Complex] Flambda_arity.t -> Call_site_inlining_decision_type.t *)
Parameter make_decision : Downwards_acc.t -> Simplify_common.expr_simplifier Flambda.Import_.Expr.t -> Simplify_common.rebuild Simplified_expr.t -> Flambda2_types.Function_type.t -> Flambda.Import_.Apply.t -> Flambda_arity.t -> M Call_site_inlining_decision_type.t.
Extract Inlined Constant make_decision => "Call_site_inlining_decision.make_decision".
(* call_site_inlining_decision.mli:28  val get_rec_info : Downwards_acc.t -> function_type:Flambda2_types.Function_type.t -> Rec_info_expr.t *)
Parameter get_rec_info : Downwards_acc.t -> Flambda2_types.Function_type.t -> M Rec_info_expr.t.
Extract Inlined Constant get_rec_info => "Call_site_inlining_decision.get_rec_info".
