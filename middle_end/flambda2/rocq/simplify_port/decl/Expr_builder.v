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
   Simplify uses of the compiler's module [Expr_builder], after its interface
   middle_end/flambda2/simplify/expr_builder.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite Apply_cont_rewrite_id Bound_pattern Continuation Cost_metrics Debuginfo Exn_continuation Flambda Flambda_arity Lifted_constant Lifted_constant_state Name_occurrences Rebuilt_expr Simple Simplified_named Switch_arm Target_ocaml_int Upwards_acc Upwards_env.

(* expr_builder.mli:28  val create_let_binding : Upwards_acc.t -> Bound_pattern.t -> Named.t -> free_names_of_defining_expr:Name_occurrences.t -> body:Rebuilt_expr.t -> cost_metrics_of_defining_expr:Cost_metrics.t -> Rebuilt_expr.t * Upwards_acc.t *)
Parameter create_let_binding : Upwards_acc.t -> Bound_pattern.t -> Flambda.Import_.Named.t -> Name_occurrences.t -> Rebuilt_expr.t -> Cost_metrics.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Inlined Constant create_let_binding => "Expr_builder.create_let_binding".
(* expr_builder.mli:44  val make_new_let_bindings : Upwards_acc.t -> bindings_outermost_first:Simplified_named.binding_to_place list -> body:Rebuilt_expr.t -> Rebuilt_expr.t * Upwards_acc.t *)
Parameter make_new_let_bindings : Upwards_acc.t -> list Simplified_named.binding_to_place -> Rebuilt_expr.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Inlined Constant make_new_let_bindings => "Expr_builder.make_new_let_bindings".
(* expr_builder.mli:58  val create_let_symbols : Upwards_acc.t -> Lifted_constant.t -> body:Rebuilt_expr.t -> Rebuilt_expr.t * Upwards_acc.t *)
Parameter create_let_symbols : Upwards_acc.t -> Lifted_constant.t -> Rebuilt_expr.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Inlined Constant create_let_symbols => "Expr_builder.create_let_symbols".
(* expr_builder.mli:66  val place_lifted_constants : Upwards_acc.t -> lifted_constants_from_defining_expr:Lifted_constant_state.t -> lifted_constants_from_body:Lifted_constant_state.t -> put_bindings_around_body: (Upwards_acc.t -> body:Rebuilt_expr.t -> Rebuilt_expr.t * Upwards_acc.t) -> body:Rebuilt_expr.t -> Rebuilt_expr.t * Upwards_acc.t *)
Parameter place_lifted_constants : Upwards_acc.t -> Lifted_constant_state.t -> Lifted_constant_state.t -> (Upwards_acc.t -> Rebuilt_expr.t -> M (Rebuilt_expr.t * Upwards_acc.t)) -> Rebuilt_expr.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Inlined Constant place_lifted_constants => "Expr_builder.place_lifted_constants".
(* expr_builder.mli:77  val create_switch : Upwards_acc.t -> condition_dbg:Debuginfo.t -> scrutinee:Simple.t -> arms:Switch_arm.t Target_ocaml_int.Map.t -> Rebuilt_expr.t * Upwards_acc.t *)
Parameter create_switch : Upwards_acc.t -> Debuginfo.t -> Simple.t -> Target_ocaml_int.Map.t Switch_arm.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Inlined Constant create_switch => "Expr_builder.create_switch".
(* expr_builder.mli:84  type new_let_cont = { cont : Continuation.t; handler : Rebuilt_expr.Continuation_handler.t; free_names_of_handler : Name_occurrences.t; cost_metrics_of_handler : Cost_metrics.t } *)
Record new_let_cont : Type := { cont : Continuation.t; handler : Rebuilt_expr.Continuation_handler.t; free_names_of_handler : Name_occurrences.t; cost_metrics_of_handler : Cost_metrics.t }.
(* expr_builder.mli:91  val bind_let_conts : Upwards_acc.t -> body:Rebuilt_expr.t -> new_let_cont list -> Upwards_acc.t * Rebuilt_expr.t *)
Parameter bind_let_conts : Upwards_acc.t -> Rebuilt_expr.t -> list new_let_cont -> M (Upwards_acc.t * Rebuilt_expr.t).
Extract Inlined Constant bind_let_conts => "Expr_builder.bind_let_conts".
(* expr_builder.mli:97  val rebuild_invalid : Upwards_acc.t -> Flambda.Invalid.t -> after_rebuild: (Rebuilt_expr.t -> Upwards_acc.t -> Rebuilt_expr.t * Upwards_acc.t) -> Rebuilt_expr.t * Upwards_acc.t *)
Parameter rebuild_invalid : Upwards_acc.t -> Flambda.Invalid.t -> (Rebuilt_expr.t -> Upwards_acc.t -> M (Rebuilt_expr.t * Upwards_acc.t)) -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Inlined Constant rebuild_invalid => "Expr_builder.rebuild_invalid".
(* expr_builder.mli:106  type rewrite_apply_cont_result = private | Invalid of { message : string } | Apply_cont of Apply_cont.t | Expr of (apply_cont_to_expr: (Apply_cont.t -> Rebuilt_expr.t * Cost_metrics.t * Name_occurrences.t) -> Rebuilt_expr.t * Cost_metrics.t * Name_occurrences.t) *)
Record invalid_payload_ : Type := { message : string }.
Inductive rewrite_apply_cont_result : Type :=
| Invalid : invalid_payload_ -> rewrite_apply_cont_result
| Apply_cont : Flambda.Import_.Apply_cont.t -> rewrite_apply_cont_result
| Expr : ((Flambda.Import_.Apply_cont.t -> M (tuple3 Rebuilt_expr.t Cost_metrics.t Name_occurrences.t)) -> M (tuple3 Rebuilt_expr.t Cost_metrics.t Name_occurrences.t)) -> rewrite_apply_cont_result.
(* expr_builder.mli:114  type rewrite_switch_arm_result = private | Invalid of { message : string } | Apply_cont of Apply_cont.t | New_wrapper of new_let_cont *)
(* PORT-GAP(type): the name of the field [message] is taken in Rocq: abstract, with a maker for each constructor and one eliminator. *)
Parameter rewrite_switch_arm_result : Type.
Extract Inlined Constant rewrite_switch_arm_result => "Expr_builder.rewrite_switch_arm_result".
Parameter match_rewrite_switch_arm_result : forall {Res : Type}, rewrite_switch_arm_result -> (string -> M Res) -> (Flambda.Import_.Apply_cont.t -> M Res) -> (new_let_cont -> M Res) -> M Res.
Extract Inlined Constant match_rewrite_switch_arm_result => "(fun x__0 f__1 f__2 f__3 -> match x__0 with Expr_builder.Invalid { message = x__1 } -> f__1 x__1 | Expr_builder.Apply_cont x__1 -> f__2 x__1 | Expr_builder.New_wrapper x__1 -> f__3 x__1)".
(* expr_builder.mli:119  val no_rewrite_apply_cont : Upwards_env.t -> Apply_cont.t -> rewrite_apply_cont_result *)
Parameter no_rewrite_apply_cont : Upwards_env.t -> Flambda.Import_.Apply_cont.t -> M rewrite_apply_cont_result.
Extract Inlined Constant no_rewrite_apply_cont => "Expr_builder.no_rewrite_apply_cont".
(* expr_builder.mli:122  val rewrite_apply_cont : Upwards_acc.t -> Apply_cont_rewrite.t -> Apply_cont_rewrite_id.t -> Apply_cont.t -> rewrite_apply_cont_result *)
Parameter rewrite_apply_cont : Upwards_acc.t -> Apply_cont_rewrite.t -> Apply_cont_rewrite_id.t -> Flambda.Import_.Apply_cont.t -> M rewrite_apply_cont_result.
Extract Inlined Constant rewrite_apply_cont => "Expr_builder.rewrite_apply_cont".
(* expr_builder.mli:129  val rewrite_switch_arm : Upwards_acc.t -> Apply_cont.t -> use_id:Apply_cont_rewrite_id.t -> [`Unarized] Flambda_arity.t -> rewrite_switch_arm_result *)
Parameter rewrite_switch_arm : Upwards_acc.t -> Flambda.Import_.Apply_cont.t -> Apply_cont_rewrite_id.t -> Flambda_arity.t -> M rewrite_switch_arm_result.
Extract Inlined Constant rewrite_switch_arm => "Expr_builder.rewrite_switch_arm".
(* expr_builder.mli:136  val rewrite_fixed_arity_apply : Upwards_acc.t -> use_id:Apply_cont_rewrite_id.t option -> is_cold:bool -> [`Unarized] Flambda_arity.t -> Apply.t -> Upwards_acc.t * Rebuilt_expr.t *)
Parameter rewrite_fixed_arity_apply : Upwards_acc.t -> option Apply_cont_rewrite_id.t -> bool -> Flambda_arity.t -> Flambda.Import_.Apply.t -> M (Upwards_acc.t * Rebuilt_expr.t).
Extract Inlined Constant rewrite_fixed_arity_apply => "Expr_builder.rewrite_fixed_arity_apply".
(* expr_builder.mli:144  val rewrite_exn_continuation : Apply_cont_rewrite.t -> Apply_cont_rewrite_id.t -> Exn_continuation.t -> Exn_continuation.t *)
Parameter rewrite_exn_continuation : Apply_cont_rewrite.t -> Apply_cont_rewrite_id.t -> Exn_continuation.t -> M Exn_continuation.t.
Extract Inlined Constant rewrite_exn_continuation => "Expr_builder.rewrite_exn_continuation".
