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
   Simplify uses of the compiler's module [Simplify_common], after its interface
   middle_end/flambda2/simplify/simplify_common.mli
   (Git blob afe17717c16e6ed2c1e7f335572fa4c1bb26e9d5). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Apply_expr Bound_parameters Bound_var Code_id Code_metadata Continuation Continuation_use_kind Debuginfo Downwards_acc Flambda Flambda2_types Flambda_arity Flambda_kind Flambda_primitive Loopify_state Or_bottom Rebuilt_expr Simple Simplified_expr Simplify_primitive_result Symbol_projection Target_system Upwards_acc.

(* simplify_common.mli:35  type after_rebuild = Rebuilt_expr.t -> Upwards_acc.t -> Rebuilt_expr.t * Upwards_acc.t *)
Definition after_rebuild : Type := Rebuilt_expr.t -> Upwards_acc.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Inlined Constant after_rebuild => "Simplify_common.after_rebuild".
(* simplify_common.mli:38  type 'a rebuild = 'a -> Upwards_acc.t -> after_rebuild:after_rebuild -> Rebuilt_expr.t * Upwards_acc.t *)
Definition rebuild (A : Type) : Type := A -> Upwards_acc.t -> after_rebuild -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Constant rebuild "'a1" => "('a1) Simplify_common.rebuild".
(* simplify_common.mli:51  type 'a down_to_up = Downwards_acc.t -> 'a -> Simplified_expr.t * Downwards_acc.t *)
Definition down_to_up (A : Type) : Type := Downwards_acc.t -> A -> M (Simplified_expr.t * Downwards_acc.t).
Extract Constant down_to_up "'a1" => "('a1) Simplify_common.down_to_up".
(* simplify_common.mli:75  type 'a expr_simplifier = Downwards_acc.t -> 'a -> down_to_up:Simplified_expr.t down_to_up -> Simplified_expr.t * Downwards_acc.t *)
Definition expr_simplifier (A : Type) : Type := Downwards_acc.t -> A -> down_to_up Simplified_expr.t -> M (Simplified_expr.t * Downwards_acc.t).
Extract Constant expr_simplifier "'a1" => "('a1) Simplify_common.expr_simplifier".
(* simplify_common.mli:81  type simplify_toplevel = Downwards_acc.t -> Expr.t -> return_continuation:Continuation.t -> return_arity:[`Complex] Flambda_arity.t -> exn_continuation:Continuation.t -> Rebuilt_expr.t * Upwards_acc.t *)
Definition simplify_toplevel : Type := Downwards_acc.t -> Flambda.Expr.t -> Continuation.t -> Flambda_arity.t_Complex -> Continuation.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Inlined Constant simplify_toplevel => "Simplify_common.simplify_toplevel".
(* simplify_common.mli:89  type simplify_function_body = Downwards_acc.t -> Expr.t -> return_continuation:Continuation.t -> return_arity:[`Complex] Flambda_arity.t -> exn_continuation:Continuation.t -> loopify_state:Loopify_state.t -> params:Bound_parameters.t -> implicit_params:Bound_parameters.t -> Rebuilt_expr.t * Upwards_acc.t *)
Definition simplify_function_body : Type := Downwards_acc.t -> Flambda.Expr.t -> Continuation.t -> Flambda_arity.t_Complex -> Continuation.t -> Loopify_state.t -> Bound_parameters.t -> Bound_parameters.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Inlined Constant simplify_function_body => "Simplify_common.simplify_function_body".
(* simplify_common.mli:100  val simplify_projection : Downwards_acc.t -> original_term:Named.t -> deconstructing:Flambda2_types.t -> shape:Flambda2_types.t -> result_var:Bound_var.t -> result_kind:Flambda_kind.t -> Simplify_primitive_result.t *)
Parameter simplify_projection : Downwards_acc.t -> Flambda.Named.t -> Flambda2_types.t -> Flambda2_types.t -> Bound_var.t -> Flambda_kind.t -> M Simplify_primitive_result.t.
Extract Inlined Constant simplify_projection => "Simplify_common.simplify_projection".
(* simplify_common.mli:109  val update_exn_continuation_extra_args : Upwards_acc.t -> exn_cont_use_id:Apply_cont_rewrite_id.t -> Apply_expr.t -> Apply_expr.t *)
Parameter update_exn_continuation_extra_args : Upwards_acc.t -> Apply_cont_rewrite_id.t -> Apply_expr.t -> M Apply_expr.t.
Extract Inlined Constant update_exn_continuation_extra_args => "Simplify_common.update_exn_continuation_extra_args".
(* simplify_common.mli:117  val project_tuple : machine_width:Target_system.Machine_width.t -> dbg:Debuginfo.t -> size:int -> field:int -> Simple.t -> Named.t *)
Parameter project_tuple : Target_system.Machine_width.t -> Debuginfo.t -> int -> int -> Simple.t -> M Flambda.Named.t.
Extract Inlined Constant project_tuple => "Simplify_common.project_tuple".
(* simplify_common.mli:127  val split_direct_over_application : Apply_expr.t -> callee's_code_id:Code_id.t -> callee's_code_metadata:Code_metadata.t -> Expr.t *)
Parameter split_direct_over_application : Apply_expr.t -> Code_id.t -> Code_metadata.t -> M Flambda.Expr.t.
Extract Inlined Constant split_direct_over_application => "Simplify_common.split_direct_over_application".
(* simplify_common.mli:133  type apply_cont_context = | Apply_cont_expr | Switch_branch *)
Inductive apply_cont_context : Type :=
| Apply_cont_expr : apply_cont_context
| Switch_branch : apply_cont_context.
Extract Inductive apply_cont_context => "Simplify_common.apply_cont_context" [ "Simplify_common.Apply_cont_expr" "Simplify_common.Switch_branch" ].
(* simplify_common.mli:137  val apply_cont_use_kind : context:apply_cont_context -> Apply_cont.t -> Continuation_use_kind.t *)
Parameter apply_cont_use_kind : apply_cont_context -> Flambda.Apply_cont.t -> M Continuation_use_kind.t.
Extract Inlined Constant apply_cont_use_kind => "Simplify_common.apply_cont_use_kind".
(* simplify_common.mli:140  val clear_demoted_trap_action_and_patch_unused_exn_bucket : Upwards_acc.t -> Apply_cont.t -> Apply_cont.t *)
Parameter clear_demoted_trap_action_and_patch_unused_exn_bucket : Upwards_acc.t -> Flambda.Apply_cont.t -> M Flambda.Apply_cont.t.
Extract Inlined Constant clear_demoted_trap_action_and_patch_unused_exn_bucket => "Simplify_common.clear_demoted_trap_action_and_patch_unused_exn_bucket".
(* simplify_common.mli:146  val specialise_array_kind : Downwards_acc.t -> Flambda_primitive.Array_kind.t -> array_ty:Flambda2_types.t -> Flambda_primitive.Array_kind.t Or_bottom.t *)
Parameter specialise_array_kind : Downwards_acc.t -> Flambda_primitive.Array_kind.t -> Flambda2_types.t -> M (Or_bottom.t Flambda_primitive.Array_kind.t).
Extract Inlined Constant specialise_array_kind => "Simplify_common.specialise_array_kind".
(* simplify_common.mli:171  val add_symbol_projection : Downwards_acc.t -> projected_from:Simple.t -> Symbol_projection.Projection.t -> projection_bound_to:Bound_var.t -> kind:Flambda_kind.With_subkind.t -> Downwards_acc.t *)
Parameter add_symbol_projection : Downwards_acc.t -> Simple.t -> Symbol_projection.Projection.t -> Bound_var.t -> Flambda_kind.With_subkind.t -> M Downwards_acc.t.
Extract Inlined Constant add_symbol_projection => "Simplify_common.add_symbol_projection".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_common. End Simplify_common.
