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
   Simplify uses of the compiler's module [Inlining_helpers], after its interface
   middle_end/flambda2/simplify_shared/inlining_helpers.mli
   (Git blob bd55cb71e8213a7a361953458e55dd45bb730a02). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Bound_parameters Code_id Continuation Debuginfo Exn_continuation Flambda Flambda_arity Flambda_kind Rec_info_expr Renaming Simple Trap_action Variable_.

(* inlining_helpers.mli:17  val make_inlined_body : callee:Simple.t option -> called_code_id:Code_id.t -> region_inlined_into:Alloc_mode.For_applications.t -> params:'param list -> args:Simple.List.t -> my_closure:'param -> my_alloc_mode:Alloc_mode.For_applications.t -> my_depth:Variable.t -> rec_info:Rec_info_expr.t -> body:'expr_with_acc -> exn_continuation:Continuation.t -> return_continuation:Continuation.t -> apply_e... *)
Parameter make_inlined_body : forall {Param Expr_with_acc : Type}, option Simple.t -> Code_id.t -> Alloc_mode.For_applications.t -> list Param -> Simple.List.t -> Param -> Alloc_mode.For_applications.t -> Variable_.t -> Rec_info_expr.t -> Expr_with_acc -> Continuation.t -> Continuation.t -> Continuation.t -> Flambda.Apply.Result_continuation.t -> (list Param -> Simple.List.t -> Expr_with_acc -> M Expr_with_acc) -> (Variable_.t -> Rec_info_expr.t -> Expr_with_acc -> M Expr_with_acc) -> (Expr_with_acc -> Renaming.t -> M Expr_with_acc) -> M Expr_with_acc.
Extract Inlined Constant make_inlined_body => "Inlining_helpers.make_inlined_body".
(* inlining_helpers.mli:45  val wrap_inlined_body_for_exn_extra_args : 'acc -> extra_args:(Simple.t * Flambda_kind.With_subkind.t) list -> apply_exn_continuation:Exn_continuation.t -> apply_return_continuation:Flambda.Apply.Result_continuation.t -> result_arity:_ Flambda_arity.t -> make_inlined_body: ('acc -> apply_exn_continuation:Continuation.t -> apply_return_continuation:Flambda.Apply.Result_continuation.t -> 'expr_wi... *)
Parameter wrap_inlined_body_for_exn_extra_args : forall {Acc Expr_with_acc : Type}, Acc -> list (Simple.t * Flambda_kind.With_subkind.t) -> Exn_continuation.t -> Flambda.Apply.Result_continuation.t -> Flambda_arity.t -> (Acc -> Continuation.t -> Flambda.Apply.Result_continuation.t -> M Expr_with_acc) -> (Acc -> Trap_action.t -> Continuation.t -> Simple.List.t -> Debuginfo.t -> M Expr_with_acc) -> (Acc -> Continuation.t -> Bound_parameters.t -> (Acc -> M Expr_with_acc) -> (Acc -> M Expr_with_acc) -> bool -> bool -> M Expr_with_acc) -> M Expr_with_acc.
Extract Inlined Constant wrap_inlined_body_for_exn_extra_args => "Inlining_helpers.wrap_inlined_body_for_exn_extra_args".
(* inlining_helpers.mli:74  type attribute_kind = | Inlined | Unrolled *)
Inductive attribute_kind : Type :=
| Inlined : attribute_kind
| Unrolled : attribute_kind.
Extract Inductive attribute_kind => "Inlining_helpers.attribute_kind" [ "Inlining_helpers.Inlined" "Inlining_helpers.Unrolled" ].
(* inlining_helpers.mli:78  val inlined_attribute_on_partial_application_msg : attribute_kind -> string *)
Parameter inlined_attribute_on_partial_application_msg : attribute_kind -> M string.
Extract Inlined Constant inlined_attribute_on_partial_application_msg => "Inlining_helpers.inlined_attribute_on_partial_application_msg".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Inlining_helpers. End Inlining_helpers.
