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
   Simplify uses of the compiler's module [Apply_cont_rewrite], after its interface
   middle_end/flambda2/simplify/apply_cont_rewrite.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter Bound_parameters Bound_var Code_size Continuation_extra_params_and_args Exn_continuation Flambda Flambda_arity Format Or_invalid Simple Target_system.

(* apply_cont_rewrite.mli:22  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Apply_cont_rewrite.t".
(* apply_cont_rewrite.mli:24  type used = | Unused | Used | Used_as_invariant *)
Inductive used : Type :=
| Unused : used
| Used : used
| Used_as_invariant : used.
Extract Inductive used => "Apply_cont_rewrite.used" [ "Apply_cont_rewrite.Unused" "Apply_cont_rewrite.Used" "Apply_cont_rewrite.Used_as_invariant" ].
(* apply_cont_rewrite.mli:29  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Apply_cont_rewrite.print".
(* apply_cont_rewrite.mli:33  val create : original_params:Bound_parameters.t -> extra_params_and_args:Continuation_extra_params_and_args.t -> decide_param_usage:(Bound_parameter.t -> used) -> t *)
Parameter create : Bound_parameters.t -> Continuation_extra_params_and_args.t -> (Bound_parameter.t -> M used) -> M t.
Extract Inlined Constant create => "Apply_cont_rewrite.create".
(* apply_cont_rewrite.mli:39  val does_nothing : t -> bool *)
Parameter does_nothing : t -> M bool.
Extract Inlined Constant does_nothing => "Apply_cont_rewrite.does_nothing".
(* apply_cont_rewrite.mli:41  val get_used_params : t -> Bound_parameters.t * Bound_parameters.t *)
Parameter get_used_params : t -> M (Bound_parameters.t * Bound_parameters.t).
Extract Inlined Constant get_used_params => "Apply_cont_rewrite.get_used_params".
(* apply_cont_rewrite.mli:43  val get_unused_params : t -> Bound_parameters.t *)
Parameter get_unused_params : t -> M Bound_parameters.t.
Extract Inlined Constant get_unused_params => "Apply_cont_rewrite.get_unused_params".
(* apply_cont_rewrite.mli:45  val original_params_arity : t -> [> ] Flambda_arity.t *)
Parameter original_params_arity : t -> M Flambda_arity.t.
Extract Inlined Constant original_params_arity => "Apply_cont_rewrite.original_params_arity".
(* apply_cont_rewrite.mli:47  type rewrite_apply_cont_ctx = | Apply_cont | Apply_expr of Simple.t list *)
Inductive rewrite_apply_cont_ctx : Type :=
| Apply_cont : rewrite_apply_cont_ctx
| Apply_expr : list Simple.t -> rewrite_apply_cont_ctx.
Extract Inductive rewrite_apply_cont_ctx => "Apply_cont_rewrite.rewrite_apply_cont_ctx" [ "Apply_cont_rewrite.Apply_cont" "Apply_cont_rewrite.Apply_expr" ].
(* apply_cont_rewrite.mli:51  val make_rewrite : t -> machine_width:Target_system.Machine_width.t -> ctx:rewrite_apply_cont_ctx -> Apply_cont_rewrite_id.t -> Simple.t list -> ((Bound_var.t * Code_size.t * Flambda.Named.t) list * Simple.t list) Or_invalid.t *)
Parameter make_rewrite : t -> Target_system.Machine_width.t -> rewrite_apply_cont_ctx -> Apply_cont_rewrite_id.t -> list Simple.t -> M (Or_invalid.t (list (tuple3 Bound_var.t Code_size.t Flambda.Named.t) * list Simple.t)).
Extract Inlined Constant make_rewrite => "Apply_cont_rewrite.make_rewrite".
(* apply_cont_rewrite.mli:60  val rewrite_exn_continuation : t -> Apply_cont_rewrite_id.t -> Exn_continuation.t -> Exn_continuation.t *)
Parameter rewrite_exn_continuation : t -> Apply_cont_rewrite_id.t -> Exn_continuation.t -> M Exn_continuation.t.
Extract Inlined Constant rewrite_exn_continuation => "Apply_cont_rewrite.rewrite_exn_continuation".
