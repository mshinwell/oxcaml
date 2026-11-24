(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Upwards_env], after its interface
   middle_end/flambda2/simplify/env/upwards_env.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite Are_rebuilding_terms Bound_parameters Continuation Continuation_in_env Continuation_shortcut Cost_metrics Flambda_arity Format Name_occurrences Or_unknown Rebuilt_expr Simple Target_system.

(* upwards_env.mli:19  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Upwards_env.t".
(* upwards_env.mli:24  val create : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> t *)
Parameter create : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> M t.
Extract Inlined Constant create => "Upwards_env.create".
(* upwards_env.mli:27  val machine_width : t -> Target_system.Machine_width.t *)
Parameter machine_width : t -> M Target_system.Machine_width.t.
Extract Inlined Constant machine_width => "Upwards_env.machine_width".
(* upwards_env.mli:29  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Upwards_env.print".
(* upwards_env.mli:31  val add_non_inlinable_continuation : Are_rebuilding_terms.t -> t -> Continuation.t -> is_cold:bool -> params:Bound_parameters.t -> handler: (Rebuilt_expr.t * is_exn_handler:bool * free_names_without_params:Name_occurrences.t) Or_unknown.t -> t *)
Parameter add_non_inlinable_continuation : Are_rebuilding_terms.t -> t -> Continuation.t -> bool -> Bound_parameters.t -> Or_unknown.t (tuple3 Rebuilt_expr.t bool Name_occurrences.t) -> M t.
Extract Inlined Constant add_non_inlinable_continuation => "Upwards_env.add_non_inlinable_continuation".
(* upwards_env.mli:44  val add_invalid_continuation : t -> Continuation.t -> [`Unarized] Flambda_arity.t -> t *)
Parameter add_invalid_continuation : t -> Continuation.t -> Flambda_arity.t_Unarized -> M t.
Extract Inlined Constant add_invalid_continuation => "Upwards_env.add_invalid_continuation".
(* upwards_env.mli:47  val add_continuation_shortcut : t -> Continuation.t -> params:Bound_parameters.t -> shortcut_to:Continuation.t -> args:Simple.t list -> t *)
Parameter add_continuation_shortcut : t -> Continuation.t -> Bound_parameters.t -> Continuation.t -> list Simple.t -> M t.
Extract Inlined Constant add_continuation_shortcut => "Upwards_env.add_continuation_shortcut".
(* upwards_env.mli:55  val add_linearly_used_inlinable_continuation : t -> Continuation.t -> params:Bound_parameters.t -> handler:Rebuilt_expr.t -> free_names_of_handler:Name_occurrences.t -> cost_metrics_of_handler:Cost_metrics.t -> t *)
Parameter add_linearly_used_inlinable_continuation : t -> Continuation.t -> Bound_parameters.t -> Rebuilt_expr.t -> Name_occurrences.t -> Cost_metrics.t -> M t.
Extract Inlined Constant add_linearly_used_inlinable_continuation => "Upwards_env.add_linearly_used_inlinable_continuation".
(* upwards_env.mli:64  val add_function_return_or_exn_continuation : t -> Continuation.t -> is_cold:bool -> [`Unarized] Flambda_arity.t -> t *)
Parameter add_function_return_or_exn_continuation : t -> Continuation.t -> bool -> Flambda_arity.t_Unarized -> M t.
Extract Inlined Constant add_function_return_or_exn_continuation => "Upwards_env.add_function_return_or_exn_continuation".
(* upwards_env.mli:67  val find_continuation : t -> Continuation.t -> Continuation_in_env.t *)
Parameter find_continuation : t -> Continuation.t -> M Continuation_in_env.t.
Extract Inlined Constant find_continuation => "Upwards_env.find_continuation".
(* upwards_env.mli:69  val mem_continuation : t -> Continuation.t -> bool *)
Parameter mem_continuation : t -> Continuation.t -> M bool.
Extract Inlined Constant mem_continuation => "Upwards_env.mem_continuation".
(* upwards_env.mli:71  val is_cold_continuation : t -> Continuation.t -> bool *)
Parameter is_cold_continuation : t -> Continuation.t -> M bool.
Extract Inlined Constant is_cold_continuation => "Upwards_env.is_cold_continuation".
(* upwards_env.mli:73  val find_continuation_shortcut : t -> Continuation.t -> Continuation_shortcut.t option *)
Parameter find_continuation_shortcut : t -> Continuation.t -> M (option Continuation_shortcut.t).
Extract Inlined Constant find_continuation_shortcut => "Upwards_env.find_continuation_shortcut".
(* upwards_env.mli:86  val find_unique_continuation_handler : Are_rebuilding_terms.t -> t -> params:Bound_parameters.t -> handler:Rebuilt_expr.t -> is_exn_handler:bool -> free_names_without_params:Name_occurrences.t -> (Continuation.t * Simple.t list) option *)
Parameter find_unique_continuation_handler : Are_rebuilding_terms.t -> t -> Bound_parameters.t -> Rebuilt_expr.t -> bool -> Name_occurrences.t -> M (option (Continuation.t * list Simple.t)).
Extract Inlined Constant find_unique_continuation_handler => "Upwards_env.find_unique_continuation_handler".
(* upwards_env.mli:95  val add_apply_cont_rewrite : t -> Continuation.t -> Apply_cont_rewrite.t -> t *)
Parameter add_apply_cont_rewrite : t -> Continuation.t -> Apply_cont_rewrite.t -> M t.
Extract Inlined Constant add_apply_cont_rewrite => "Upwards_env.add_apply_cont_rewrite".
(* upwards_env.mli:97  val replace_apply_cont_rewrite : t -> Continuation.t -> Apply_cont_rewrite.t -> t *)
Parameter replace_apply_cont_rewrite : t -> Continuation.t -> Apply_cont_rewrite.t -> M t.
Extract Inlined Constant replace_apply_cont_rewrite => "Upwards_env.replace_apply_cont_rewrite".
(* upwards_env.mli:100  val find_apply_cont_rewrite : t -> Continuation.t -> Apply_cont_rewrite.t option *)
Parameter find_apply_cont_rewrite : t -> Continuation.t -> M (option Apply_cont_rewrite.t).
Extract Inlined Constant find_apply_cont_rewrite => "Upwards_env.find_apply_cont_rewrite".
