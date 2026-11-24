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
   Simplify uses of the compiler's module [Upwards_acc], after its interface
   middle_end/flambda2/simplify/env/upwards_acc.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Are_rebuilding_terms Code Code_id Code_size Continuation Continuation_callsite_map Cost_metrics Downwards_acc Exported_code Flambda2_types Flow_types Format Lifted_constant Lifted_constant_state Name Name_occurrences Or_unknown Removed_operations Slot_offsets Static_const Symbol Upwards_env.

(* upwards_acc.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Upwards_acc.t".
(* upwards_acc.mli:20  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Upwards_acc.print".
(* upwards_acc.mli:22  val create : flow_result:Flow_types.Flow_result.t -> compute_slot_offsets:bool -> Upwards_env.t -> Downwards_acc.t -> t *)
Parameter create : Flow_types.Flow_result.t -> bool -> Upwards_env.t -> Downwards_acc.t -> M t.
Extract Inlined Constant create => "Upwards_acc.create".
(* upwards_acc.mli:29  val creation_dacc : t -> Downwards_acc.t *)
Parameter creation_dacc : t -> M Downwards_acc.t.
Extract Inlined Constant creation_dacc => "Upwards_acc.creation_dacc".
(* upwards_acc.mli:32  val uenv : t -> Upwards_env.t *)
Parameter uenv : t -> M Upwards_env.t.
Extract Inlined Constant uenv => "Upwards_acc.uenv".
(* upwards_acc.mli:34  val cost_metrics : t -> Cost_metrics.t *)
Parameter cost_metrics : t -> M Cost_metrics.t.
Extract Inlined Constant cost_metrics => "Upwards_acc.cost_metrics".
(* upwards_acc.mli:36  val code_age_relation : t -> Code_age_relation.t *)
Parameter code_age_relation : t -> M Flambda2_types.Code_age_relation.t.
Extract Inlined Constant code_age_relation => "Upwards_acc.code_age_relation".
(* upwards_acc.mli:40  val lifted_constants : t -> Lifted_constant_state.t *)
Parameter lifted_constants : t -> M Lifted_constant_state.t.
Extract Inlined Constant lifted_constants => "Upwards_acc.lifted_constants".
(* upwards_acc.mli:42  val get_and_clear_lifted_constants : t -> t * Lifted_constant_state.t *)
Parameter get_and_clear_lifted_constants : t -> M (t * Lifted_constant_state.t).
Extract Inlined Constant get_and_clear_lifted_constants => "Upwards_acc.get_and_clear_lifted_constants".
(* upwards_acc.mli:45  val with_lifted_constants : t -> Lifted_constant_state.t -> t *)
Parameter with_lifted_constants : t -> Lifted_constant_state.t -> M t.
Extract Inlined Constant with_lifted_constants => "Upwards_acc.with_lifted_constants".
(* upwards_acc.mli:47  val no_lifted_constants : t -> bool *)
Parameter no_lifted_constants : t -> M bool.
Extract Inlined Constant no_lifted_constants => "Upwards_acc.no_lifted_constants".
(* upwards_acc.mli:49  val add_lifted_constant : t -> Lifted_constant.t -> t *)
Parameter add_lifted_constant : t -> Lifted_constant.t -> M t.
Extract Inlined Constant add_lifted_constant => "Upwards_acc.add_lifted_constant".
(* upwards_acc.mli:52  val map_uenv : t -> f:(Upwards_env.t -> Upwards_env.t) -> t *)
Parameter map_uenv : t -> (Upwards_env.t -> M Upwards_env.t) -> M t.
Extract Inlined Constant map_uenv => "Upwards_acc.map_uenv".
(* upwards_acc.mli:55  val with_uenv : t -> Upwards_env.t -> t *)
Parameter with_uenv : t -> Upwards_env.t -> M t.
Extract Inlined Constant with_uenv => "Upwards_acc.with_uenv".
(* upwards_acc.mli:57  val remember_code_for_cmx : t -> Code.t Code_id.Map.t -> t *)
Parameter remember_code_for_cmx : t -> Code_id.Map.t Code.t -> M t.
Extract Inlined Constant remember_code_for_cmx => "Upwards_acc.remember_code_for_cmx".
(* upwards_acc.mli:59  val all_code : t -> Exported_code.t *)
Parameter all_code : t -> M Exported_code.t.
Extract Inlined Constant all_code => "Upwards_acc.all_code".
(* upwards_acc.mli:61  val shareable_constants : t -> Symbol.t Static_const.Map.t *)
Parameter shareable_constants : t -> M (Static_const.Map.t Symbol.t).
Extract Inlined Constant shareable_constants => "Upwards_acc.shareable_constants".
(* upwards_acc.mli:63  val name_occurrences : t -> Name_occurrences.t *)
Parameter name_occurrences : t -> M Name_occurrences.t.
Extract Inlined Constant name_occurrences => "Upwards_acc.name_occurrences".
(* upwards_acc.mli:65  val with_name_occurrences : t -> name_occurrences:Name_occurrences.t -> t *)
Parameter with_name_occurrences : t -> Name_occurrences.t -> M t.
Extract Inlined Constant with_name_occurrences => "Upwards_acc.with_name_occurrences".
(* upwards_acc.mli:67  val clear_name_occurrences : t -> t *)
Parameter clear_name_occurrences : t -> M t.
Extract Inlined Constant clear_name_occurrences => "Upwards_acc.clear_name_occurrences".
(* upwards_acc.mli:69  val add_free_names : t -> Name_occurrences.t -> t *)
Parameter add_free_names : t -> Name_occurrences.t -> M t.
Extract Inlined Constant add_free_names => "Upwards_acc.add_free_names".
(* upwards_acc.mli:72  val used_value_slots : t -> Name_occurrences.t *)
Parameter used_value_slots : t -> M Name_occurrences.t.
Extract Inlined Constant used_value_slots => "Upwards_acc.used_value_slots".
(* upwards_acc.mli:74  val remove_all_occurrences_of_free_names : t -> Name_occurrences.t -> t *)
Parameter remove_all_occurrences_of_free_names : t -> Name_occurrences.t -> M t.
Extract Inlined Constant remove_all_occurrences_of_free_names => "Upwards_acc.remove_all_occurrences_of_free_names".
(* upwards_acc.mli:76  val clear_cost_metrics : t -> t *)
Parameter clear_cost_metrics : t -> M t.
Extract Inlined Constant clear_cost_metrics => "Upwards_acc.clear_cost_metrics".
(* upwards_acc.mli:78  val with_cost_metrics : Cost_metrics.t -> t -> t *)
Parameter with_cost_metrics : Cost_metrics.t -> t -> M t.
Extract Inlined Constant with_cost_metrics => "Upwards_acc.with_cost_metrics".
(* upwards_acc.mli:80  val add_cost_metrics : Cost_metrics.t -> t -> t *)
Parameter add_cost_metrics : Cost_metrics.t -> t -> M t.
Extract Inlined Constant add_cost_metrics => "Upwards_acc.add_cost_metrics".
(* upwards_acc.mli:86  val add_cost_metrics_and_with_name_occurrences : t -> Cost_metrics.t -> Name_occurrences.t -> t *)
Parameter add_cost_metrics_and_with_name_occurrences : t -> Cost_metrics.t -> Name_occurrences.t -> M t.
Extract Inlined Constant add_cost_metrics_and_with_name_occurrences => "Upwards_acc.add_cost_metrics_and_with_name_occurrences".
(* upwards_acc.mli:89  val notify_added : code_size:Code_size.t -> t -> t *)
Parameter notify_added : Code_size.t -> t -> M t.
Extract Inlined Constant notify_added => "Upwards_acc.notify_added".
(* upwards_acc.mli:91  val notify_removed : operation:Removed_operations.t -> t -> t *)
Parameter notify_removed : Removed_operations.t -> t -> M t.
Extract Inlined Constant notify_removed => "Upwards_acc.notify_removed".
(* upwards_acc.mli:93  val generate_phantom_lets : t -> bool *)
Parameter generate_phantom_lets : t -> M bool.
Extract Inlined Constant generate_phantom_lets => "Upwards_acc.generate_phantom_lets".
(* upwards_acc.mli:95  val are_rebuilding_terms : t -> Are_rebuilding_terms.t *)
Parameter are_rebuilding_terms : t -> M Are_rebuilding_terms.t.
Extract Inlined Constant are_rebuilding_terms => "Upwards_acc.are_rebuilding_terms".
(* upwards_acc.mli:97  val is_demoted_exn_handler : t -> Continuation.t -> bool *)
Parameter is_demoted_exn_handler : t -> Continuation.t -> M bool.
Extract Inlined Constant is_demoted_exn_handler => "Upwards_acc.is_demoted_exn_handler".
(* upwards_acc.mli:99  val slot_offsets : t -> Slot_offsets.t Or_unknown.t *)
Parameter slot_offsets : t -> M (Or_unknown.t Slot_offsets.t).
Extract Inlined Constant slot_offsets => "Upwards_acc.slot_offsets".
(* upwards_acc.mli:101  val with_slot_offsets : t -> Slot_offsets.t Or_unknown.t -> t *)
Parameter with_slot_offsets : t -> Or_unknown.t Slot_offsets.t -> M t.
Extract Inlined Constant with_slot_offsets => "Upwards_acc.with_slot_offsets".
(* upwards_acc.mli:105  val required_names : t -> Name.Set.t *)
Parameter required_names : t -> M Name.Set_.t.
Extract Inlined Constant required_names => "Upwards_acc.required_names".
(* upwards_acc.mli:107  val reachable_code_ids : t -> Flow_types.Reachable_code_ids.t Or_unknown.t *)
Parameter reachable_code_ids : t -> M (Or_unknown.t Flow_types.Reachable_code_ids.t).
Extract Inlined Constant reachable_code_ids => "Upwards_acc.reachable_code_ids".
(* upwards_acc.mli:109  val continuation_param_aliases : t -> Flow_types.Alias_result.t *)
Parameter continuation_param_aliases : t -> M Flow_types.Alias_result.t.
Extract Inlined Constant continuation_param_aliases => "Upwards_acc.continuation_param_aliases".
(* upwards_acc.mli:111  val mutable_unboxing_result : t -> Flow_types.Mutable_unboxing_result.t *)
Parameter mutable_unboxing_result : t -> M Flow_types.Mutable_unboxing_result.t.
Extract Inlined Constant mutable_unboxing_result => "Upwards_acc.mutable_unboxing_result".
(* upwards_acc.mli:113  val set_resimplify : t -> t *)
Parameter set_resimplify : t -> M t.
Extract Inlined Constant set_resimplify => "Upwards_acc.set_resimplify".
(* upwards_acc.mli:115  val resimplify : t -> bool *)
Parameter resimplify : t -> M bool.
Extract Inlined Constant resimplify => "Upwards_acc.resimplify".
(* upwards_acc.mli:117  val specialization_map : t -> Continuation.t Continuation_callsite_map.t *)
Parameter specialization_map : t -> M (Continuation_callsite_map.t Continuation.t).
Extract Inlined Constant specialization_map => "Upwards_acc.specialization_map".
