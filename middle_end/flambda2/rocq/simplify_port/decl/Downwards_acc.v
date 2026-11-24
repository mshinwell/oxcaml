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
   Simplify uses of the compiler's module [Downwards_acc], after its interface
   middle_end/flambda2/simplify/env/downwards_acc.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Are_lifting_conts Are_rebuilding_terms Bound_var Code_id Continuation Continuation_use_kind Continuation_uses_env Debuginfo Downwards_env Flambda2_types Flambda_arity Flow Format Lifted_constant_state Name_occurrences Original_handlers Simple Slot_offsets Static_const Symbol Value_slot.

(* downwards_acc.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Downwards_acc.t".
(* downwards_acc.mli:20  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Downwards_acc.print".
(* downwards_acc.mli:23  val create : Downwards_env.t -> Slot_offsets.t Code_id.Map.t -> Continuation_uses_env.t -> t *)
Parameter create : Downwards_env.t -> Code_id.Map.t Slot_offsets.t -> Continuation_uses_env.t -> M t.
Extract Inlined Constant create => "Downwards_acc.create".
(* downwards_acc.mli:30  val denv : t -> Downwards_env.t *)
Parameter denv : t -> M Downwards_env.t.
Extract Inlined Constant denv => "Downwards_acc.denv".
(* downwards_acc.mli:33  val map_denv : t -> f:(Downwards_env.t -> Downwards_env.t) -> t *)
Parameter map_denv : t -> (Downwards_env.t -> M Downwards_env.t) -> M t.
Extract Inlined Constant map_denv => "Downwards_acc.map_denv".
(* downwards_acc.mli:36  val with_denv : t -> Downwards_env.t -> t *)
Parameter with_denv : t -> Downwards_env.t -> M t.
Extract Inlined Constant with_denv => "Downwards_acc.with_denv".
(* downwards_acc.mli:39  val flow_acc : t -> Flow.Acc.t *)
Parameter flow_acc : t -> M Flow.Acc.t.
Extract Inlined Constant flow_acc => "Downwards_acc.flow_acc".
(* downwards_acc.mli:42  val with_flow_acc : Flow.Acc.t -> t -> t *)
Parameter with_flow_acc : Flow.Acc.t -> t -> M t.
Extract Inlined Constant with_flow_acc => "Downwards_acc.with_flow_acc".
(* downwards_acc.mli:45  val map_flow_acc : t -> f:(Flow.Acc.t -> Flow.Acc.t) -> t *)
Parameter map_flow_acc : t -> (Flow.Acc.t -> M Flow.Acc.t) -> M t.
Extract Inlined Constant map_flow_acc => "Downwards_acc.map_flow_acc".
(* downwards_acc.mli:47  include Continuation_uses_env_intf.S with type t := t *)
Parameter record_continuation : t -> Continuation.t -> Flambda_arity.t -> M t.
Extract Inlined Constant record_continuation => "Downwards_acc.record_continuation".
(* downwards_acc.mli:47  include Continuation_uses_env_intf.S with type t := t *)
Parameter record_continuation_use : t -> Continuation.t -> Continuation_use_kind.t -> Downwards_env.t -> list Flambda2_types.t -> M (t * Apply_cont_rewrite_id.t).
Extract Inlined Constant record_continuation_use => "Downwards_acc.record_continuation_use".
(* downwards_acc.mli:47  include Continuation_uses_env_intf.S with type t := t *)
Parameter delete_continuation_uses : t -> Continuation.t -> M t.
Extract Inlined Constant delete_continuation_uses => "Downwards_acc.delete_continuation_uses".
(* downwards_acc.mli:47  include Continuation_uses_env_intf.S with type t := t *)
Parameter get_typing_env_no_more_than_one_use : t -> Continuation.t -> M (option Flambda2_types.Typing_env.t).
Extract Inlined Constant get_typing_env_no_more_than_one_use => "Downwards_acc.get_typing_env_no_more_than_one_use".
(* downwards_acc.mli:47  include Continuation_uses_env_intf.S with type t := t *)
Parameter num_continuation_uses : t -> Continuation.t -> M int.
Extract Inlined Constant num_continuation_uses => "Downwards_acc.num_continuation_uses".
(* downwards_acc.mli:47  include Continuation_uses_env_intf.S with type t := t *)
Parameter all_continuations_used : t -> M Continuation.Set_.t.
Extract Inlined Constant all_continuations_used => "Downwards_acc.all_continuations_used".
(* downwards_acc.mli:49  val continuation_uses_env : t -> Continuation_uses_env.t *)
Parameter continuation_uses_env : t -> M Continuation_uses_env.t.
Extract Inlined Constant continuation_uses_env => "Downwards_acc.continuation_uses_env".
(* downwards_acc.mli:51  val with_continuation_uses_env : t -> cont_uses_env:Continuation_uses_env.t -> t *)
Parameter with_continuation_uses_env : t -> Continuation_uses_env.t -> M t.
Extract Inlined Constant with_continuation_uses_env => "Downwards_acc.with_continuation_uses_env".
(* downwards_acc.mli:55  val demote_exn_handler : t -> Continuation.t -> t *)
Parameter demote_exn_handler : t -> Continuation.t -> M t.
Extract Inlined Constant demote_exn_handler => "Downwards_acc.demote_exn_handler".
(* downwards_acc.mli:57  val demoted_exn_handlers : t -> Continuation.Set.t *)
Parameter demoted_exn_handlers : t -> M Continuation.Set_.t.
Extract Inlined Constant demoted_exn_handlers => "Downwards_acc.demoted_exn_handlers".
(* downwards_acc.mli:59  val code_age_relation : t -> Code_age_relation.t *)
Parameter code_age_relation : t -> M Flambda2_types.Code_age_relation.t.
Extract Inlined Constant code_age_relation => "Downwards_acc.code_age_relation".
(* downwards_acc.mli:61  val with_code_age_relation : t -> code_age_relation:Code_age_relation.t -> t *)
Parameter with_code_age_relation : t -> Flambda2_types.Code_age_relation.t -> M t.
Extract Inlined Constant with_code_age_relation => "Downwards_acc.with_code_age_relation".
(* downwards_acc.mli:63  val typing_env : t -> Flambda2_types.Typing_env.t *)
Parameter typing_env : t -> M Flambda2_types.Typing_env.t.
Extract Inlined Constant typing_env => "Downwards_acc.typing_env".
(* downwards_acc.mli:65  val add_variable : t -> Bound_var.t -> Flambda2_types.t -> t *)
Parameter add_variable : t -> Bound_var.t -> Flambda2_types.t -> M t.
Extract Inlined Constant add_variable => "Downwards_acc.add_variable".
(* downwards_acc.mli:67  val no_lifted_constants : t -> bool *)
Parameter no_lifted_constants : t -> M bool.
Extract Inlined Constant no_lifted_constants => "Downwards_acc.no_lifted_constants".
(* downwards_acc.mli:69  val add_to_lifted_constant_accumulator : ?also_add_to_env:unit -> t -> Lifted_constant_state.t -> t *)
Parameter add_to_lifted_constant_accumulator : option unit -> t -> Lifted_constant_state.t -> M t.
Extract Inlined Constant add_to_lifted_constant_accumulator => "(fun x__1 x__2 x__3 -> Downwards_acc.add_to_lifted_constant_accumulator ?also_add_to_env:x__1 x__2 x__3)".
(* downwards_acc.mli:72  val get_lifted_constants : t -> Lifted_constant_state.t *)
Parameter get_lifted_constants : t -> M Lifted_constant_state.t.
Extract Inlined Constant get_lifted_constants => "Downwards_acc.get_lifted_constants".
(* downwards_acc.mli:74  val get_and_clear_lifted_constants : t -> t * Lifted_constant_state.t *)
Parameter get_and_clear_lifted_constants : t -> M (t * Lifted_constant_state.t).
Extract Inlined Constant get_and_clear_lifted_constants => "Downwards_acc.get_and_clear_lifted_constants".
(* downwards_acc.mli:76  val clear_lifted_constants : t -> t *)
Parameter clear_lifted_constants : t -> M t.
Extract Inlined Constant clear_lifted_constants => "Downwards_acc.clear_lifted_constants".
(* downwards_acc.mli:78  val set_lifted_constants : t -> Lifted_constant_state.t -> t *)
Parameter set_lifted_constants : t -> Lifted_constant_state.t -> M t.
Extract Inlined Constant set_lifted_constants => "Downwards_acc.set_lifted_constants".
(* downwards_acc.mli:80  val find_shareable_constant : t -> Static_const.t -> Symbol.t option *)
Parameter find_shareable_constant : t -> Static_const.t -> M (option Symbol.t).
Extract Inlined Constant find_shareable_constant => "Downwards_acc.find_shareable_constant".
(* downwards_acc.mli:82  val consider_constant_for_sharing : t -> Symbol.t -> Static_const.t -> t *)
Parameter consider_constant_for_sharing : t -> Symbol.t -> Static_const.t -> M t.
Extract Inlined Constant consider_constant_for_sharing => "Downwards_acc.consider_constant_for_sharing".
(* downwards_acc.mli:84  val with_shareable_constants : t -> shareable_constants:Symbol.t Static_const.Map.t -> t *)
Parameter with_shareable_constants : t -> Static_const.Map.t Symbol.t -> M t.
Extract Inlined Constant with_shareable_constants => "Downwards_acc.with_shareable_constants".
(* downwards_acc.mli:87  val shareable_constants : t -> Symbol.t Static_const.Map.t *)
Parameter shareable_constants : t -> M (Static_const.Map.t Symbol.t).
Extract Inlined Constant shareable_constants => "Downwards_acc.shareable_constants".
(* downwards_acc.mli:89  val add_use_of_value_slot : t -> Value_slot.t -> t *)
Parameter add_use_of_value_slot : t -> Value_slot.t -> M t.
Extract Inlined Constant add_use_of_value_slot => "Downwards_acc.add_use_of_value_slot".
(* downwards_acc.mli:91  val used_value_slots : t -> Name_occurrences.t *)
Parameter used_value_slots : t -> M Name_occurrences.t.
Extract Inlined Constant used_value_slots => "Downwards_acc.used_value_slots".
(* downwards_acc.mli:93  val with_used_value_slots : t -> used_value_slots:Name_occurrences.t -> t *)
Parameter with_used_value_slots : t -> Name_occurrences.t -> M t.
Extract Inlined Constant with_used_value_slots => "Downwards_acc.with_used_value_slots".
(* downwards_acc.mli:95  val add_code_ids_to_remember : t -> Code_id.Set.t -> t *)
Parameter add_code_ids_to_remember : t -> Code_id.Set_.t -> M t.
Extract Inlined Constant add_code_ids_to_remember => "Downwards_acc.add_code_ids_to_remember".
(* downwards_acc.mli:97  val code_ids_to_remember : t -> Code_id.Set.t *)
Parameter code_ids_to_remember : t -> M Code_id.Set_.t.
Extract Inlined Constant code_ids_to_remember => "Downwards_acc.code_ids_to_remember".
(* downwards_acc.mli:99  val with_code_ids_to_remember : t -> code_ids_to_remember:Code_id.Set.t -> t *)
Parameter with_code_ids_to_remember : t -> Code_id.Set_.t -> M t.
Extract Inlined Constant with_code_ids_to_remember => "Downwards_acc.with_code_ids_to_remember".
(* downwards_acc.mli:101  val add_code_ids_to_never_delete : t -> Code_id.Set.t -> t *)
Parameter add_code_ids_to_never_delete : t -> Code_id.Set_.t -> M t.
Extract Inlined Constant add_code_ids_to_never_delete => "Downwards_acc.add_code_ids_to_never_delete".
(* downwards_acc.mli:103  val code_ids_to_never_delete : t -> Code_id.Set.t *)
Parameter code_ids_to_never_delete : t -> M Code_id.Set_.t.
Extract Inlined Constant code_ids_to_never_delete => "Downwards_acc.code_ids_to_never_delete".
(* downwards_acc.mli:105  val with_code_ids_to_never_delete : t -> code_ids_to_never_delete:Code_id.Set.t -> t *)
Parameter with_code_ids_to_never_delete : t -> Code_id.Set_.t -> M t.
Extract Inlined Constant with_code_ids_to_never_delete => "Downwards_acc.with_code_ids_to_never_delete".
(* downwards_acc.mli:108  val add_code_ids_never_simplified : t -> old_code_ids:Code_id.Set.t -> t *)
Parameter add_code_ids_never_simplified : t -> Code_id.Set_.t -> M t.
Extract Inlined Constant add_code_ids_never_simplified => "Downwards_acc.add_code_ids_never_simplified".
(* downwards_acc.mli:110  val code_ids_never_simplified : t -> Code_id.Set.t *)
Parameter code_ids_never_simplified : t -> M Code_id.Set_.t.
Extract Inlined Constant code_ids_never_simplified => "Downwards_acc.code_ids_never_simplified".
(* downwards_acc.mli:112  val with_code_ids_never_simplified : t -> code_ids_never_simplified:Code_id.Set.t -> t *)
Parameter with_code_ids_never_simplified : t -> Code_id.Set_.t -> M t.
Extract Inlined Constant with_code_ids_never_simplified => "Downwards_acc.with_code_ids_never_simplified".
(* downwards_acc.mli:115  val are_rebuilding_terms : t -> Are_rebuilding_terms.t *)
Parameter are_rebuilding_terms : t -> M Are_rebuilding_terms.t.
Extract Inlined Constant are_rebuilding_terms => "Downwards_acc.are_rebuilding_terms".
(* downwards_acc.mli:117  val slot_offsets : t -> Slot_offsets.t Code_id.Map.t *)
Parameter slot_offsets : t -> M (Code_id.Map.t Slot_offsets.t).
Extract Inlined Constant slot_offsets => "Downwards_acc.slot_offsets".
(* downwards_acc.mli:119  val with_slot_offsets : t -> slot_offsets:Slot_offsets.t Code_id.Map.t -> t *)
Parameter with_slot_offsets : t -> Code_id.Map.t Slot_offsets.t -> M t.
Extract Inlined Constant with_slot_offsets => "Downwards_acc.with_slot_offsets".
(* downwards_acc.mli:121  val merge_debuginfo_rewrite : t -> bound_to:Simple.t -> Debuginfo.t -> t *)
Parameter merge_debuginfo_rewrite : t -> Simple.t -> Debuginfo.t -> M t.
Extract Inlined Constant merge_debuginfo_rewrite => "Downwards_acc.merge_debuginfo_rewrite".
(* downwards_acc.mli:123  val find_debuginfo_rewrite : t -> bound_to:Simple.t -> Debuginfo.t option *)
Parameter find_debuginfo_rewrite : t -> Simple.t -> M (option Debuginfo.t).
Extract Inlined Constant find_debuginfo_rewrite => "Downwards_acc.find_debuginfo_rewrite".
(* downwards_acc.mli:125  val are_lifting_conts : t -> Are_lifting_conts.t *)
Parameter are_lifting_conts : t -> M Are_lifting_conts.t.
Extract Inlined Constant are_lifting_conts => "Downwards_acc.are_lifting_conts".
(* downwards_acc.mli:127  val with_are_lifting_conts : t -> Are_lifting_conts.t -> t *)
Parameter with_are_lifting_conts : t -> Are_lifting_conts.t -> M t.
Extract Inlined Constant with_are_lifting_conts => "Downwards_acc.with_are_lifting_conts".
(* downwards_acc.mli:129  val get_and_clear_lifted_continuations : t -> t * (Downwards_env.t * Original_handlers.t) list *)
Parameter get_and_clear_lifted_continuations : t -> M (t * list (Downwards_env.t * Original_handlers.t)).
Extract Inlined Constant get_and_clear_lifted_continuations => "Downwards_acc.get_and_clear_lifted_continuations".
(* downwards_acc.mli:132  val add_lifted_continuation : Downwards_env.t -> Original_handlers.t -> t -> t *)
Parameter add_lifted_continuation : Downwards_env.t -> Original_handlers.t -> t -> M t.
Extract Inlined Constant add_lifted_continuation => "Downwards_acc.add_lifted_continuation".
(* downwards_acc.mli:134  val get_continuation_lifting_budget : t -> int *)
Parameter get_continuation_lifting_budget : t -> M int.
Extract Inlined Constant get_continuation_lifting_budget => "Downwards_acc.get_continuation_lifting_budget".
(* downwards_acc.mli:136  val reset_continuation_lifting_budget : t -> t *)
Parameter reset_continuation_lifting_budget : t -> M t.
Extract Inlined Constant reset_continuation_lifting_budget => "Downwards_acc.reset_continuation_lifting_budget".
(* downwards_acc.mli:138  val with_continuation_lifting_budget : t -> int -> t *)
Parameter with_continuation_lifting_budget : t -> int -> M t.
Extract Inlined Constant with_continuation_lifting_budget => "Downwards_acc.with_continuation_lifting_budget".
(* downwards_acc.mli:140  val decrease_continuation_lifting_budget : t -> int -> t *)
Parameter decrease_continuation_lifting_budget : t -> int -> M t.
Extract Inlined Constant decrease_continuation_lifting_budget => "Downwards_acc.decrease_continuation_lifting_budget".
(* downwards_acc.mli:142  val prepare_for_speculative_inlining : t -> t *)
Parameter prepare_for_speculative_inlining : t -> M t.
Extract Inlined Constant prepare_for_speculative_inlining => "Downwards_acc.prepare_for_speculative_inlining".
(* downwards_acc.mli:144  val continuations_to_specialize : t -> Continuation.Set.t *)
Parameter continuations_to_specialize : t -> M Continuation.Set_.t.
Extract Inlined Constant continuations_to_specialize => "Downwards_acc.continuations_to_specialize".
(* downwards_acc.mli:146  val add_continuation_to_specialize : t -> Continuation.t -> t *)
Parameter add_continuation_to_specialize : t -> Continuation.t -> M t.
Extract Inlined Constant add_continuation_to_specialize => "Downwards_acc.add_continuation_to_specialize".
(* downwards_acc.mli:148  val specialization_map : t -> Continuation.t Apply_cont_rewrite_id.Map.t Continuation.Map.t *)
Parameter specialization_map : t -> M (Continuation.Map.t (Apply_cont_rewrite_id.Map.t Continuation.t)).
Extract Inlined Constant specialization_map => "Downwards_acc.specialization_map".
(* downwards_acc.mli:151  val add_specialization : t -> Apply_cont_rewrite_id.t -> old:Continuation.t -> specialized:Continuation.t -> t *)
Parameter add_specialization : t -> Apply_cont_rewrite_id.t -> Continuation.t -> Continuation.t -> M t.
Extract Inlined Constant add_specialization => "Downwards_acc.add_specialization".
