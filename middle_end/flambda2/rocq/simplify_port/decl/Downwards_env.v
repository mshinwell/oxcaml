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
   Simplify uses of the compiler's module [Downwards_env], after its interface
   middle_end/flambda2/simplify/env/downwards_env.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Apply_cont_rewrite_id Apply_expr Are_rebuilding_terms Bound_name Bound_parameters Bound_var Call_site_inlining_decision_type Closure_info Code Code_id Code_metadata Code_or_metadata Common_subexpression_elimination Comparison_result Compilation_unit Continuation Debuginfo Exported_code Flambda Flambda2_types Flambda_kind Flambda_primitive Format Inlined_attribute Inlined_debuginfo Inlining_arguments Inlining_history Inlining_state Lifted_constant_state Lifted_cont_params Loopify_state Name Name_mode Replay_history Scope Simple Specialization_cost Symbol Symbol_projection Target_system Variable_.

(* downwards_env.mli:19  type resolver = Compilation_unit.t -> Flambda2_types.Typing_env.Serializable.t option *)
Definition resolver_ : Type := Compilation_unit.t -> M (option Flambda2_types.Typing_env.Serializable.t).
Extract Inlined Constant resolver_ => "Downwards_env.resolver".
(* downwards_env.mli:22  type get_imported_code = unit -> Exported_code.t *)
Definition get_imported_code : Type := unit -> M Exported_code.t.
Extract Inlined Constant get_imported_code => "Downwards_env.get_imported_code".
(* downwards_env.mli:24  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Downwards_env.t".
(* downwards_env.mli:27  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Downwards_env.print".
(* downwards_env.mli:31  val create : round:int -> machine_width:Target_system.Machine_width.t -> resolver:resolver -> get_imported_code:get_imported_code -> propagating_float_consts:bool -> unit_toplevel_exn_continuation:Continuation.t -> unit_toplevel_return_continuation:Continuation.t -> toplevel_my_alloc_region:Variable.t -> t *)
Parameter create : int -> Target_system.Machine_width.t -> resolver_ -> get_imported_code -> bool -> Continuation.t -> Continuation.t -> Variable_.t -> M t.
Extract Inlined Constant create => "Downwards_env.create".
(* downwards_env.mli:42  val all_code : t -> Code.t Code_id.Map.t *)
Parameter all_code : t -> M (Code_id.Map.t Code.t).
Extract Inlined Constant all_code => "Downwards_env.all_code".
(* downwards_env.mli:44  val machine_width : t -> Target_system.Machine_width.t *)
Parameter machine_width : t -> M Target_system.Machine_width.t.
Extract Inlined Constant machine_width => "Downwards_env.machine_width".
(* downwards_env.mli:46  val resolver : t -> Compilation_unit.t -> Flambda2_types.Typing_env.Serializable.t option *)
Parameter resolver : t -> Compilation_unit.t -> M (option Flambda2_types.Typing_env.Serializable.t).
Extract Inlined Constant resolver => "Downwards_env.resolver".
(* downwards_env.mli:49  val propagating_float_consts : t -> bool *)
Parameter propagating_float_consts : t -> M bool.
Extract Inlined Constant propagating_float_consts => "Downwards_env.propagating_float_consts".
(* downwards_env.mli:51  val at_unit_toplevel : t -> bool *)
Parameter at_unit_toplevel : t -> M bool.
Extract Inlined Constant at_unit_toplevel => "Downwards_env.at_unit_toplevel".
(* downwards_env.mli:53  val set_at_unit_toplevel_state : t -> bool -> t *)
Parameter set_at_unit_toplevel_state : t -> bool -> M t.
Extract Inlined Constant set_at_unit_toplevel_state => "Downwards_env.set_at_unit_toplevel_state".
(* downwards_env.mli:55  val is_defined_at_toplevel : t -> Variable.t -> bool *)
Parameter is_defined_at_toplevel : t -> Variable_.t -> M bool.
Extract Inlined Constant is_defined_at_toplevel => "Downwards_env.is_defined_at_toplevel".
(* downwards_env.mli:57  val add_symbol_projection : t -> Variable.t -> Symbol_projection.t -> t *)
Parameter add_symbol_projection : t -> Variable_.t -> Symbol_projection.t -> M t.
Extract Inlined Constant add_symbol_projection => "Downwards_env.add_symbol_projection".
(* downwards_env.mli:59  val find_symbol_projection : t -> Variable.t -> Symbol_projection.t option *)
Parameter find_symbol_projection : t -> Variable_.t -> M (option Symbol_projection.t).
Extract Inlined Constant find_symbol_projection => "Downwards_env.find_symbol_projection".
(* downwards_env.mli:61  val unit_toplevel_return_continuation : t -> Continuation.t *)
Parameter unit_toplevel_return_continuation : t -> M Continuation.t.
Extract Inlined Constant unit_toplevel_return_continuation => "Downwards_env.unit_toplevel_return_continuation".
(* downwards_env.mli:63  val unit_toplevel_exn_continuation : t -> Continuation.t *)
Parameter unit_toplevel_exn_continuation : t -> M Continuation.t.
Extract Inlined Constant unit_toplevel_exn_continuation => "Downwards_env.unit_toplevel_exn_continuation".
(* downwards_env.mli:65  val unit_toplevel_alloc_region : t -> Variable.t *)
Parameter unit_toplevel_alloc_region : t -> M Variable_.t.
Extract Inlined Constant unit_toplevel_alloc_region => "Downwards_env.unit_toplevel_alloc_region".
(* downwards_env.mli:67  val increment_continuation_scope : t -> t *)
Parameter increment_continuation_scope : t -> M t.
Extract Inlined Constant increment_continuation_scope => "Downwards_env.increment_continuation_scope".
(* downwards_env.mli:69  val bump_current_level_scope : t -> t *)
Parameter bump_current_level_scope : t -> M t.
Extract Inlined Constant bump_current_level_scope => "Downwards_env.bump_current_level_scope".
(* downwards_env.mli:71  val get_continuation_scope : t -> Scope.t *)
Parameter get_continuation_scope : t -> M Scope.t.
Extract Inlined Constant get_continuation_scope => "Downwards_env.get_continuation_scope".
(* downwards_env.mli:73  val typing_env : t -> Flambda2_types.Typing_env.t *)
Parameter typing_env : t -> M Flambda2_types.Typing_env.t.
Extract Inlined Constant typing_env => "Downwards_env.typing_env".
(* downwards_env.mli:75  val define_continuations : can_be_lifted:bool -> t -> Continuation.t list -> t *)
Parameter define_continuations : bool -> t -> list Continuation.t -> M t.
Extract Inlined Constant define_continuations => "Downwards_env.define_continuations".
(* downwards_env.mli:77  val define_variable : t -> Bound_var.t -> Flambda_kind.t -> t *)
Parameter define_variable : t -> Bound_var.t -> Flambda_kind.t -> M t.
Extract Inlined Constant define_variable => "Downwards_env.define_variable".
(* downwards_env.mli:79  val define_extra_variable : t -> Bound_var.t -> Flambda_kind.t -> t *)
Parameter define_extra_variable : t -> Bound_var.t -> Flambda_kind.t -> M t.
Extract Inlined Constant define_extra_variable => "Downwards_env.define_extra_variable".
(* downwards_env.mli:81  val add_name : t -> Bound_name.t -> Flambda2_types.t -> t *)
Parameter add_name : t -> Bound_name.t -> Flambda2_types.t -> M t.
Extract Inlined Constant add_name => "Downwards_env.add_name".
(* downwards_env.mli:83  val add_variable : t -> Bound_var.t -> Flambda2_types.t -> t *)
Parameter add_variable : t -> Bound_var.t -> Flambda2_types.t -> M t.
Extract Inlined Constant add_variable => "Downwards_env.add_variable".
(* downwards_env.mli:85  val add_equation_on_variable : t -> Variable.t -> Flambda2_types.t -> t *)
Parameter add_equation_on_variable : t -> Variable_.t -> Flambda2_types.t -> M t.
Extract Inlined Constant add_equation_on_variable => "Downwards_env.add_equation_on_variable".
(* downwards_env.mli:87  val mem_variable : t -> Variable.t -> bool *)
Parameter mem_variable : t -> Variable_.t -> M bool.
Extract Inlined Constant mem_variable => "Downwards_env.mem_variable".
(* downwards_env.mli:89  val add_symbol : t -> Symbol.t -> Flambda2_types.t -> t *)
Parameter add_symbol : t -> Symbol.t -> Flambda2_types.t -> M t.
Extract Inlined Constant add_symbol => "Downwards_env.add_symbol".
(* downwards_env.mli:91  val define_symbol : t -> Symbol.t -> Flambda_kind.t -> t *)
Parameter define_symbol : t -> Symbol.t -> Flambda_kind.t -> M t.
Extract Inlined Constant define_symbol => "Downwards_env.define_symbol".
(* downwards_env.mli:93  val mem_symbol : t -> Symbol.t -> bool *)
Parameter mem_symbol : t -> Symbol.t -> M bool.
Extract Inlined Constant mem_symbol => "Downwards_env.mem_symbol".
(* downwards_env.mli:95  val find_symbol : t -> Symbol.t -> Flambda2_types.t *)
Parameter find_symbol : t -> Symbol.t -> M Flambda2_types.t.
Extract Inlined Constant find_symbol => "Downwards_env.find_symbol".
(* downwards_env.mli:97  val add_equation_on_symbol : t -> Symbol.t -> Flambda2_types.t -> t *)
Parameter add_equation_on_symbol : t -> Symbol.t -> Flambda2_types.t -> M t.
Extract Inlined Constant add_equation_on_symbol => "Downwards_env.add_equation_on_symbol".
(* downwards_env.mli:99  val define_name : t -> Bound_name.t -> Flambda_kind.t -> t *)
Parameter define_name : t -> Bound_name.t -> Flambda_kind.t -> M t.
Extract Inlined Constant define_name => "Downwards_env.define_name".
(* downwards_env.mli:101  val define_name_if_undefined : t -> Bound_name.t -> Flambda_kind.t -> t *)
Parameter define_name_if_undefined : t -> Bound_name.t -> Flambda_kind.t -> M t.
Extract Inlined Constant define_name_if_undefined => "Downwards_env.define_name_if_undefined".
(* downwards_env.mli:103  val add_equation_on_name : t -> Name.t -> Flambda2_types.t -> t *)
Parameter add_equation_on_name : t -> Name.t -> Flambda2_types.t -> M t.
Extract Inlined Constant add_equation_on_name => "Downwards_env.add_equation_on_name".
(* downwards_env.mli:105  val define_parameters : extra:bool -> t -> params:Bound_parameters.t -> t *)
Parameter define_parameters : bool -> t -> Bound_parameters.t -> M t.
Extract Inlined Constant define_parameters => "Downwards_env.define_parameters".
(* downwards_env.mli:107  val add_parameters : extra:bool -> ?name_mode:Name_mode.t -> t -> Bound_parameters.t -> param_types:Flambda2_types.t list -> t *)
Parameter add_parameters : bool -> option Name_mode.t -> t -> Bound_parameters.t -> list Flambda2_types.t -> M t.
Extract Inlined Constant add_parameters => "(fun x__1 x__2 x__3 x__4 x__5 -> Downwards_env.add_parameters x__1 ?name_mode:x__2 x__3 x__4 x__5)".
(* downwards_env.mli:115  val add_parameters_with_unknown_types : extra:bool -> ?alloc_modes:Alloc_mode.For_types.t list -> ?name_mode:Name_mode.t -> t -> Bound_parameters.t -> t *)
Parameter add_parameters_with_unknown_types : bool -> option (list Alloc_mode.For_types.t) -> option Name_mode.t -> t -> Bound_parameters.t -> M t.
Extract Inlined Constant add_parameters_with_unknown_types => "(fun x__1 x__2 x__3 x__4 x__5 -> Downwards_env.add_parameters_with_unknown_types x__1 ?alloc_modes:x__2 ?name_mode:x__3 x__4 x__5)".
(* downwards_env.mli:123  val mark_parameters_as_toplevel : t -> Bound_parameters.t -> t *)
Parameter mark_parameters_as_toplevel : t -> Bound_parameters.t -> M t.
Extract Inlined Constant mark_parameters_as_toplevel => "Downwards_env.mark_parameters_as_toplevel".
(* downwards_env.mli:125  val extend_typing_environment : t -> Flambda2_types.Typing_env_extension.With_extra_variables.t -> t *)
Parameter extend_typing_environment : t -> Flambda2_types.Typing_env_extension.With_extra_variables.t -> M t.
Extract Inlined Constant extend_typing_environment => "Downwards_env.extend_typing_environment".
(* downwards_env.mli:128  val with_typing_env : t -> Flambda2_types.Typing_env.t -> t *)
Parameter with_typing_env : t -> Flambda2_types.Typing_env.t -> M t.
Extract Inlined Constant with_typing_env => "Downwards_env.with_typing_env".
(* downwards_env.mli:130  val map_typing_env : t -> f:(Flambda2_types.Typing_env.t -> Flambda2_types.Typing_env.t) -> t *)
Parameter map_typing_env : t -> (Flambda2_types.Typing_env.t -> M Flambda2_types.Typing_env.t) -> M t.
Extract Inlined Constant map_typing_env => "Downwards_env.map_typing_env".
(* downwards_env.mli:133  val check_simple_is_bound : t -> Simple.t -> unit *)
Parameter check_simple_is_bound : t -> Simple.t -> M unit.
Extract Inlined Constant check_simple_is_bound => "Downwards_env.check_simple_is_bound".
(* downwards_env.mli:135  val define_code : t -> code_id:Code_id.t -> code:Code.t -> t *)
Parameter define_code : t -> Code_id.t -> Code.t -> M t.
Extract Inlined Constant define_code => "Downwards_env.define_code".
(* downwards_env.mli:137  val mem_code : t -> Code_id.t -> bool *)
Parameter mem_code : t -> Code_id.t -> M bool.
Extract Inlined Constant mem_code => "Downwards_env.mem_code".
(* downwards_env.mli:140  val find_code_exn : t -> Code_id.t -> Code_or_metadata.t *)
Parameter find_code_exn : t -> Code_id.t -> M Code_or_metadata.t.
Extract Inlined Constant find_code_exn => "Downwards_env.find_code_exn".
(* downwards_env.mli:143  val find_code_metadata_exn : t -> Code_id.t -> Code_metadata.t *)
Parameter find_code_metadata_exn : t -> Code_id.t -> M Code_metadata.t.
Extract Inlined Constant find_code_metadata_exn => "Downwards_env.find_code_metadata_exn".
(* downwards_env.mli:145  val set_inlined_debuginfo : t -> from:t -> t *)
Parameter set_inlined_debuginfo : t -> t -> M t.
Extract Inlined Constant set_inlined_debuginfo => "Downwards_env.set_inlined_debuginfo".
(* downwards_env.mli:147  val merge_inlined_debuginfo_and_forward_inlined_attribute : t -> from_apply_expr:Inlined_debuginfo.t -> inlined_attribute:Inlined_attribute.t -> t *)
Parameter merge_inlined_debuginfo_and_forward_inlined_attribute : t -> Inlined_debuginfo.t -> Inlined_attribute.t -> M t.
Extract Inlined Constant merge_inlined_debuginfo_and_forward_inlined_attribute => "Downwards_env.merge_inlined_debuginfo_and_forward_inlined_attribute".
(* downwards_env.mli:153  val add_inlined_debuginfo : t -> Debuginfo.t -> Debuginfo.t *)
Parameter add_inlined_debuginfo : t -> Debuginfo.t -> M Debuginfo.t.
Extract Inlined Constant add_inlined_debuginfo => "Downwards_env.add_inlined_debuginfo".
(* downwards_env.mli:155  val round : t -> int *)
Parameter round : t -> M int.
Extract Inlined Constant round => "Downwards_env.round".
(* downwards_env.mli:157  val set_inlining_state : t -> Inlining_state.t -> t *)
Parameter set_inlining_state : t -> Inlining_state.t -> M t.
Extract Inlined Constant set_inlining_state => "Downwards_env.set_inlining_state".
(* downwards_env.mli:159  val get_inlining_state : t -> Inlining_state.t *)
Parameter get_inlining_state : t -> M Inlining_state.t.
Extract Inlined Constant get_inlining_state => "Downwards_env.get_inlining_state".
(* downwards_env.mli:161  val add_cse : t -> Flambda_primitive.Eligible_for_cse.t -> bound_to:Simple.t -> name_mode:Name_mode.t -> t *)
Parameter add_cse : t -> Flambda_primitive.Eligible_for_cse.t -> Simple.t -> Name_mode.t -> M t.
Extract Inlined Constant add_cse => "Downwards_env.add_cse".
(* downwards_env.mli:168  val find_cse : t -> Flambda_primitive.Eligible_for_cse.t -> Simple.t option *)
Parameter find_cse : t -> Flambda_primitive.Eligible_for_cse.t -> M (option Simple.t).
Extract Inlined Constant find_cse => "Downwards_env.find_cse".
(* downwards_env.mli:170  val find_comparison_result : t -> Variable.t -> Comparison_result.t option *)
Parameter find_comparison_result : t -> Variable_.t -> M (option Comparison_result.t).
Extract Inlined Constant find_comparison_result => "Downwards_env.find_comparison_result".
(* downwards_env.mli:172  val cse : t -> Common_subexpression_elimination.t *)
Parameter cse : t -> M Common_subexpression_elimination.t.
Extract Inlined Constant cse => "Downwards_env.cse".
(* downwards_env.mli:174  val comparison_results : t -> Comparison_result.t Variable.Map.t *)
Parameter comparison_results : t -> M (Variable_.Map.t Comparison_result.t).
Extract Inlined Constant comparison_results => "Downwards_env.comparison_results".
(* downwards_env.mli:176  val with_cse : t -> Common_subexpression_elimination.t -> t *)
Parameter with_cse : t -> Common_subexpression_elimination.t -> M t.
Extract Inlined Constant with_cse => "Downwards_env.with_cse".
Module Disable_inlining_reason.
  (* downwards_env.mli:179  type t = | Stub | Speculative_inlining *)
  Inductive t : Type :=
  | Stub : t
  | Speculative_inlining : t.
  Extract Inductive t => "Downwards_env.Disable_inlining_reason.t" [ "Downwards_env.Disable_inlining_reason.Stub" "Downwards_env.Disable_inlining_reason.Speculative_inlining" ].
End Disable_inlining_reason.
(* downwards_env.mli:184  val set_do_not_rebuild_terms_and_disable_inlining : t -> Disable_inlining_reason.t -> t *)
Parameter set_do_not_rebuild_terms_and_disable_inlining : t -> Downwards_env.Disable_inlining_reason.t -> M t.
Extract Inlined Constant set_do_not_rebuild_terms_and_disable_inlining => "Downwards_env.set_do_not_rebuild_terms_and_disable_inlining".
(* downwards_env.mli:187  val set_disable_inlining : t -> Disable_inlining_reason.t -> t *)
Parameter set_disable_inlining : t -> Downwards_env.Disable_inlining_reason.t -> M t.
Extract Inlined Constant set_disable_inlining => "Downwards_env.set_disable_inlining".
Module Disable_inlining.
  (* downwards_env.mli:190  type t = | Disable_inlining of Disable_inlining_reason.t | Do_not_disable_inlining *)
  Inductive t : Type :=
  | Disable_inlining : Downwards_env.Disable_inlining_reason.t -> t
  | Do_not_disable_inlining : t.
  Extract Inductive t => "Downwards_env.Disable_inlining.t" [ "Downwards_env.Disable_inlining.Disable_inlining" "Downwards_env.Disable_inlining.Do_not_disable_inlining" ].
End Disable_inlining.
(* downwards_env.mli:195  val disable_inlining : t -> Disable_inlining.t *)
Parameter disable_inlining : t -> M Downwards_env.Disable_inlining.t.
Extract Inlined Constant disable_inlining => "Downwards_env.disable_inlining".
(* downwards_env.mli:197  val disable_partial_application_stub_generation : t -> bool *)
Parameter disable_partial_application_stub_generation : t -> M bool.
Extract Inlined Constant disable_partial_application_stub_generation => "Downwards_env.disable_partial_application_stub_generation".
(* The tuple with labels (Inlined_attribute.t * forwarded_from:Inlined_debuginfo.t) that the interface writes: Rocq has no label in a tuple. [Forwarded_from_tuple] makes one, and a [match] takes it apart. *)
Inductive forwarded_from_tuple : Type :=
| Forwarded_from_tuple : Inlined_attribute.t -> Inlined_debuginfo.t -> forwarded_from_tuple.
Extract Inductive forwarded_from_tuple => "(Inlined_attribute.t * forwarded_from:Inlined_debuginfo.t)" [ "(fun (x__1, x__2) -> (x__1, ~forwarded_from:x__2))" ] "(fun f__1 x__0 -> let (x__1, ~forwarded_from:x__2) = x__0 in f__1 x__1 x__2)".
(* downwards_env.mli:204  val inlined_attribute_to_forward : t -> (Inlined_attribute.t * forwarded_from:Inlined_debuginfo.t) option *)
Parameter inlined_attribute_to_forward : t -> M (option forwarded_from_tuple).
Extract Inlined Constant inlined_attribute_to_forward => "Downwards_env.inlined_attribute_to_forward".
(* downwards_env.mli:207  val enter_set_of_closures : t -> t *)
Parameter enter_set_of_closures : t -> M t.
Extract Inlined Constant enter_set_of_closures => "Downwards_env.enter_set_of_closures".
(* downwards_env.mli:209  val enter_stub_function : t -> t *)
Parameter enter_stub_function : t -> M t.
Extract Inlined Constant enter_stub_function => "Downwards_env.enter_stub_function".
(* downwards_env.mli:211  val set_rebuild_terms : t -> t *)
Parameter set_rebuild_terms : t -> M t.
Extract Inlined Constant set_rebuild_terms => "Downwards_env.set_rebuild_terms".
(* downwards_env.mli:213  val are_rebuilding_terms : t -> Are_rebuilding_terms.t *)
Parameter are_rebuilding_terms : t -> M Are_rebuilding_terms.t.
Extract Inlined Constant are_rebuilding_terms => "Downwards_env.are_rebuilding_terms".
(* downwards_env.mli:215  val enter_closure : Code_id.t -> return_continuation:Continuation.t -> exn_continuation:Continuation.t -> my_closure:Variable.t -> my_alloc_region:Variable.t -> t -> t *)
Parameter enter_closure : Code_id.t -> Continuation.t -> Continuation.t -> Variable_.t -> Variable_.t -> t -> M t.
Extract Inlined Constant enter_closure => "Downwards_env.enter_closure".
(* downwards_env.mli:224  val closure_info : t -> Closure_info.t *)
Parameter closure_info : t -> M Closure_info.t.
Extract Inlined Constant closure_info => "Downwards_env.closure_info".
(* downwards_env.mli:226  val inlining_arguments : t -> Inlining_arguments.t *)
Parameter inlining_arguments : t -> M Inlining_arguments.t.
Extract Inlined Constant inlining_arguments => "Downwards_env.inlining_arguments".
(* downwards_env.mli:228  val set_inlining_arguments : Inlining_arguments.t -> t -> t *)
Parameter set_inlining_arguments : Inlining_arguments.t -> t -> M t.
Extract Inlined Constant set_inlining_arguments => "Downwards_env.set_inlining_arguments".
(* downwards_env.mli:230  val enter_inlined_apply : called_code:Code.t -> apply:Apply.t -> was_inline_always:bool -> t -> t *)
Parameter enter_inlined_apply : Code.t -> Flambda.Import_.Apply.t -> bool -> t -> M t.
Extract Inlined Constant enter_inlined_apply => "Downwards_env.enter_inlined_apply".
(* downwards_env.mli:233  val generate_phantom_lets : t -> bool *)
Parameter generate_phantom_lets : t -> M bool.
Extract Inlined Constant generate_phantom_lets => "Downwards_env.generate_phantom_lets".
(* downwards_env.mli:235  val inlining_history_tracker : t -> Inlining_history.Tracker.t *)
Parameter inlining_history_tracker : t -> M Inlining_history.Tracker.t.
Extract Inlined Constant inlining_history_tracker => "Downwards_env.inlining_history_tracker".
(* downwards_env.mli:237  val set_inlining_history_tracker : Inlining_history.Tracker.t -> t -> t *)
Parameter set_inlining_history_tracker : Inlining_history.Tracker.t -> t -> M t.
Extract Inlined Constant set_inlining_history_tracker => "Downwards_env.set_inlining_history_tracker".
(* downwards_env.mli:239  val relative_history : t -> Inlining_history.Relative.t *)
Parameter relative_history : t -> M Inlining_history.Relative.t.
Extract Inlined Constant relative_history => "Downwards_env.relative_history".
(* downwards_env.mli:241  val loopify_state : t -> Loopify_state.t *)
Parameter loopify_state : t -> M Loopify_state.t.
Extract Inlined Constant loopify_state => "Downwards_env.loopify_state".
(* downwards_env.mli:243  val set_loopify_state : Loopify_state.t -> t -> t *)
Parameter set_loopify_state : Loopify_state.t -> t -> M t.
Extract Inlined Constant set_loopify_state => "Downwards_env.set_loopify_state".
(* downwards_env.mli:245  val with_code_age_relation : Code_age_relation.t -> t -> t *)
Parameter with_code_age_relation : Flambda2_types.Code_age_relation.t -> t -> M t.
Extract Inlined Constant with_code_age_relation => "Downwards_env.with_code_age_relation".
(* downwards_env.mli:247  val defined_variables_by_scope : t -> Lifted_cont_params.t list *)
Parameter defined_variables_by_scope : t -> M (list Lifted_cont_params.t).
Extract Inlined Constant defined_variables_by_scope => "Downwards_env.defined_variables_by_scope".
(* downwards_env.mli:249  val enter_continuation_handler : Lifted_cont_params.t -> t -> t *)
Parameter enter_continuation_handler : Lifted_cont_params.t -> t -> M t.
Extract Inlined Constant enter_continuation_handler => "Downwards_env.enter_continuation_handler".
(* downwards_env.mli:251  val add_lifted_constant_state : ?maybe_already_defined:unit -> t -> Lifted_constant_state.t -> t *)
Parameter add_lifted_constant_state : option unit -> t -> Lifted_constant_state.t -> M t.
Extract Inlined Constant add_lifted_constant_state => "(fun x__1 x__2 x__3 -> Downwards_env.add_lifted_constant_state ?maybe_already_defined:x__1 x__2 x__3)".
(* downwards_env.mli:254  val variables_defined_in_current_continuation : t -> Lifted_cont_params.t *)
Parameter variables_defined_in_current_continuation : t -> M Lifted_cont_params.t.
Extract Inlined Constant variables_defined_in_current_continuation => "Downwards_env.variables_defined_in_current_continuation".
(* downwards_env.mli:256  val cost_of_lifting_continuations_out_of_current_one : t -> int *)
Parameter cost_of_lifting_continuations_out_of_current_one : t -> M int.
Extract Inlined Constant cost_of_lifting_continuations_out_of_current_one => "Downwards_env.cost_of_lifting_continuations_out_of_current_one".
(* downwards_env.mli:258  val add_lifting_cost : int -> t -> t *)
Parameter add_lifting_cost : int -> t -> M t.
Extract Inlined Constant add_lifting_cost => "Downwards_env.add_lifting_cost".
(* downwards_env.mli:260  val must_inline : t -> bool *)
Parameter must_inline : t -> M bool.
Extract Inlined Constant must_inline => "Downwards_env.must_inline".
(* downwards_env.mli:262  val replay_history : t -> Replay_history.t *)
Parameter replay_history : t -> M Replay_history.t.
Extract Inlined Constant replay_history => "Downwards_env.replay_history".
(* downwards_env.mli:264  val with_replay_history : (Replay_history.t * bool) option -> t -> t *)
Parameter with_replay_history : option (Replay_history.t * bool) -> t -> M t.
Extract Inlined Constant with_replay_history => "Downwards_env.with_replay_history".
(* downwards_env.mli:266  val record_inlining_decision : apply:Apply_expr.t -> Call_site_inlining_decision_type.t -> t -> t *)
Parameter record_inlining_decision : Apply_expr.t -> Call_site_inlining_decision_type.t -> t -> M t.
Extract Inlined Constant record_inlining_decision => "Downwards_env.record_inlining_decision".
(* downwards_env.mli:269  val with_join_analysis : Apply_cont_rewrite_id.t Join_analysis.t option -> t -> t *)
Parameter with_join_analysis : option (Flambda2_types.Join_analysis.t Apply_cont_rewrite_id.t) -> t -> M t.
Extract Inlined Constant with_join_analysis => "Downwards_env.with_join_analysis".
(* downwards_env.mli:272  val join_analysis : t -> Apply_cont_rewrite_id.t Join_analysis.t option *)
Parameter join_analysis : t -> M (option (Flambda2_types.Join_analysis.t Apply_cont_rewrite_id.t)).
Extract Inlined Constant join_analysis => "Downwards_env.join_analysis".
(* downwards_env.mli:274  val map_specialization_cost : f:(Specialization_cost.t -> Specialization_cost.t) -> t -> t *)
Parameter map_specialization_cost : (Specialization_cost.t -> M Specialization_cost.t) -> t -> M t.
Extract Inlined Constant map_specialization_cost => "Downwards_env.map_specialization_cost".
(* downwards_env.mli:277  val specialization_cost : t -> Specialization_cost.t *)
Parameter specialization_cost : t -> M Specialization_cost.t.
Extract Inlined Constant specialization_cost => "Downwards_env.specialization_cost".
(* downwards_env.mli:279  val denv_for_lifted_continuation : denv_for_join:t -> denv:t -> t *)
Parameter denv_for_lifted_continuation : t -> t -> M t.
Extract Inlined Constant denv_for_lifted_continuation => "Downwards_env.denv_for_lifted_continuation".
(* downwards_env.mli:281  val has_seen_a_non_liftable_continuation : t -> bool *)
Parameter has_seen_a_non_liftable_continuation : t -> M bool.
Extract Inlined Constant has_seen_a_non_liftable_continuation => "Downwards_env.has_seen_a_non_liftable_continuation".
(* downwards_env.mli:283  val set_has_seen_a_non_liftable_continuation : t -> t *)
Parameter set_has_seen_a_non_liftable_continuation : t -> M t.
Extract Inlined Constant set_has_seen_a_non_liftable_continuation => "Downwards_env.set_has_seen_a_non_liftable_continuation".
(* downwards_env.mli:285  val is_cold : t -> bool *)
Parameter is_cold : t -> M bool.
Extract Inlined Constant is_cold => "Downwards_env.is_cold".
(* downwards_env.mli:287  val mark_as_cold : t -> t *)
Parameter mark_as_cold : t -> M t.
Extract Inlined Constant mark_as_cold => "Downwards_env.mark_as_cold".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Downwards_env. End Downwards_env.
