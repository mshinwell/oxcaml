(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flow], after its interface
   middle_end/flambda2/simplify/flow/flow.mli
   (Git blob e5dd6716a8607bf064940ded0463310986fcac23). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameters Bound_pattern Code_id Continuation Continuation_callsite_map Continuation_extra_params_and_args Exn_continuation Flambda2_types Flambda_arity Flow_types Format Lifted_constant_state Name Name_occurrences Named_rewrite_id Or_unknown Simple Simplified_named Symbol Target_system Value_slot Variable_.

Module Acc.
  (* flow.mli:17  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flow.Acc.t".
  (* flow.mli:20  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flow.Acc.print".
  (* flow.mli:25  val empty : unit -> t *)
  Parameter empty : unit -> M t.
  Extract Inlined Constant empty => "Flow.Acc.empty".
  (* flow.mli:29  val init_toplevel : dummy_toplevel_cont:Continuation.t -> Bound_parameters.t -> t *)
  Parameter init_toplevel : Continuation.t -> Bound_parameters.t -> M t.
  Extract Inlined Constant init_toplevel => "Flow.Acc.init_toplevel".
  (* flow.mli:34  val enter_continuation : Continuation.t -> recursive:bool -> is_exn_handler:bool -> Bound_parameters.t -> t -> t *)
  Parameter enter_continuation : Continuation.t -> bool -> bool -> Bound_parameters.t -> t -> M t.
  Extract Inlined Constant enter_continuation => "Flow.Acc.enter_continuation".
  (* flow.mli:44  val exit_continuation : Continuation.t -> t -> t *)
  Parameter exit_continuation : Continuation.t -> t -> M t.
  Extract Inlined Constant exit_continuation => "Flow.Acc.exit_continuation".
  (* flow.mli:50  val record_lifted_constants : Lifted_constant_state.t -> t -> t *)
  Parameter record_lifted_constants : Lifted_constant_state.t -> t -> M t.
  Extract Inlined Constant record_lifted_constants => "Flow.Acc.record_lifted_constants".
  (* flow.mli:53  val record_defined_var : Variable.t -> t -> t *)
  Parameter record_defined_var : Variable_.t -> t -> M t.
  Extract Inlined Constant record_defined_var => "Flow.Acc.record_defined_var".
  (* flow.mli:56  val record_var_binding : Variable.t -> Name_occurrences.t -> generate_phantom_lets:bool -> t -> t *)
  Parameter record_var_binding : Variable_.t -> Name_occurrences.t -> bool -> t -> M t.
  Extract Inlined Constant record_var_binding => "Flow.Acc.record_var_binding".
  (* flow.mli:60  val record_let_binding : rewrite_id:Named_rewrite_id.t -> generate_phantom_lets:bool -> let_bound:Bound_pattern.t -> simplified_defining_expr:Simplified_named.t -> t -> t *)
  Parameter record_let_binding : Named_rewrite_id.t -> bool -> Bound_pattern.t -> Simplified_named.t -> t -> M t.
  Extract Inlined Constant record_let_binding => "Flow.Acc.record_let_binding".
  (* flow.mli:70  val record_symbol_projection : Variable.t -> Name_occurrences.t -> t -> t *)
  Parameter record_symbol_projection : Variable_.t -> Name_occurrences.t -> t -> M t.
  Extract Inlined Constant record_symbol_projection => "Flow.Acc.record_symbol_projection".
  (* flow.mli:73  val record_symbol_binding : Symbol.t -> Name_occurrences.t -> t -> t *)
  Parameter record_symbol_binding : Symbol.t -> Name_occurrences.t -> t -> M t.
  Extract Inlined Constant record_symbol_binding => "Flow.Acc.record_symbol_binding".
  (* flow.mli:76  val record_code_id_binding : Code_id.t -> Name_occurrences.t -> t -> t *)
  Parameter record_code_id_binding : Code_id.t -> Name_occurrences.t -> t -> M t.
  Extract Inlined Constant record_code_id_binding => "Flow.Acc.record_code_id_binding".
  (* flow.mli:79  val record_value_slot : Name.t -> Value_slot.t -> Name_occurrences.t -> t -> t *)
  Parameter record_value_slot : Name.t -> Value_slot.t -> Name_occurrences.t -> t -> M t.
  Extract Inlined Constant record_value_slot => "Flow.Acc.record_value_slot".
  (* flow.mli:84  val add_used_in_current_handler : Name_occurrences.t -> t -> t *)
  Parameter add_used_in_current_handler : Name_occurrences.t -> t -> M t.
  Extract Inlined Constant add_used_in_current_handler => "Flow.Acc.add_used_in_current_handler".
  (* flow.mli:88  val add_apply_conts : result_cont:(Apply_cont_rewrite_id.t * Continuation.t) option -> exn_cont:Apply_cont_rewrite_id.t * Exn_continuation.t -> result_arity:_ Flambda_arity.t -> t -> t *)
  Parameter add_apply_conts : option (Apply_cont_rewrite_id.t * Continuation.t) -> (Apply_cont_rewrite_id.t * Exn_continuation.t) -> Flambda_arity.t -> t -> M t.
  Extract Inlined Constant add_apply_conts => "Flow.Acc.add_apply_conts".
  (* flow.mli:97  val add_apply_cont_args : rewrite_id:Apply_cont_rewrite_id.t -> Continuation.t -> Simple.t list -> t -> t *)
  Parameter add_apply_cont_args : Apply_cont_rewrite_id.t -> Continuation.t -> list Simple.t -> t -> M t.
  Extract Inlined Constant add_apply_cont_args => "Flow.Acc.add_apply_cont_args".
  (* flow.mli:105  val add_extra_params_and_args : Continuation.t -> Continuation_extra_params_and_args.t -> t -> t *)
  Parameter add_extra_params_and_args : Continuation.t -> Continuation_extra_params_and_args.t -> t -> M t.
  Extract Inlined Constant add_extra_params_and_args => "Flow.Acc.add_extra_params_and_args".
End Acc.
Module Analysis.
  (* flow.mli:111  val analyze : ?speculative:bool -> ?print_name:string -> machine_width:Target_system.Machine_width.t -> return_continuation:Continuation.t -> exn_continuation:Continuation.t -> code_age_relation:Code_age_relation.t -> used_value_slots:Name_occurrences.t Or_unknown.t -> code_ids_to_never_delete:Code_id.Set.t -> specialization_map:Continuation.t Continuation_callsite_map.t -> Acc.t -> Flow_types.... *)
  Parameter analyze : option bool -> option string -> Target_system.Machine_width.t -> Continuation.t -> Continuation.t -> Flambda2_types.Code_age_relation.t -> Or_unknown.t Name_occurrences.t -> Code_id.Set_.t -> Continuation_callsite_map.t Continuation.t -> Flow.Acc.t -> M Flow_types.Flow_result.t.
  Extract Inlined Constant analyze => "(fun x__1 x__2 x__3 x__4 x__5 x__6 x__7 x__8 x__9 x__10 -> Flow.Analysis.analyze ?speculative:x__1 ?print_name:x__2 x__3 x__4 x__5 x__6 x__7 x__8 x__9 x__10)".
  (* flow.mli:125  val did_perform_mutable_unboxing : Flow_types.Flow_result.t -> bool *)
  Parameter did_perform_mutable_unboxing : Flow_types.Flow_result.t -> M bool.
  Extract Inlined Constant did_perform_mutable_unboxing => "Flow.Analysis.did_perform_mutable_unboxing".
  (* flow.mli:129  val added_useful_alias_in_loop : Typing_env.t -> Acc.t -> Flow_types.Flow_result.t -> bool *)
  Parameter added_useful_alias_in_loop : Flambda2_types.Typing_env.t -> Flow.Acc.t -> Flow_types.Flow_result.t -> M bool.
  Extract Inlined Constant added_useful_alias_in_loop => "Flow.Analysis.added_useful_alias_in_loop".
End Analysis.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Flow. End Flow.
