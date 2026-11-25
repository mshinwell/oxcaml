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
   Simplify uses of the compiler's module [Flow_acc], after its interface
   middle_end/flambda2/simplify/flow/flow_acc.mli
   (Git blob 8d0f077e11a2fe2d358cf91a7fec10971f364824). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameters Bound_pattern Code_id Continuation Continuation_extra_params_and_args Exn_continuation Flambda_arity Flow_types Format Lifted_constant_state Name Name_occurrences Named_rewrite_id Simple Simplified_named Symbol Value_slot Variable_.

(* flow_acc.mli:26  type t = Flow_types.Acc.t *)
Definition t : Type := Flow_types.Acc.t.
Extract Inlined Constant t => "Flow_acc.t".
(* flow_acc.mli:29  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Flow_acc.print".
(* flow_acc.mli:35  val normalize_acc : specialization_map: Continuation.t Apply_cont_rewrite_id.Map.t Continuation.Map.t -> t -> t *)
Parameter normalize_acc : Continuation.Map.t (Apply_cont_rewrite_id.Map.t Continuation.t) -> t -> M t.
Extract Inlined Constant normalize_acc => "Flow_acc.normalize_acc".
(* flow_acc.mli:42  val wrong_dummy_toplevel_cont_name : string *)
Parameter wrong_dummy_toplevel_cont_name : string.
Extract Inlined Constant wrong_dummy_toplevel_cont_name => "Flow_acc.wrong_dummy_toplevel_cont_name".
(* flow_acc.mli:47  val empty : unit -> t *)
Parameter empty : unit -> M t.
Extract Inlined Constant empty => "Flow_acc.empty".
(* flow_acc.mli:51  val init_toplevel : dummy_toplevel_cont:Continuation.t -> Bound_parameters.t -> t *)
Parameter init_toplevel : Continuation.t -> Bound_parameters.t -> M t.
Extract Inlined Constant init_toplevel => "Flow_acc.init_toplevel".
(* flow_acc.mli:56  val enter_continuation : Continuation.t -> recursive:bool -> is_exn_handler:bool -> Bound_parameters.t -> t -> t *)
Parameter enter_continuation : Continuation.t -> bool -> bool -> Bound_parameters.t -> t -> M t.
Extract Inlined Constant enter_continuation => "Flow_acc.enter_continuation".
(* flow_acc.mli:66  val exit_continuation : Continuation.t -> t -> t *)
Parameter exit_continuation : Continuation.t -> t -> M t.
Extract Inlined Constant exit_continuation => "Flow_acc.exit_continuation".
(* flow_acc.mli:72  val record_lifted_constants : Lifted_constant_state.t -> t -> t *)
Parameter record_lifted_constants : Lifted_constant_state.t -> t -> M t.
Extract Inlined Constant record_lifted_constants => "Flow_acc.record_lifted_constants".
(* flow_acc.mli:75  val record_defined_var : Variable.t -> t -> t *)
Parameter record_defined_var : Variable_.t -> t -> M t.
Extract Inlined Constant record_defined_var => "Flow_acc.record_defined_var".
(* flow_acc.mli:78  val record_var_binding : Variable.t -> Name_occurrences.t -> generate_phantom_lets:bool -> t -> t *)
Parameter record_var_binding : Variable_.t -> Name_occurrences.t -> bool -> t -> M t.
Extract Inlined Constant record_var_binding => "Flow_acc.record_var_binding".
(* flow_acc.mli:82  val record_let_binding : rewrite_id:Named_rewrite_id.t -> generate_phantom_lets:bool -> let_bound:Bound_pattern.t -> simplified_defining_expr:Simplified_named.t -> t -> t *)
Parameter record_let_binding : Named_rewrite_id.t -> bool -> Bound_pattern.t -> Simplified_named.t -> t -> M t.
Extract Inlined Constant record_let_binding => "Flow_acc.record_let_binding".
(* flow_acc.mli:92  val record_symbol_projection : Variable.t -> Name_occurrences.t -> t -> t *)
Parameter record_symbol_projection : Variable_.t -> Name_occurrences.t -> t -> M t.
Extract Inlined Constant record_symbol_projection => "Flow_acc.record_symbol_projection".
(* flow_acc.mli:95  val record_symbol_binding : Symbol.t -> Name_occurrences.t -> t -> t *)
Parameter record_symbol_binding : Symbol.t -> Name_occurrences.t -> t -> M t.
Extract Inlined Constant record_symbol_binding => "Flow_acc.record_symbol_binding".
(* flow_acc.mli:98  val record_code_id_binding : Code_id.t -> Name_occurrences.t -> t -> t *)
Parameter record_code_id_binding : Code_id.t -> Name_occurrences.t -> t -> M t.
Extract Inlined Constant record_code_id_binding => "Flow_acc.record_code_id_binding".
(* flow_acc.mli:101  val record_value_slot : Name.t -> Value_slot.t -> Name_occurrences.t -> t -> t *)
Parameter record_value_slot : Name.t -> Value_slot.t -> Name_occurrences.t -> t -> M t.
Extract Inlined Constant record_value_slot => "Flow_acc.record_value_slot".
(* flow_acc.mli:105  val add_used_in_current_handler : Name_occurrences.t -> t -> t *)
Parameter add_used_in_current_handler : Name_occurrences.t -> t -> M t.
Extract Inlined Constant add_used_in_current_handler => "Flow_acc.add_used_in_current_handler".
(* flow_acc.mli:109  val add_apply_conts : result_cont:(Apply_cont_rewrite_id.t * Continuation.t) option -> exn_cont:Apply_cont_rewrite_id.t * Exn_continuation.t -> result_arity:_ Flambda_arity.t -> t -> t *)
Parameter add_apply_conts : option (Apply_cont_rewrite_id.t * Continuation.t) -> (Apply_cont_rewrite_id.t * Exn_continuation.t) -> Flambda_arity.t -> t -> M t.
Extract Inlined Constant add_apply_conts => "Flow_acc.add_apply_conts".
(* flow_acc.mli:118  val add_apply_cont_args : rewrite_id:Apply_cont_rewrite_id.t -> Continuation.t -> Simple.t list -> t -> t *)
Parameter add_apply_cont_args : Apply_cont_rewrite_id.t -> Continuation.t -> list Simple.t -> t -> M t.
Extract Inlined Constant add_apply_cont_args => "Flow_acc.add_apply_cont_args".
(* flow_acc.mli:126  val add_extra_params_and_args : Continuation.t -> Continuation_extra_params_and_args.t -> t -> t *)
Parameter add_extra_params_and_args : Continuation.t -> Continuation_extra_params_and_args.t -> t -> M t.
Extract Inlined Constant add_extra_params_and_args => "Flow_acc.add_extra_params_and_args".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Flow_acc. End Flow_acc.
