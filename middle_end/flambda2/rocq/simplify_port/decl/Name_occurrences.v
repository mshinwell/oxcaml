(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2019 OCamlPro SAS                                          *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Name_occurrences], after its interface
   middle_end/flambda2/nominal/name_occurrences.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Code_id_or_symbol Continuation Format Name Name_mode Num_occurrences Symbol Value_slot Variable_.

(* name_occurrences.mli:26  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Name_occurrences.t".
(* name_occurrences.mli:28  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Name_occurrences.empty".
(* name_occurrences.mli:32  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Name_occurrences.print".
(* name_occurrences.mli:34  val equal : t -> t -> bool *)
Parameter equal : t -> t -> M bool.
Extract Inlined Constant equal => "Name_occurrences.equal".
(* name_occurrences.mli:49  val count_continuation : t -> Continuation.t -> Num_occurrences.t *)
Parameter count_continuation : t -> Continuation.t -> M Num_occurrences.t.
Extract Inlined Constant count_continuation => "Name_occurrences.count_continuation".
(* name_occurrences.mli:51  val continuation_is_applied_with_traps : t -> Continuation.t -> bool *)
Parameter continuation_is_applied_with_traps : t -> Continuation.t -> M bool.
Extract Inlined Constant continuation_is_applied_with_traps => "Name_occurrences.continuation_is_applied_with_traps".
(* name_occurrences.mli:55  val count_variable_normal_mode : t -> Variable.t -> Num_occurrences.t *)
Parameter count_variable_normal_mode : t -> Variable_.t -> M Num_occurrences.t.
Extract Inlined Constant count_variable_normal_mode => "Name_occurrences.count_variable_normal_mode".
(* name_occurrences.mli:57  val singleton_variable : Variable.t -> Name_mode.t -> t *)
Parameter singleton_variable : Variable_.t -> Name_mode.t -> M t.
Extract Inlined Constant singleton_variable => "Name_occurrences.singleton_variable".
(* name_occurrences.mli:59  val add_variable : t -> Variable.t -> Name_mode.t -> t *)
Parameter add_variable : t -> Variable_.t -> Name_mode.t -> M t.
Extract Inlined Constant add_variable => "Name_occurrences.add_variable".
(* name_occurrences.mli:61  val add_symbol : t -> Symbol.t -> Name_mode.t -> t *)
Parameter add_symbol : t -> Symbol.t -> Name_mode.t -> M t.
Extract Inlined Constant add_symbol => "Name_occurrences.add_symbol".
(* name_occurrences.mli:63  val add_name : t -> Name.t -> Name_mode.t -> t *)
Parameter add_name : t -> Name.t -> Name_mode.t -> M t.
Extract Inlined Constant add_name => "Name_occurrences.add_name".
(* name_occurrences.mli:67  val add_value_slot_in_projection : t -> Value_slot.t -> Name_mode.t -> t *)
Parameter add_value_slot_in_projection : t -> Value_slot.t -> Name_mode.t -> M t.
Extract Inlined Constant add_value_slot_in_projection => "Name_occurrences.add_value_slot_in_projection".
(* name_occurrences.mli:93  val create_variables : Variable.Set.t -> Name_mode.t -> t *)
Parameter create_variables : Variable_.Set_.t -> Name_mode.t -> M t.
Extract Inlined Constant create_variables => "Name_occurrences.create_variables".
(* name_occurrences.mli:106  val diff : t -> without:t -> t *)
Parameter diff : t -> t -> M t.
Extract Inlined Constant diff => "Name_occurrences.diff".
(* name_occurrences.mli:108  val union : t -> t -> t *)
Parameter union : t -> t -> M t.
Extract Inlined Constant union => "Name_occurrences.union".
(* name_occurrences.mli:117  val inter_domain_is_non_empty : t -> t -> bool *)
Parameter inter_domain_is_non_empty : t -> t -> M bool.
Extract Inlined Constant inter_domain_is_non_empty => "Name_occurrences.inter_domain_is_non_empty".
(* name_occurrences.mli:119  val no_variables : t -> bool *)
Parameter no_variables : t -> M bool.
Extract Inlined Constant no_variables => "Name_occurrences.no_variables".
(* name_occurrences.mli:121  val no_continuations : t -> bool *)
Parameter no_continuations : t -> M bool.
Extract Inlined Constant no_continuations => "Name_occurrences.no_continuations".
(* name_occurrences.mli:137  val symbols : t -> Symbol.Set.t *)
Parameter symbols : t -> M Symbol.Set_.t.
Extract Inlined Constant symbols => "Name_occurrences.symbols".
(* name_occurrences.mli:139  val code_ids : t -> Code_id.Set.t *)
Parameter code_ids : t -> M Code_id.Set_.t.
Extract Inlined Constant code_ids => "Name_occurrences.code_ids".
(* name_occurrences.mli:145  val code_ids_and_newer_version_of_code_ids : t -> Code_id.Set.t *)
Parameter code_ids_and_newer_version_of_code_ids : t -> M Code_id.Set_.t.
Extract Inlined Constant code_ids_and_newer_version_of_code_ids => "Name_occurrences.code_ids_and_newer_version_of_code_ids".
(* name_occurrences.mli:164  val without_names_or_continuations : t -> t *)
Parameter without_names_or_continuations : t -> M t.
Extract Inlined Constant without_names_or_continuations => "Name_occurrences.without_names_or_continuations".
(* name_occurrences.mli:166  val mem_var : t -> Variable.t -> bool *)
Parameter mem_var : t -> Variable_.t -> M bool.
Extract Inlined Constant mem_var => "Name_occurrences.mem_var".
(* name_occurrences.mli:170  val mem_name : t -> Name.t -> bool *)
Parameter mem_name : t -> Name.t -> M bool.
Extract Inlined Constant mem_name => "Name_occurrences.mem_name".
(* name_occurrences.mli:176  val value_slot_is_used_or_imported : t -> Value_slot.t -> bool *)
Parameter value_slot_is_used_or_imported : t -> Value_slot.t -> M bool.
Extract Inlined Constant value_slot_is_used_or_imported => "Name_occurrences.value_slot_is_used_or_imported".
(* name_occurrences.mli:178  val remove_var : t -> var:Variable.t -> t *)
Parameter remove_var : t -> Variable_.t -> M t.
Extract Inlined Constant remove_var => "Name_occurrences.remove_var".
(* name_occurrences.mli:182  val remove_code_id_or_symbol : t -> code_id_or_symbol:Code_id_or_symbol.t -> t *)
Parameter remove_code_id_or_symbol : t -> Code_id_or_symbol.t -> M t.
Extract Inlined Constant remove_code_id_or_symbol => "Name_occurrences.remove_code_id_or_symbol".
(* name_occurrences.mli:184  val remove_continuation : t -> continuation:Continuation.t -> t *)
Parameter remove_continuation : t -> Continuation.t -> M t.
Extract Inlined Constant remove_continuation => "Name_occurrences.remove_continuation".
(* name_occurrences.mli:186  val greatest_name_mode_var : t -> Variable.t -> Name_mode.Or_absent.t *)
Parameter greatest_name_mode_var : t -> Variable_.t -> M Name_mode.Or_absent.t.
Extract Inlined Constant greatest_name_mode_var => "Name_occurrences.greatest_name_mode_var".
(* name_occurrences.mli:188  val downgrade_occurrences_at_strictly_greater_name_mode : t -> Name_mode.t -> t *)
Parameter downgrade_occurrences_at_strictly_greater_name_mode : t -> Name_mode.t -> M t.
Extract Inlined Constant downgrade_occurrences_at_strictly_greater_name_mode => "Name_occurrences.downgrade_occurrences_at_strictly_greater_name_mode".
(* name_occurrences.mli:190  val fold_names : t -> init:'a -> f:('a -> Name.t -> 'a) -> 'a *)
Parameter fold_names : forall {A : Type}, t -> A -> (A -> Name.t -> M A) -> M A.
Extract Inlined Constant fold_names => "Name_occurrences.fold_names".
(* name_occurrences.mli:192  val fold_variables : t -> init:'a -> f:('a -> Variable.t -> 'a) -> 'a *)
Parameter fold_variables : forall {A : Type}, t -> A -> (A -> Variable_.t -> M A) -> M A.
Extract Inlined Constant fold_variables => "Name_occurrences.fold_variables".
(* name_occurrences.mli:194  val fold_continuations_including_in_trap_actions : t -> init:'a -> f:('a -> Continuation.t -> 'a) -> 'a *)
Parameter fold_continuations_including_in_trap_actions : forall {A : Type}, t -> A -> (A -> Continuation.t -> M A) -> M A.
Extract Inlined Constant fold_continuations_including_in_trap_actions => "Name_occurrences.fold_continuations_including_in_trap_actions".
(* name_occurrences.mli:199  val increase_counts : t -> t *)
Parameter increase_counts : t -> M t.
Extract Inlined Constant increase_counts => "Name_occurrences.increase_counts".
