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
   Simplify uses of the compiler's module [Flambda2_types], after its interface
   middle_end/flambda2/types/flambda2_types.mli
   (Git blob fc25fd91715a9446cedf37513203629d8471ee4a). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Apply_cont_rewrite_id Bound_name Bound_parameters Code_id Compilation_unit Continuation Continuation_use_kind Empty_array_kind Flambda_arity Flambda_kind Format Function_slot Int32 Int64 Name Name_mode Name_occurrences Numeric_types Or_bottom Or_unknown Or_unknown_or_bottom Rec_info_expr Reg_width_const Scope Simple String_info Symbol Symbol_projection Tag Target_ocaml_int Target_system Targetint_32_64 Value_slot Variable_ Vector_types.

(* flambda2_types.mli:20  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Flambda2_types.t".
(* flambda2_types.mli:22  type flambda_type = t *)
Definition flambda_type : Type := t.
Extract Inlined Constant flambda_type => "Flambda2_types.flambda_type".
(* flambda2_types.mli:24  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Flambda2_types.print".
(* flambda2_types.mli:26  val arity_of_list : t list -> [`Unarized] Flambda_arity.t *)
Parameter arity_of_list : list t -> M Flambda_arity.t_Unarized.
Extract Inlined Constant arity_of_list => "Flambda2_types.arity_of_list".
(* flambda2_types.mli:38  type typing_env *)
Parameter typing_env : Type.
Extract Inlined Constant typing_env => "Flambda2_types.typing_env".
(* flambda2_types.mli:40  type typing_env_extension *)
Parameter typing_env_extension : Type.
Extract Inlined Constant typing_env_extension => "Flambda2_types.typing_env_extension".
Module Code_age_relation.
  (* flambda2_types.mli:43  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda2_types.Code_age_relation.t".
  (* flambda2_types.mli:45  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda2_types.Code_age_relation.print".
  (* flambda2_types.mli:47  val empty : t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Flambda2_types.Code_age_relation.empty".
  (* flambda2_types.mli:49  val get_older_version_of : t -> Code_id.t -> Code_id.t option *)
  Parameter get_older_version_of : t -> Code_id.t -> M (option Code_id.t).
  Extract Inlined Constant get_older_version_of => "Flambda2_types.Code_age_relation.get_older_version_of".
  (* flambda2_types.mli:57  val meet_set : t -> resolver:(Compilation_unit.t -> t option) -> Code_id.Set.t -> Code_id.Set.t -> Code_id.Set.t Or_bottom.t *)
  Parameter meet_set : t -> (Compilation_unit.t -> M (option t)) -> Code_id.Set_.t -> Code_id.Set_.t -> M (Or_bottom.t Code_id.Set_.t).
  Extract Inlined Constant meet_set => "Flambda2_types.Code_age_relation.meet_set".
End Code_age_relation.
Module Typing_env_extension.
  (* flambda2_types.mli:66  type t = typing_env_extension *)
  Definition t : Type := Flambda2_types.typing_env_extension.
  Extract Inlined Constant t => "Flambda2_types.Typing_env_extension.t".
  (* flambda2_types.mli:72  val empty : t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Flambda2_types.Typing_env_extension.empty".
  (* flambda2_types.mli:74  val has_equation : Name.t -> t -> bool *)
  Parameter has_equation : Name.t -> t -> M bool.
  Extract Inlined Constant has_equation => "Flambda2_types.Typing_env_extension.has_equation".
  (* flambda2_types.mli:78  val add_or_replace_equation : t -> Name.t -> flambda_type -> t *)
  Parameter add_or_replace_equation : t -> Name.t -> Flambda2_types.flambda_type -> M t.
  Extract Inlined Constant add_or_replace_equation => "Flambda2_types.Typing_env_extension.add_or_replace_equation".
  (* flambda2_types.mli:87  val add_is_int_relation : machine_width:Target_system.Machine_width.t -> t -> Name.t -> scrutinee:Simple.t -> t *)
  Parameter add_is_int_relation : Target_system.Machine_width.t -> t -> Name.t -> Simple.t -> M t.
  Extract Inlined Constant add_is_int_relation => "Flambda2_types.Typing_env_extension.add_is_int_relation".
  (* flambda2_types.mli:94  val add_get_tag_relation : t -> Name.t -> scrutinee:Simple.t -> t *)
  Parameter add_get_tag_relation : t -> Name.t -> Simple.t -> M t.
  Extract Inlined Constant add_get_tag_relation => "Flambda2_types.Typing_env_extension.add_get_tag_relation".
  (* flambda2_types.mli:96  val disjoint_union : t -> t -> t *)
  Parameter disjoint_union : t -> t -> M t.
  Extract Inlined Constant disjoint_union => "Flambda2_types.Typing_env_extension.disjoint_union".
  Module With_extra_variables.
    (* flambda2_types.mli:99  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Flambda2_types.Typing_env_extension.With_extra_variables.t".
  End With_extra_variables.
End Typing_env_extension.
Module Typing_env.
  (* flambda2_types.mli:120  type t = typing_env *)
  Definition t : Type := Flambda2_types.typing_env.
  Extract Inlined Constant t => "Flambda2_types.Typing_env.t".
  Module Serializable.
    (* flambda2_types.mli:140  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Flambda2_types.Typing_env.Serializable.t".
  End Serializable.
  (* flambda2_types.mli:165  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda2_types.Typing_env.print".
  (* flambda2_types.mli:167  val create : machine_width:Target_system.Machine_width.t -> resolver:(Compilation_unit.t -> Serializable.t option) -> t *)
  Parameter create : Target_system.Machine_width.t -> (Compilation_unit.t -> M (option Flambda2_types.Typing_env.Serializable.t)) -> M t.
  Extract Inlined Constant create => "Flambda2_types.Typing_env.create".
  (* flambda2_types.mli:179  val machine_width : t -> Target_system.Machine_width.t *)
  Parameter machine_width : t -> M Target_system.Machine_width.t.
  Extract Inlined Constant machine_width => "Flambda2_types.Typing_env.machine_width".
  (* flambda2_types.mli:181  val closure_env : t -> t *)
  Parameter closure_env : t -> M t.
  Extract Inlined Constant closure_env => "Flambda2_types.Typing_env.closure_env".
  (* flambda2_types.mli:183  val resolver : t -> Compilation_unit.t -> Serializable.t option *)
  Parameter resolver : t -> Compilation_unit.t -> M (option Flambda2_types.Typing_env.Serializable.t).
  Extract Inlined Constant resolver => "Flambda2_types.Typing_env.resolver".
  (* flambda2_types.mli:185  val code_age_relation_resolver : t -> Compilation_unit.t -> Code_age_relation.t option *)
  Parameter code_age_relation_resolver : t -> Compilation_unit.t -> M (option Flambda2_types.Code_age_relation.t).
  Extract Inlined Constant code_age_relation_resolver => "Flambda2_types.Typing_env.code_age_relation_resolver".
  (* flambda2_types.mli:188  val current_scope : t -> Scope.t *)
  Parameter current_scope : t -> M Scope.t.
  Extract Inlined Constant current_scope => "Flambda2_types.Typing_env.current_scope".
  (* flambda2_types.mli:190  val increment_scope : t -> t *)
  Parameter increment_scope : t -> M t.
  Extract Inlined Constant increment_scope => "Flambda2_types.Typing_env.increment_scope".
  (* flambda2_types.mli:192  val add_definition : t -> Bound_name.t -> Flambda_kind.t -> t *)
  Parameter add_definition : t -> Bound_name.t -> Flambda_kind.t -> M t.
  Extract Inlined Constant add_definition => "Flambda2_types.Typing_env.add_definition".
  (* flambda2_types.mli:194  val add_definitions_of_params : t -> params:Bound_parameters.t -> t *)
  Parameter add_definitions_of_params : t -> Bound_parameters.t -> M t.
  Extract Inlined Constant add_definitions_of_params => "Flambda2_types.Typing_env.add_definitions_of_params".
  (* flambda2_types.mli:196  val add_symbol_definition : t -> Symbol.t -> t *)
  Parameter add_symbol_definition : t -> Symbol.t -> M t.
  Extract Inlined Constant add_symbol_definition => "Flambda2_types.Typing_env.add_symbol_definition".
  (* flambda2_types.mli:200  val add_symbol_projection : t -> Variable.t -> Symbol_projection.t -> t *)
  Parameter add_symbol_projection : t -> Variable_.t -> Symbol_projection.t -> M t.
  Extract Inlined Constant add_symbol_projection => "Flambda2_types.Typing_env.add_symbol_projection".
  (* flambda2_types.mli:202  val find_symbol_projection : t -> Variable.t -> Symbol_projection.t option *)
  Parameter find_symbol_projection : t -> Variable_.t -> M (option Symbol_projection.t).
  Extract Inlined Constant find_symbol_projection => "Flambda2_types.Typing_env.find_symbol_projection".
  (* flambda2_types.mli:204  val add_equation : t -> Name.t -> flambda_type -> t *)
  Parameter add_equation : t -> Name.t -> Flambda2_types.flambda_type -> M t.
  Extract Inlined Constant add_equation => "Flambda2_types.Typing_env.add_equation".
  (* flambda2_types.mli:209  val add_is_null_relation : t -> Name.t -> scrutinee:Simple.t -> t *)
  Parameter add_is_null_relation : t -> Name.t -> Simple.t -> M t.
  Extract Inlined Constant add_is_null_relation => "Flambda2_types.Typing_env.add_is_null_relation".
  (* flambda2_types.mli:211  val add_is_int_relation : t -> Name.t -> scrutinee:Simple.t -> t *)
  Parameter add_is_int_relation : t -> Name.t -> Simple.t -> M t.
  Extract Inlined Constant add_is_int_relation => "Flambda2_types.Typing_env.add_is_int_relation".
  (* flambda2_types.mli:213  val add_get_tag_relation : t -> Name.t -> scrutinee:Simple.t -> t *)
  Parameter add_get_tag_relation : t -> Name.t -> Simple.t -> M t.
  Extract Inlined Constant add_get_tag_relation => "Flambda2_types.Typing_env.add_get_tag_relation".
  (* flambda2_types.mli:215  val mem : ?min_name_mode:Name_mode.t -> t -> Name.t -> bool *)
  Parameter mem : option Name_mode.t -> t -> Name.t -> M bool.
  Extract Inlined Constant mem => "(fun x__1 x__2 x__3 -> Flambda2_types.Typing_env.mem ?min_name_mode:x__1 x__2 x__3)".
  (* flambda2_types.mli:217  val mem_simple : ?min_name_mode:Name_mode.t -> t -> Simple.t -> bool *)
  Parameter mem_simple : option Name_mode.t -> t -> Simple.t -> M bool.
  Extract Inlined Constant mem_simple => "(fun x__1 x__2 x__3 -> Flambda2_types.Typing_env.mem_simple ?min_name_mode:x__1 x__2 x__3)".
  (* flambda2_types.mli:219  val find : t -> Name.t -> Flambda_kind.t option -> flambda_type *)
  Parameter find : t -> Name.t -> option Flambda_kind.t -> M Flambda2_types.flambda_type.
  Extract Inlined Constant find => "Flambda2_types.Typing_env.find".
  (* flambda2_types.mli:221  val find_params : t -> Bound_parameters.t -> flambda_type list *)
  Parameter find_params : t -> Bound_parameters.t -> M (list Flambda2_types.flambda_type).
  Extract Inlined Constant find_params => "Flambda2_types.Typing_env.find_params".
  (* flambda2_types.mli:223  val add_env_extension : t -> Typing_env_extension.t -> t *)
  Parameter add_env_extension : t -> Flambda2_types.Typing_env_extension.t -> M t.
  Extract Inlined Constant add_env_extension => "Flambda2_types.Typing_env.add_env_extension".
  (* flambda2_types.mli:225  val add_env_extension_with_extra_variables : t -> Typing_env_extension.With_extra_variables.t -> t *)
  Parameter add_env_extension_with_extra_variables : t -> Flambda2_types.Typing_env_extension.With_extra_variables.t -> M t.
  Extract Inlined Constant add_env_extension_with_extra_variables => "Flambda2_types.Typing_env.add_env_extension_with_extra_variables".
  (* flambda2_types.mli:231  val get_canonical_simple_exn : t -> ?min_name_mode:Name_mode.t -> ?name_mode_of_existing_simple:Name_mode.t -> Simple.t -> Simple.t *)
  Parameter get_canonical_simple_exn : t -> option Name_mode.t -> option Name_mode.t -> Simple.t -> M Simple.t.
  Extract Inlined Constant get_canonical_simple_exn => "(fun x__1 x__2 x__3 x__4 -> Flambda2_types.Typing_env.get_canonical_simple_exn x__1 ?min_name_mode:x__2 ?name_mode_of_existing_simple:x__3 x__4)".
  (* flambda2_types.mli:239  val type_simple_in_term_exn : t -> ?min_name_mode:Name_mode.t -> Simple.t -> flambda_type * Simple.t *)
  Parameter type_simple_in_term_exn : t -> option Name_mode.t -> Simple.t -> M (Flambda2_types.flambda_type * Simple.t).
  Extract Inlined Constant type_simple_in_term_exn => "(fun x__1 x__2 x__3 -> Flambda2_types.Typing_env.type_simple_in_term_exn x__1 ?min_name_mode:x__2 x__3)".
  (* flambda2_types.mli:243  val get_alias_then_canonical_simple_exn : t -> ?min_name_mode:Name_mode.t -> ?name_mode_of_existing_simple:Name_mode.t -> flambda_type -> Simple.t *)
  Parameter get_alias_then_canonical_simple_exn : t -> option Name_mode.t -> option Name_mode.t -> Flambda2_types.flambda_type -> M Simple.t.
  Extract Inlined Constant get_alias_then_canonical_simple_exn => "(fun x__1 x__2 x__3 x__4 -> Flambda2_types.Typing_env.get_alias_then_canonical_simple_exn x__1 ?min_name_mode:x__2 ?name_mode_of_existing_simple:x__3 x__4)".
  (* flambda2_types.mli:250  val code_age_relation : t -> Code_age_relation.t *)
  Parameter code_age_relation : t -> M Flambda2_types.Code_age_relation.t.
  Extract Inlined Constant code_age_relation => "Flambda2_types.Typing_env.code_age_relation".
  (* flambda2_types.mli:252  val with_code_age_relation : t -> Code_age_relation.t -> t *)
  Parameter with_code_age_relation : t -> Flambda2_types.Code_age_relation.t -> M t.
  Extract Inlined Constant with_code_age_relation => "Flambda2_types.Typing_env.with_code_age_relation".
  (* flambda2_types.mli:254  val add_to_code_age_relation : t -> new_code_id:Code_id.t -> old_code_id:Code_id.t option -> t *)
  Parameter add_to_code_age_relation : t -> Code_id.t -> option Code_id.t -> M t.
  Extract Inlined Constant add_to_code_age_relation => "Flambda2_types.Typing_env.add_to_code_age_relation".
  (* flambda2_types.mli:257  val free_names_transitive : t -> flambda_type -> Name_occurrences.t *)
  Parameter free_names_transitive : t -> Flambda2_types.flambda_type -> M Name_occurrences.t.
  Extract Inlined Constant free_names_transitive => "Flambda2_types.Typing_env.free_names_transitive".
  (* flambda2_types.mli:259  val bump_current_level_scope : t -> t *)
  Parameter bump_current_level_scope : t -> M t.
  Extract Inlined Constant bump_current_level_scope => "Flambda2_types.Typing_env.bump_current_level_scope".
  (* flambda2_types.mli:261  val stable_compare_simples : t -> Simple.t -> Simple.t -> int *)
  Parameter stable_compare_simples : t -> Simple.t -> Simple.t -> M int.
  Extract Inlined Constant stable_compare_simples => "Flambda2_types.Typing_env.stable_compare_simples".
  Module Alias_set.
    (* flambda2_types.mli:264  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Flambda2_types.Typing_env.Alias_set.t".
    (* flambda2_types.mli:266  val filter : t -> f:(Simple.t -> bool) -> t *)
    Parameter filter : t -> (Simple.t -> M bool) -> M t.
    Extract Inlined Constant filter => "Flambda2_types.Typing_env.Alias_set.filter".
    (* flambda2_types.mli:268  val get_singleton : t -> Simple.t option *)
    Parameter get_singleton : t -> M (option Simple.t).
    Extract Inlined Constant get_singleton => "Flambda2_types.Typing_env.Alias_set.get_singleton".
    (* flambda2_types.mli:270  val find_best : t -> Simple.t option *)
    Parameter find_best : t -> M (option Simple.t).
    Extract Inlined Constant find_best => "Flambda2_types.Typing_env.Alias_set.find_best".
    (* flambda2_types.mli:272  val inter : t -> t -> t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Flambda2_types.Typing_env.Alias_set.inter".
    (* flambda2_types.mli:274  val singleton : Simple.t -> t *)
    Parameter singleton : Simple.t -> M t.
    Extract Inlined Constant singleton => "Flambda2_types.Typing_env.Alias_set.singleton".
  End Alias_set.
  (* flambda2_types.mli:279  val aliases_of_simple : t -> min_name_mode:Name_mode.t -> Simple.t -> Alias_set.t *)
  Parameter aliases_of_simple : t -> Name_mode.t -> Simple.t -> M Flambda2_types.Typing_env.Alias_set.t.
  Extract Inlined Constant aliases_of_simple => "Flambda2_types.Typing_env.aliases_of_simple".
  (* flambda2_types.mli:295  val notify_test_observer : t -> at_handler:Continuation.t -> unit *)
  Parameter notify_test_observer : t -> Continuation.t -> M unit.
  Extract Inlined Constant notify_test_observer => "Flambda2_types.Typing_env.notify_test_observer".
End Typing_env.
(* flambda2_types.mli:298  val meet : Typing_env.t -> t -> t -> (t * Typing_env.t) Or_bottom.t *)
Parameter meet : Flambda2_types.Typing_env.t -> t -> t -> M (Or_bottom.t (t * Flambda2_types.Typing_env.t)).
Extract Inlined Constant meet => "Flambda2_types.meet".
(* flambda2_types.mli:300  val meet_shape : Typing_env.t -> t -> shape:t -> Typing_env.t Or_bottom.t *)
Parameter meet_shape : Flambda2_types.Typing_env.t -> t -> t -> M (Or_bottom.t Flambda2_types.Typing_env.t).
Extract Inlined Constant meet_shape => "Flambda2_types.meet_shape".
Module Join_analysis.
  (* flambda2_types.mli:303  type 'a t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Flambda2_types.Join_analysis.t".
  (* flambda2_types.mli:305  val print : Format.formatter -> 'a t -> unit *)
  Parameter print : forall {A : Type}, Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Flambda2_types.Join_analysis.print".
  Module Variable_refined_at_join.
    (* flambda2_types.mli:308  type 'a t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Flambda2_types.Join_analysis.Variable_refined_at_join.t".
    (* flambda2_types.mli:310  val fold_values_at_uses : ('a -> Reg_width_const.t Or_unknown.t -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
    Parameter fold_values_at_uses : forall {A B : Type}, (A -> Or_unknown.t Reg_width_const.t -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold_values_at_uses => "Flambda2_types.Join_analysis.Variable_refined_at_join.fold_values_at_uses".
  End Variable_refined_at_join.
  (* flambda2_types.mli:314  type 'a simple_refined_at_join = | Not_refined_at_join | Invariant_in_all_uses of Simple.t | Variable_refined_at_these_uses of 'a Variable_refined_at_join.t *)
  Inductive simple_refined_at_join_ (A : Type) : Type :=
  | Not_refined_at_join : simple_refined_at_join_ A
  | Invariant_in_all_uses : Simple.t -> simple_refined_at_join_ A
  | Variable_refined_at_these_uses : Flambda2_types.Join_analysis.Variable_refined_at_join.t A -> simple_refined_at_join_ A.
  Arguments Not_refined_at_join {A}.
  Arguments Invariant_in_all_uses {A}.
  Arguments Variable_refined_at_these_uses {A}.
  Extract Inductive simple_refined_at_join_ => "Flambda2_types.Join_analysis.simple_refined_at_join" [ "Flambda2_types.Join_analysis.Not_refined_at_join" "Flambda2_types.Join_analysis.Invariant_in_all_uses" "Flambda2_types.Join_analysis.Variable_refined_at_these_uses" ].
  (* flambda2_types.mli:319  val simple_refined_at_join : 'a t -> Typing_env.t -> Simple.t -> 'a simple_refined_at_join *)
  Parameter simple_refined_at_join : forall {A : Type}, t A -> Flambda2_types.Typing_env.t -> Simple.t -> M (simple_refined_at_join_ A).
  Extract Inlined Constant simple_refined_at_join => "Flambda2_types.Join_analysis.simple_refined_at_join".
  Module Simples_at_join.
    (* flambda2_types.mli:323  type 'a t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Flambda2_types.Join_analysis.Simples_at_join.t".
    (* flambda2_types.mli:325  type definition_at_use = At_normal_mode of Simple.t [@@unboxed] *)
    Inductive definition_at_use : Type :=
    | At_normal_mode : Simple.t -> definition_at_use.
    Extract Inductive definition_at_use => "Flambda2_types.Join_analysis.Simples_at_join.definition_at_use" [ "Flambda2_types.Join_analysis.Simples_at_join.At_normal_mode" ].
    (* flambda2_types.mli:327  val fold_definitions_at_uses : ('a -> definition_at_use -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
    Parameter fold_definitions_at_uses : forall {A B : Type}, (A -> definition_at_use -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold_definitions_at_uses => "Flambda2_types.Join_analysis.Simples_at_join.fold_definitions_at_uses".
  End Simples_at_join.
  (* flambda2_types.mli:336  val fold_variables_created_at_join : f:(Name.t -> 'a Simples_at_join.t -> Flambda_kind.t -> 'b -> 'b) -> 'a t -> init:'b -> 'b *)
  Parameter fold_variables_created_at_join : forall {A B : Type}, (Name.t -> Flambda2_types.Join_analysis.Simples_at_join.t A -> Flambda_kind.t -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold_variables_created_at_join => "Flambda2_types.Join_analysis.fold_variables_created_at_join".
End Join_analysis.
(* flambda2_types.mli:343  val cut_and_n_way_join : Typing_env.t -> (Typing_env.t * Apply_cont_rewrite_id.t * Continuation_use_kind.t) list -> params:Bound_parameters.t -> cut_after:Scope.t -> extra_lifted_consts_in_use_envs:Symbol.Set.t -> extra_allowed_names:Name_occurrences.t -> Typing_env.t * Apply_cont_rewrite_id.t Join_analysis.t option *)
Parameter cut_and_n_way_join : Flambda2_types.Typing_env.t -> list (tuple3 Flambda2_types.Typing_env.t Apply_cont_rewrite_id.t Continuation_use_kind.t) -> Bound_parameters.t -> Scope.t -> Symbol.Set_.t -> Name_occurrences.t -> M (Flambda2_types.Typing_env.t * option (Flambda2_types.Join_analysis.t Apply_cont_rewrite_id.t)).
Extract Inlined Constant cut_and_n_way_join => "Flambda2_types.cut_and_n_way_join".
Module Function_type.
  (* flambda2_types.mli:353  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda2_types.Function_type.t".
  (* flambda2_types.mli:355  val create : Code_id.t -> rec_info:flambda_type -> t *)
  Parameter create : Code_id.t -> Flambda2_types.flambda_type -> M t.
  Extract Inlined Constant create => "Flambda2_types.Function_type.create".
  (* flambda2_types.mli:357  val code_id : t -> Code_id.t *)
  Parameter code_id : t -> M Code_id.t.
  Extract Inlined Constant code_id => "Flambda2_types.Function_type.code_id".
  (* flambda2_types.mli:359  val rec_info : t -> flambda_type *)
  Parameter rec_info : t -> M Flambda2_types.flambda_type.
  Extract Inlined Constant rec_info => "Flambda2_types.Function_type.rec_info".
End Function_type.
Module Closures_entry.
  (* flambda2_types.mli:363  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda2_types.Closures_entry.t".
  (* flambda2_types.mli:369  val value_slot_types : t -> flambda_type Value_slot.Map.t *)
  Parameter value_slot_types : t -> M (Value_slot.Map.t Flambda2_types.flambda_type).
  Extract Inlined Constant value_slot_types => "Flambda2_types.Closures_entry.value_slot_types".
End Closures_entry.
(* flambda2_types.mli:374  type to_erase = | Everything_not_in of Typing_env.t | All_variables_except of Variable.Set.t *)
Inductive to_erase : Type :=
| Everything_not_in : Flambda2_types.Typing_env.t -> to_erase
| All_variables_except : Variable_.Set_.t -> to_erase.
Extract Inductive to_erase => "Flambda2_types.to_erase" [ "Flambda2_types.Everything_not_in" "Flambda2_types.All_variables_except" ].
(* flambda2_types.mli:382  val make_suitable_for_environment : Typing_env.t -> to_erase -> (Name.t * flambda_type) list -> Typing_env_extension.With_extra_variables.t *)
Parameter make_suitable_for_environment : Flambda2_types.Typing_env.t -> to_erase -> list (Name.t * flambda_type) -> M Flambda2_types.Typing_env_extension.With_extra_variables.t.
Extract Inlined Constant make_suitable_for_environment => "Flambda2_types.make_suitable_for_environment".
(* flambda2_types.mli:396  val type_is_useful : Flambda_kind.With_subkind.t -> Typing_env.t -> Name.t -> bool *)
Parameter type_is_useful : Flambda_kind.With_subkind.t -> Flambda2_types.Typing_env.t -> Name.t -> M bool.
Extract Inlined Constant type_is_useful => "Flambda2_types.type_is_useful".
(* flambda2_types.mli:402  val bottom : Flambda_kind.t -> t *)
Parameter bottom : Flambda_kind.t -> M t.
Extract Inlined Constant bottom => "Flambda2_types.bottom".
(* flambda2_types.mli:405  val unknown : Flambda_kind.t -> t *)
Parameter unknown : Flambda_kind.t -> M t.
Extract Inlined Constant unknown => "Flambda2_types.unknown".
(* flambda2_types.mli:407  val unknown_with_subkind : ?alloc_mode:Alloc_mode.For_types.t -> machine_width:Target_system.Machine_width.t -> Flambda_kind.With_subkind.t -> t *)
Parameter unknown_with_subkind : option Alloc_mode.For_types.t -> Target_system.Machine_width.t -> Flambda_kind.With_subkind.t -> M t.
Extract Inlined Constant unknown_with_subkind => "(fun x__1 x__2 x__3 -> Flambda2_types.unknown_with_subkind ?alloc_mode:x__1 x__2 x__3)".
(* flambda2_types.mli:419  val any_value : t *)
Parameter any_value : t.
Extract Inlined Constant any_value => "Flambda2_types.any_value".
(* flambda2_types.mli:421  val any_tagged_immediate : t *)
Parameter any_tagged_immediate : t.
Extract Inlined Constant any_tagged_immediate => "Flambda2_types.any_tagged_immediate".
(* flambda2_types.mli:423  val any_tagged_immediate_or_null : t *)
Parameter any_tagged_immediate_or_null : t.
Extract Inlined Constant any_tagged_immediate_or_null => "Flambda2_types.any_tagged_immediate_or_null".
(* flambda2_types.mli:425  val any_tagged_bool : machine_width:Target_system.Machine_width.t -> t *)
Parameter any_tagged_bool : Target_system.Machine_width.t -> M t.
Extract Inlined Constant any_tagged_bool => "Flambda2_types.any_tagged_bool".
(* flambda2_types.mli:437  val any_naked_immediate : t *)
Parameter any_naked_immediate : t.
Extract Inlined Constant any_naked_immediate => "Flambda2_types.any_naked_immediate".
(* flambda2_types.mli:439  val any_naked_bool : machine_width:Target_system.Machine_width.t -> t *)
Parameter any_naked_bool : Target_system.Machine_width.t -> M t.
Extract Inlined Constant any_naked_bool => "Flambda2_types.any_naked_bool".
(* flambda2_types.mli:441  val any_naked_float32 : t *)
Parameter any_naked_float32 : t.
Extract Inlined Constant any_naked_float32 => "Flambda2_types.any_naked_float32".
(* flambda2_types.mli:443  val any_naked_float : t *)
Parameter any_naked_float : t.
Extract Inlined Constant any_naked_float => "Flambda2_types.any_naked_float".
(* flambda2_types.mli:445  val any_naked_int8 : t *)
Parameter any_naked_int8 : t.
Extract Inlined Constant any_naked_int8 => "Flambda2_types.any_naked_int8".
(* flambda2_types.mli:447  val any_naked_int16 : t *)
Parameter any_naked_int16 : t.
Extract Inlined Constant any_naked_int16 => "Flambda2_types.any_naked_int16".
(* flambda2_types.mli:449  val any_naked_int32 : t *)
Parameter any_naked_int32 : t.
Extract Inlined Constant any_naked_int32 => "Flambda2_types.any_naked_int32".
(* flambda2_types.mli:451  val any_naked_int64 : t *)
Parameter any_naked_int64 : t.
Extract Inlined Constant any_naked_int64 => "Flambda2_types.any_naked_int64".
(* flambda2_types.mli:453  val any_naked_nativeint : t *)
Parameter any_naked_nativeint : t.
Extract Inlined Constant any_naked_nativeint => "Flambda2_types.any_naked_nativeint".
(* flambda2_types.mli:455  val any_region : t *)
Parameter any_region : t.
Extract Inlined Constant any_region => "Flambda2_types.any_region".
(* flambda2_types.mli:461  val this_tagged_immediate : Target_ocaml_int.t -> t *)
Parameter this_tagged_immediate : Target_ocaml_int.t -> M t.
Extract Inlined Constant this_tagged_immediate => "Flambda2_types.this_tagged_immediate".
(* flambda2_types.mli:463  val this_boxed_float32 : Numeric_types.Float32_by_bit_pattern.t -> Alloc_mode.For_types.t -> t *)
Parameter this_boxed_float32 : Numeric_types.Float32_by_bit_pattern.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant this_boxed_float32 => "Flambda2_types.this_boxed_float32".
(* flambda2_types.mli:466  val this_boxed_float : Numeric_types.Float_by_bit_pattern.t -> Alloc_mode.For_types.t -> t *)
Parameter this_boxed_float : Numeric_types.Float_by_bit_pattern.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant this_boxed_float => "Flambda2_types.this_boxed_float".
(* flambda2_types.mli:469  val this_boxed_int32 : Numeric_types.Int32.t -> Alloc_mode.For_types.t -> t *)
Parameter this_boxed_int32 : Numeric_types.Int32.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant this_boxed_int32 => "Flambda2_types.this_boxed_int32".
(* flambda2_types.mli:471  val this_boxed_int64 : Numeric_types.Int64.t -> Alloc_mode.For_types.t -> t *)
Parameter this_boxed_int64 : Numeric_types.Int64.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant this_boxed_int64 => "Flambda2_types.this_boxed_int64".
(* flambda2_types.mli:473  val this_boxed_nativeint : Targetint_32_64.t -> Alloc_mode.For_types.t -> t *)
Parameter this_boxed_nativeint : Targetint_32_64.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant this_boxed_nativeint => "Flambda2_types.this_boxed_nativeint".
(* flambda2_types.mli:475  val this_boxed_vec128 : Vector_types.Vec128.Bit_pattern.t -> Alloc_mode.For_types.t -> t *)
Parameter this_boxed_vec128 : Vector_types.Vec128.Bit_pattern.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant this_boxed_vec128 => "Flambda2_types.this_boxed_vec128".
(* flambda2_types.mli:478  val this_boxed_vec256 : Vector_types.Vec256.Bit_pattern.t -> Alloc_mode.For_types.t -> t *)
Parameter this_boxed_vec256 : Vector_types.Vec256.Bit_pattern.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant this_boxed_vec256 => "Flambda2_types.this_boxed_vec256".
(* flambda2_types.mli:481  val this_boxed_vec512 : Vector_types.Vec512.Bit_pattern.t -> Alloc_mode.For_types.t -> t *)
Parameter this_boxed_vec512 : Vector_types.Vec512.Bit_pattern.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant this_boxed_vec512 => "Flambda2_types.this_boxed_vec512".
(* flambda2_types.mli:484  val this_boxed_mask : Vector_types.Mask.Bit_pattern.t -> Alloc_mode.For_types.t -> t *)
Parameter this_boxed_mask : Vector_types.Mask.Bit_pattern.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant this_boxed_mask => "Flambda2_types.this_boxed_mask".
(* flambda2_types.mli:487  val these_tagged_immediates : Target_ocaml_int.Set.t -> t *)
Parameter these_tagged_immediates : Target_ocaml_int.Set_.t -> M t.
Extract Inlined Constant these_tagged_immediates => "Flambda2_types.these_tagged_immediates".
(* flambda2_types.mli:489  val these_boxed_float32s : Numeric_types.Float32_by_bit_pattern.Set.t -> Alloc_mode.For_types.t -> t *)
Parameter these_boxed_float32s : Numeric_types.Float32_by_bit_pattern.Set_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant these_boxed_float32s => "Flambda2_types.these_boxed_float32s".
(* flambda2_types.mli:492  val these_boxed_floats : Numeric_types.Float_by_bit_pattern.Set.t -> Alloc_mode.For_types.t -> t *)
Parameter these_boxed_floats : Numeric_types.Float_by_bit_pattern.Set_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant these_boxed_floats => "Flambda2_types.these_boxed_floats".
(* flambda2_types.mli:495  val these_boxed_int32s : Numeric_types.Int32.Set.t -> Alloc_mode.For_types.t -> t *)
Parameter these_boxed_int32s : Numeric_types.Int32.Set_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant these_boxed_int32s => "Flambda2_types.these_boxed_int32s".
(* flambda2_types.mli:498  val these_boxed_int64s : Numeric_types.Int64.Set.t -> Alloc_mode.For_types.t -> t *)
Parameter these_boxed_int64s : Numeric_types.Int64.Set_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant these_boxed_int64s => "Flambda2_types.these_boxed_int64s".
(* flambda2_types.mli:501  val these_boxed_nativeints : Targetint_32_64.Set.t -> Alloc_mode.For_types.t -> t *)
Parameter these_boxed_nativeints : Targetint_32_64.Set_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant these_boxed_nativeints => "Flambda2_types.these_boxed_nativeints".
(* flambda2_types.mli:506  val this_naked_immediate : Target_ocaml_int.t -> t *)
Parameter this_naked_immediate : Target_ocaml_int.t -> M t.
Extract Inlined Constant this_naked_immediate => "Flambda2_types.this_naked_immediate".
(* flambda2_types.mli:508  val this_naked_float32 : Numeric_types.Float32_by_bit_pattern.t -> t *)
Parameter this_naked_float32 : Numeric_types.Float32_by_bit_pattern.t -> M t.
Extract Inlined Constant this_naked_float32 => "Flambda2_types.this_naked_float32".
(* flambda2_types.mli:510  val this_naked_float : Numeric_types.Float_by_bit_pattern.t -> t *)
Parameter this_naked_float : Numeric_types.Float_by_bit_pattern.t -> M t.
Extract Inlined Constant this_naked_float => "Flambda2_types.this_naked_float".
(* flambda2_types.mli:512  val this_naked_int8 : Numeric_types.Int8.t -> t *)
Parameter this_naked_int8 : Numeric_types.Int8.t -> M t.
Extract Inlined Constant this_naked_int8 => "Flambda2_types.this_naked_int8".
(* flambda2_types.mli:514  val this_naked_int16 : Numeric_types.Int16.t -> t *)
Parameter this_naked_int16 : Numeric_types.Int16.t -> M t.
Extract Inlined Constant this_naked_int16 => "Flambda2_types.this_naked_int16".
(* flambda2_types.mli:516  val this_naked_int32 : Numeric_types.Int32.t -> t *)
Parameter this_naked_int32 : Numeric_types.Int32.t -> M t.
Extract Inlined Constant this_naked_int32 => "Flambda2_types.this_naked_int32".
(* flambda2_types.mli:518  val this_naked_int64 : Numeric_types.Int64.t -> t *)
Parameter this_naked_int64 : Numeric_types.Int64.t -> M t.
Extract Inlined Constant this_naked_int64 => "Flambda2_types.this_naked_int64".
(* flambda2_types.mli:520  val this_naked_nativeint : Targetint_32_64.t -> t *)
Parameter this_naked_nativeint : Targetint_32_64.t -> M t.
Extract Inlined Constant this_naked_nativeint => "Flambda2_types.this_naked_nativeint".
(* flambda2_types.mli:522  val this_naked_vec128 : Vector_types.Vec128.Bit_pattern.t -> t *)
Parameter this_naked_vec128 : Vector_types.Vec128.Bit_pattern.t -> M t.
Extract Inlined Constant this_naked_vec128 => "Flambda2_types.this_naked_vec128".
(* flambda2_types.mli:524  val this_naked_vec256 : Vector_types.Vec256.Bit_pattern.t -> t *)
Parameter this_naked_vec256 : Vector_types.Vec256.Bit_pattern.t -> M t.
Extract Inlined Constant this_naked_vec256 => "Flambda2_types.this_naked_vec256".
(* flambda2_types.mli:526  val this_naked_vec512 : Vector_types.Vec512.Bit_pattern.t -> t *)
Parameter this_naked_vec512 : Vector_types.Vec512.Bit_pattern.t -> M t.
Extract Inlined Constant this_naked_vec512 => "Flambda2_types.this_naked_vec512".
(* flambda2_types.mli:528  val this_naked_mask : Vector_types.Mask.Bit_pattern.t -> t *)
Parameter this_naked_mask : Vector_types.Mask.Bit_pattern.t -> M t.
Extract Inlined Constant this_naked_mask => "Flambda2_types.this_naked_mask".
(* flambda2_types.mli:530  val this_rec_info : Rec_info_expr.t -> t *)
Parameter this_rec_info : Rec_info_expr.t -> M t.
Extract Inlined Constant this_rec_info => "Flambda2_types.this_rec_info".
(* flambda2_types.mli:532  val these_naked_immediates : Target_ocaml_int.Set.t -> t *)
Parameter these_naked_immediates : Target_ocaml_int.Set_.t -> M t.
Extract Inlined Constant these_naked_immediates => "Flambda2_types.these_naked_immediates".
(* flambda2_types.mli:534  val these_naked_float32s : Numeric_types.Float32_by_bit_pattern.Set.t -> t *)
Parameter these_naked_float32s : Numeric_types.Float32_by_bit_pattern.Set_.t -> M t.
Extract Inlined Constant these_naked_float32s => "Flambda2_types.these_naked_float32s".
(* flambda2_types.mli:536  val these_naked_floats : Numeric_types.Float_by_bit_pattern.Set.t -> t *)
Parameter these_naked_floats : Numeric_types.Float_by_bit_pattern.Set_.t -> M t.
Extract Inlined Constant these_naked_floats => "Flambda2_types.these_naked_floats".
(* flambda2_types.mli:538  val these_naked_int8s : Numeric_types.Int8.Set.t -> t *)
Parameter these_naked_int8s : Numeric_types.Int8.Set_.t -> M t.
Extract Inlined Constant these_naked_int8s => "Flambda2_types.these_naked_int8s".
(* flambda2_types.mli:540  val these_naked_int16s : Numeric_types.Int16.Set.t -> t *)
Parameter these_naked_int16s : Numeric_types.Int16.Set_.t -> M t.
Extract Inlined Constant these_naked_int16s => "Flambda2_types.these_naked_int16s".
(* flambda2_types.mli:542  val these_naked_int32s : Numeric_types.Int32.Set.t -> t *)
Parameter these_naked_int32s : Numeric_types.Int32.Set_.t -> M t.
Extract Inlined Constant these_naked_int32s => "Flambda2_types.these_naked_int32s".
(* flambda2_types.mli:544  val these_naked_int64s : Numeric_types.Int64.Set.t -> t *)
Parameter these_naked_int64s : Numeric_types.Int64.Set_.t -> M t.
Extract Inlined Constant these_naked_int64s => "Flambda2_types.these_naked_int64s".
(* flambda2_types.mli:546  val these_naked_nativeints : Targetint_32_64.Set.t -> t *)
Parameter these_naked_nativeints : Targetint_32_64.Set_.t -> M t.
Extract Inlined Constant these_naked_nativeints => "Flambda2_types.these_naked_nativeints".
(* flambda2_types.mli:548  val boxed_float32_alias_to : naked_float32:Variable.t -> Alloc_mode.For_types.t -> t *)
Parameter boxed_float32_alias_to : Variable_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant boxed_float32_alias_to => "Flambda2_types.boxed_float32_alias_to".
(* flambda2_types.mli:551  val boxed_float_alias_to : naked_float:Variable.t -> Alloc_mode.For_types.t -> t *)
Parameter boxed_float_alias_to : Variable_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant boxed_float_alias_to => "Flambda2_types.boxed_float_alias_to".
(* flambda2_types.mli:559  val boxed_int32_alias_to : naked_int32:Variable.t -> Alloc_mode.For_types.t -> t *)
Parameter boxed_int32_alias_to : Variable_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant boxed_int32_alias_to => "Flambda2_types.boxed_int32_alias_to".
(* flambda2_types.mli:561  val boxed_int64_alias_to : naked_int64:Variable.t -> Alloc_mode.For_types.t -> t *)
Parameter boxed_int64_alias_to : Variable_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant boxed_int64_alias_to => "Flambda2_types.boxed_int64_alias_to".
(* flambda2_types.mli:563  val boxed_nativeint_alias_to : naked_nativeint:Variable.t -> Alloc_mode.For_types.t -> t *)
Parameter boxed_nativeint_alias_to : Variable_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant boxed_nativeint_alias_to => "Flambda2_types.boxed_nativeint_alias_to".
(* flambda2_types.mli:566  val boxed_vec128_alias_to : naked_vec128:Variable.t -> Alloc_mode.For_types.t -> t *)
Parameter boxed_vec128_alias_to : Variable_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant boxed_vec128_alias_to => "Flambda2_types.boxed_vec128_alias_to".
(* flambda2_types.mli:569  val boxed_vec256_alias_to : naked_vec256:Variable.t -> Alloc_mode.For_types.t -> t *)
Parameter boxed_vec256_alias_to : Variable_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant boxed_vec256_alias_to => "Flambda2_types.boxed_vec256_alias_to".
(* flambda2_types.mli:572  val boxed_vec512_alias_to : naked_vec512:Variable.t -> Alloc_mode.For_types.t -> t *)
Parameter boxed_vec512_alias_to : Variable_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant boxed_vec512_alias_to => "Flambda2_types.boxed_vec512_alias_to".
(* flambda2_types.mli:575  val boxed_mask_alias_to : naked_mask:Variable.t -> Alloc_mode.For_types.t -> t *)
Parameter boxed_mask_alias_to : Variable_.t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant boxed_mask_alias_to => "Flambda2_types.boxed_mask_alias_to".
(* flambda2_types.mli:577  val box_float32 : t -> Alloc_mode.For_types.t -> t *)
Parameter box_float32 : t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant box_float32 => "Flambda2_types.box_float32".
(* flambda2_types.mli:579  val box_float : t -> Alloc_mode.For_types.t -> t *)
Parameter box_float : t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant box_float => "Flambda2_types.box_float".
(* flambda2_types.mli:581  val box_int32 : t -> Alloc_mode.For_types.t -> t *)
Parameter box_int32 : t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant box_int32 => "Flambda2_types.box_int32".
(* flambda2_types.mli:583  val box_int64 : t -> Alloc_mode.For_types.t -> t *)
Parameter box_int64 : t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant box_int64 => "Flambda2_types.box_int64".
(* flambda2_types.mli:585  val box_nativeint : t -> Alloc_mode.For_types.t -> t *)
Parameter box_nativeint : t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant box_nativeint => "Flambda2_types.box_nativeint".
(* flambda2_types.mli:587  val box_vec128 : t -> Alloc_mode.For_types.t -> t *)
Parameter box_vec128 : t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant box_vec128 => "Flambda2_types.box_vec128".
(* flambda2_types.mli:589  val box_vec256 : t -> Alloc_mode.For_types.t -> t *)
Parameter box_vec256 : t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant box_vec256 => "Flambda2_types.box_vec256".
(* flambda2_types.mli:591  val box_vec512 : t -> Alloc_mode.For_types.t -> t *)
Parameter box_vec512 : t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant box_vec512 => "Flambda2_types.box_vec512".
(* flambda2_types.mli:593  val box_mask : t -> Alloc_mode.For_types.t -> t *)
Parameter box_mask : t -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant box_mask => "Flambda2_types.box_mask".
(* flambda2_types.mli:595  val tagged_immediate_alias_to : naked_immediate:Variable.t -> t *)
Parameter tagged_immediate_alias_to : Variable_.t -> M t.
Extract Inlined Constant tagged_immediate_alias_to => "Flambda2_types.tagged_immediate_alias_to".
(* flambda2_types.mli:597  val tag_immediate : t -> t *)
Parameter tag_immediate : t -> M t.
Extract Inlined Constant tag_immediate => "Flambda2_types.tag_immediate".
(* flambda2_types.mli:602  val immutable_block : machine_width:Target_system.Machine_width.t -> is_unique:bool -> Tag.t -> shape:Flambda_kind.Block_shape.t -> Alloc_mode.For_types.t -> fields:t list -> t *)
Parameter immutable_block : Target_system.Machine_width.t -> bool -> Tag.t -> Flambda_kind.Block_shape.t -> Alloc_mode.For_types.t -> list t -> M t.
Extract Inlined Constant immutable_block => "Flambda2_types.immutable_block".
(* flambda2_types.mli:614  val immutable_block_with_size_at_least : machine_width:Target_system.Machine_width.t -> tag:Tag.t Or_unknown.t -> n:Target_ocaml_int.t -> shape:Flambda_kind.Block_shape.t -> field_n_minus_one:Variable.t -> t *)
Parameter immutable_block_with_size_at_least : Target_system.Machine_width.t -> Or_unknown.t Tag.t -> Target_ocaml_int.t -> Flambda_kind.Block_shape.t -> Variable_.t -> M t.
Extract Inlined Constant immutable_block_with_size_at_least => "Flambda2_types.immutable_block_with_size_at_least".
(* flambda2_types.mli:622  val mutable_block : Alloc_mode.For_types.t -> t *)
Parameter mutable_block : Alloc_mode.For_types.t -> M t.
Extract Inlined Constant mutable_block => "Flambda2_types.mutable_block".
(* flambda2_types.mli:624  val variant : machine_width:Target_system.Machine_width.t -> const_ctors:t -> non_const_ctors:(Flambda_kind.Block_shape.t * t list) Tag.Scannable.Map.t -> Alloc_mode.For_types.t -> t *)
Parameter variant : Target_system.Machine_width.t -> t -> Tag.Scannable.Map.t (Flambda_kind.Block_shape.t * list t) -> Alloc_mode.For_types.t -> M t.
Extract Inlined Constant variant => "Flambda2_types.variant".
(* flambda2_types.mli:631  val this_immutable_string : string -> t *)
Parameter this_immutable_string : string -> M t.
Extract Inlined Constant this_immutable_string => "Flambda2_types.this_immutable_string".
(* flambda2_types.mli:633  val exactly_this_closure : Function_slot.t -> all_function_slots_in_set:Function_type.t Or_unknown.t Function_slot.Map.t -> all_closure_types_in_set:t Function_slot.Map.t -> all_value_slots_in_set:flambda_type Value_slot.Map.t -> Alloc_mode.For_types.t -> flambda_type *)
Parameter exactly_this_closure : Function_slot.t -> Function_slot.Map.t (Or_unknown.t Flambda2_types.Function_type.t) -> Function_slot.Map.t t -> Value_slot.Map.t flambda_type -> Alloc_mode.For_types.t -> M flambda_type.
Extract Inlined Constant exactly_this_closure => "Flambda2_types.exactly_this_closure".
(* flambda2_types.mli:641  val closure_with_at_least_these_function_slots : this_function_slot:Function_slot.t -> Simple.t Function_slot.Map.t -> flambda_type *)
Parameter closure_with_at_least_these_function_slots : Function_slot.t -> Function_slot.Map.t Simple.t -> M flambda_type.
Extract Inlined Constant closure_with_at_least_these_function_slots => "Flambda2_types.closure_with_at_least_these_function_slots".
(* flambda2_types.mli:646  val closure_with_at_least_this_value_slot : this_function_slot:Function_slot.t -> Value_slot.t -> value_slot_var:Variable.t -> value_slot_kind:Flambda_kind.t -> flambda_type *)
Parameter closure_with_at_least_this_value_slot : Function_slot.t -> Value_slot.t -> Variable_.t -> Flambda_kind.t -> M flambda_type.
Extract Inlined Constant closure_with_at_least_this_value_slot => "Flambda2_types.closure_with_at_least_this_value_slot".
(* flambda2_types.mli:653  val closure_with_at_least_these_value_slots : this_function_slot:Function_slot.t -> (Variable.t * Flambda_kind.t) Value_slot.Map.t -> flambda_type *)
Parameter closure_with_at_least_these_value_slots : Function_slot.t -> Value_slot.Map.t (Variable_.t * Flambda_kind.t) -> M flambda_type.
Extract Inlined Constant closure_with_at_least_these_value_slots => "Flambda2_types.closure_with_at_least_these_value_slots".
(* flambda2_types.mli:658  val array_of_length : element_kind:Flambda_kind.With_subkind.t Or_unknown_or_bottom.t -> length:flambda_type -> Alloc_mode.For_types.t -> flambda_type *)
Parameter array_of_length : Or_unknown_or_bottom.t Flambda_kind.With_subkind.t -> flambda_type -> Alloc_mode.For_types.t -> M flambda_type.
Extract Inlined Constant array_of_length => "Flambda2_types.array_of_length".
(* flambda2_types.mli:664  val mutable_array : element_kind:Flambda_kind.With_subkind.t Or_unknown_or_bottom.t -> length:flambda_type -> Alloc_mode.For_types.t -> flambda_type *)
Parameter mutable_array : Or_unknown_or_bottom.t Flambda_kind.With_subkind.t -> flambda_type -> Alloc_mode.For_types.t -> M flambda_type.
Extract Inlined Constant mutable_array => "Flambda2_types.mutable_array".
(* flambda2_types.mli:670  val immutable_array : element_kind:Flambda_kind.With_subkind.t Or_unknown_or_bottom.t -> fields:flambda_type list -> Alloc_mode.For_types.t -> machine_width:Target_system.Machine_width.t -> flambda_type *)
Parameter immutable_array : Or_unknown_or_bottom.t Flambda_kind.With_subkind.t -> list flambda_type -> Alloc_mode.For_types.t -> Target_system.Machine_width.t -> M flambda_type.
Extract Inlined Constant immutable_array => "Flambda2_types.immutable_array".
(* flambda2_types.mli:679  val alias_type_of : Flambda_kind.t -> Simple.t -> t *)
Parameter alias_type_of : Flambda_kind.t -> Simple.t -> M t.
Extract Inlined Constant alias_type_of => "Flambda2_types.alias_type_of".
(* flambda2_types.mli:682  val kind : t -> Flambda_kind.t *)
Parameter kind : t -> M Flambda_kind.t.
Extract Inlined Constant kind => "Flambda2_types.kind".
(* flambda2_types.mli:685  val unknown_types_from_arity : ?alloc_mode:Alloc_mode.For_types.t -> machine_width:Target_system.Machine_width.t -> _ Flambda_arity.t -> t list *)
Parameter unknown_types_from_arity : option Alloc_mode.For_types.t -> Target_system.Machine_width.t -> Flambda_arity.t -> M (list t).
Extract Inlined Constant unknown_types_from_arity => "(fun x__1 x__2 x__3 -> Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)".
(* flambda2_types.mli:695  val is_unknown : Typing_env.t -> t -> bool *)
Parameter is_unknown : Flambda2_types.Typing_env.t -> t -> M bool.
Extract Inlined Constant is_unknown => "Flambda2_types.is_unknown".
(* flambda2_types.mli:701  val is_unknown_maybe_null : Typing_env.t -> t -> bool *)
Parameter is_unknown_maybe_null : Flambda2_types.Typing_env.t -> t -> M bool.
Extract Inlined Constant is_unknown_maybe_null => "Flambda2_types.is_unknown_maybe_null".
(* flambda2_types.mli:703  val is_alias_to_a_symbol : t -> bool *)
Parameter is_alias_to_a_symbol : t -> M bool.
Extract Inlined Constant is_alias_to_a_symbol => "Flambda2_types.is_alias_to_a_symbol".
(* flambda2_types.mli:709  type 'a meet_shortcut = private | Known_result of 'a | Need_meet | Invalid *)
Inductive meet_shortcut (A : Type) : Type :=
| Known_result : A -> meet_shortcut A
| Need_meet : meet_shortcut A
| Invalid : meet_shortcut A.
Arguments Known_result {A}.
Arguments Need_meet {A}.
Arguments Invalid {A}.
Extract Inductive meet_shortcut => "Flambda2_types.meet_shortcut" [ "Flambda2_types.Known_result" "Flambda2_types.Need_meet" "(Flambda2_types.Invalid : (_) Flambda2_types.meet_shortcut)" ] "(fun f__1 f__2 f__3 x__0 -> match (x__0 : (_) Flambda2_types.meet_shortcut) with Flambda2_types.Known_result x__1 -> f__1 x__1 | Flambda2_types.Need_meet -> f__2 () | Flambda2_types.Invalid -> f__3 ())".
(* flambda2_types.mli:714  type 'a proof_of_property = private | Proved of 'a | Unknown *)
Inductive proof_of_property (A : Type) : Type :=
| Proved : A -> proof_of_property A
| Unknown : proof_of_property A.
Arguments Proved {A}.
Arguments Unknown {A}.
Extract Inductive proof_of_property => "Flambda2_types.proof_of_property" [ "Flambda2_types.Proved" "Flambda2_types.Unknown" ].
(* flambda2_types.mli:719  val prove_equals_tagged_immediates : Typing_env.t -> t -> Target_ocaml_int.Set.t proof_of_property *)
Parameter prove_equals_tagged_immediates : Flambda2_types.Typing_env.t -> t -> M (proof_of_property Target_ocaml_int.Set_.t).
Extract Inlined Constant prove_equals_tagged_immediates => "Flambda2_types.prove_equals_tagged_immediates".
(* flambda2_types.mli:722  val meet_equals_tagged_immediates : Typing_env.t -> t -> Target_ocaml_int.Set.t meet_shortcut *)
Parameter meet_equals_tagged_immediates : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Target_ocaml_int.Set_.t).
Extract Inlined Constant meet_equals_tagged_immediates => "Flambda2_types.meet_equals_tagged_immediates".
(* flambda2_types.mli:725  val meet_naked_immediates : Typing_env.t -> t -> Target_ocaml_int.Set.t meet_shortcut *)
Parameter meet_naked_immediates : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Target_ocaml_int.Set_.t).
Extract Inlined Constant meet_naked_immediates => "Flambda2_types.meet_naked_immediates".
(* flambda2_types.mli:731  val meet_naked_float32s : Typing_env.t -> t -> Numeric_types.Float32_by_bit_pattern.Set.t meet_shortcut *)
Parameter meet_naked_float32s : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Numeric_types.Float32_by_bit_pattern.Set_.t).
Extract Inlined Constant meet_naked_float32s => "Flambda2_types.meet_naked_float32s".
(* flambda2_types.mli:734  val meet_naked_floats : Typing_env.t -> t -> Numeric_types.Float_by_bit_pattern.Set.t meet_shortcut *)
Parameter meet_naked_floats : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Numeric_types.Float_by_bit_pattern.Set_.t).
Extract Inlined Constant meet_naked_floats => "Flambda2_types.meet_naked_floats".
(* flambda2_types.mli:737  val meet_naked_int8s : Typing_env.t -> t -> Numeric_types.Int8.Set.t meet_shortcut *)
Parameter meet_naked_int8s : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Numeric_types.Int8.Set_.t).
Extract Inlined Constant meet_naked_int8s => "Flambda2_types.meet_naked_int8s".
(* flambda2_types.mli:740  val meet_naked_int16s : Typing_env.t -> t -> Numeric_types.Int16.Set.t meet_shortcut *)
Parameter meet_naked_int16s : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Numeric_types.Int16.Set_.t).
Extract Inlined Constant meet_naked_int16s => "Flambda2_types.meet_naked_int16s".
(* flambda2_types.mli:743  val meet_naked_int32s : Typing_env.t -> t -> Numeric_types.Int32.Set.t meet_shortcut *)
Parameter meet_naked_int32s : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Numeric_types.Int32.Set_.t).
Extract Inlined Constant meet_naked_int32s => "Flambda2_types.meet_naked_int32s".
(* flambda2_types.mli:746  val meet_naked_int64s : Typing_env.t -> t -> Numeric_types.Int64.Set.t meet_shortcut *)
Parameter meet_naked_int64s : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Numeric_types.Int64.Set_.t).
Extract Inlined Constant meet_naked_int64s => "Flambda2_types.meet_naked_int64s".
(* flambda2_types.mli:749  val meet_naked_nativeints : Typing_env.t -> t -> Targetint_32_64.Set.t meet_shortcut *)
Parameter meet_naked_nativeints : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Targetint_32_64.Set_.t).
Extract Inlined Constant meet_naked_nativeints => "Flambda2_types.meet_naked_nativeints".
(* flambda2_types.mli:752  type variant_like_proof = private { const_ctors : Target_ocaml_int.Set.t Or_unknown.t; non_const_ctors_with_sizes : (Target_ocaml_int.t * Flambda_kind.Block_shape.t) Tag.Scannable.Map.t } *)
Record variant_like_proof : Type := { const_ctors : Or_unknown.t Target_ocaml_int.Set_.t; non_const_ctors_with_sizes : Tag.Scannable.Map.t (Target_ocaml_int.t * Flambda_kind.Block_shape.t) }.
(* flambda2_types.mli:758  val meet_variant_like : Typing_env.t -> t -> variant_like_proof meet_shortcut *)
Parameter meet_variant_like : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut variant_like_proof).
Extract Inlined Constant meet_variant_like => "Flambda2_types.meet_variant_like".
(* flambda2_types.mli:760  val prove_variant_like : Typing_env.t -> t -> variant_like_proof proof_of_property *)
Parameter prove_variant_like : Flambda2_types.Typing_env.t -> t -> M (proof_of_property variant_like_proof).
Extract Inlined Constant prove_variant_like => "Flambda2_types.prove_variant_like".
(* flambda2_types.mli:771  type boxed_or_tagged_number = private | Boxed of Alloc_mode.For_types.t * Flambda_kind.Boxable_number.t * t | Tagged_immediate *)
Inductive boxed_or_tagged_number : Type :=
| Boxed : Alloc_mode.For_types.t -> Flambda_kind.Boxable_number.t -> t -> boxed_or_tagged_number
| Tagged_immediate : boxed_or_tagged_number.
Extract Inductive boxed_or_tagged_number => "Flambda2_types.boxed_or_tagged_number" [ "Flambda2_types.Boxed" "Flambda2_types.Tagged_immediate" ].
(* flambda2_types.mli:775  val prove_is_a_boxed_or_tagged_number : Typing_env.t -> t -> boxed_or_tagged_number proof_of_property *)
Parameter prove_is_a_boxed_or_tagged_number : Flambda2_types.Typing_env.t -> t -> M (proof_of_property boxed_or_tagged_number).
Extract Inlined Constant prove_is_a_boxed_or_tagged_number => "Flambda2_types.prove_is_a_boxed_or_tagged_number".
(* flambda2_types.mli:780  val prove_is_a_tagged_immediate : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_tagged_immediate : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_tagged_immediate => "Flambda2_types.prove_is_a_tagged_immediate".
(* flambda2_types.mli:782  val prove_is_a_boxed_float32 : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_boxed_float32 : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_boxed_float32 => "Flambda2_types.prove_is_a_boxed_float32".
(* flambda2_types.mli:784  val prove_is_a_boxed_float : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_boxed_float : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_boxed_float => "Flambda2_types.prove_is_a_boxed_float".
(* flambda2_types.mli:786  val prove_is_a_boxed_int32 : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_boxed_int32 : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_boxed_int32 => "Flambda2_types.prove_is_a_boxed_int32".
(* flambda2_types.mli:788  val prove_is_a_boxed_int64 : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_boxed_int64 : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_boxed_int64 => "Flambda2_types.prove_is_a_boxed_int64".
(* flambda2_types.mli:790  val prove_is_a_boxed_nativeint : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_boxed_nativeint : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_boxed_nativeint => "Flambda2_types.prove_is_a_boxed_nativeint".
(* flambda2_types.mli:792  val prove_is_a_boxed_vec128 : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_boxed_vec128 : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_boxed_vec128 => "Flambda2_types.prove_is_a_boxed_vec128".
(* flambda2_types.mli:794  val prove_is_a_boxed_vec256 : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_boxed_vec256 : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_boxed_vec256 => "Flambda2_types.prove_is_a_boxed_vec256".
(* flambda2_types.mli:796  val prove_is_a_boxed_vec512 : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_boxed_vec512 : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_boxed_vec512 => "Flambda2_types.prove_is_a_boxed_vec512".
(* flambda2_types.mli:798  val prove_is_a_boxed_mask : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_a_boxed_mask : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_a_boxed_mask => "Flambda2_types.prove_is_a_boxed_mask".
(* flambda2_types.mli:800  val prove_is_or_is_not_a_boxed_float : Typing_env.t -> t -> bool proof_of_property *)
Parameter prove_is_or_is_not_a_boxed_float : Flambda2_types.Typing_env.t -> t -> M (proof_of_property bool).
Extract Inlined Constant prove_is_or_is_not_a_boxed_float => "Flambda2_types.prove_is_or_is_not_a_boxed_float".
(* flambda2_types.mli:803  val prove_unique_tag_and_size : Typing_env.t -> t -> (Tag.t * Flambda_kind.Block_shape.t * Target_ocaml_int.t) proof_of_property *)
Parameter prove_unique_tag_and_size : Flambda2_types.Typing_env.t -> t -> M (proof_of_property (tuple3 Tag.t Flambda_kind.Block_shape.t Target_ocaml_int.t)).
Extract Inlined Constant prove_unique_tag_and_size => "Flambda2_types.prove_unique_tag_and_size".
(* flambda2_types.mli:808  val prove_unique_fully_constructed_immutable_heap_block : Typing_env.t -> t -> (Tag.t * Flambda_kind.Block_shape.t * Target_ocaml_int.t * Simple.t list) proof_of_property *)
Parameter prove_unique_fully_constructed_immutable_heap_block : Flambda2_types.Typing_env.t -> t -> M (proof_of_property (tuple4 Tag.t Flambda_kind.Block_shape.t Target_ocaml_int.t (list Simple.t))).
Extract Inlined Constant prove_unique_fully_constructed_immutable_heap_block => "Flambda2_types.prove_unique_fully_constructed_immutable_heap_block".
(* flambda2_types.mli:814  val prove_is_int : Typing_env.t -> t -> bool proof_of_property *)
Parameter prove_is_int : Flambda2_types.Typing_env.t -> t -> M (proof_of_property bool).
Extract Inlined Constant prove_is_int => "Flambda2_types.prove_is_int".
(* flambda2_types.mli:817  val prove_is_not_a_pointer : Typing_env.t -> t -> bool proof_of_property *)
Parameter prove_is_not_a_pointer : Flambda2_types.Typing_env.t -> t -> M (proof_of_property bool).
Extract Inlined Constant prove_is_not_a_pointer => "Flambda2_types.prove_is_not_a_pointer".
(* flambda2_types.mli:820  val meet_is_flat_float_array : Typing_env.t -> t -> bool meet_shortcut *)
Parameter meet_is_flat_float_array : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut bool).
Extract Inlined Constant meet_is_flat_float_array => "Flambda2_types.meet_is_flat_float_array".
(* flambda2_types.mli:823  val meet_is_non_empty_naked_number_array : Flambda_kind.Naked_number_kind.t -> Typing_env.t -> t -> unit meet_shortcut *)
Parameter meet_is_non_empty_naked_number_array : Flambda_kind.Naked_number_kind.t -> Flambda2_types.Typing_env.t -> t -> M (meet_shortcut unit).
Extract Inlined Constant meet_is_non_empty_naked_number_array => "Flambda2_types.meet_is_non_empty_naked_number_array".
(* flambda2_types.mli:826  val prove_is_immediates_array : Typing_env.t -> t -> unit proof_of_property *)
Parameter prove_is_immediates_array : Flambda2_types.Typing_env.t -> t -> M (proof_of_property unit).
Extract Inlined Constant prove_is_immediates_array => "Flambda2_types.prove_is_immediates_array".
(* flambda2_types.mli:828  val meet_is_immutable_array : Typing_env.t -> t -> (Flambda_kind.With_subkind.t Or_unknown_or_bottom.t * t array * Alloc_mode.For_types.t) meet_shortcut *)
Parameter meet_is_immutable_array : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut (tuple3 (Or_unknown_or_bottom.t Flambda_kind.With_subkind.t) (array t) Alloc_mode.For_types.t)).
Extract Inlined Constant meet_is_immutable_array => "Flambda2_types.meet_is_immutable_array".
(* flambda2_types.mli:836  val prove_is_immutable_array : Typing_env.t -> t -> (Flambda_kind.With_subkind.t Or_unknown_or_bottom.t * t array * Alloc_mode.For_types.t) proof_of_property *)
Parameter prove_is_immutable_array : Flambda2_types.Typing_env.t -> t -> M (proof_of_property (tuple3 (Or_unknown_or_bottom.t Flambda_kind.With_subkind.t) (array t) Alloc_mode.For_types.t)).
Extract Inlined Constant prove_is_immutable_array => "Flambda2_types.prove_is_immutable_array".
(* flambda2_types.mli:844  val meet_single_closures_entry : Typing_env.t -> t -> (Function_slot.t * Alloc_mode.For_types.t * Closures_entry.t * Function_type.t) meet_shortcut *)
Parameter meet_single_closures_entry : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut (tuple4 Function_slot.t Alloc_mode.For_types.t Flambda2_types.Closures_entry.t Flambda2_types.Function_type.t)).
Extract Inlined Constant meet_single_closures_entry => "Flambda2_types.meet_single_closures_entry".
(* flambda2_types.mli:853  val prove_single_closures_entry : Typing_env.t -> t -> (Function_slot.t * Alloc_mode.For_types.t * Closures_entry.t * Function_type.t) proof_of_property *)
Parameter prove_single_closures_entry : Flambda2_types.Typing_env.t -> t -> M (proof_of_property (tuple4 Function_slot.t Alloc_mode.For_types.t Flambda2_types.Closures_entry.t Flambda2_types.Function_type.t)).
Extract Inlined Constant prove_single_closures_entry => "Flambda2_types.prove_single_closures_entry".
(* flambda2_types.mli:862  val meet_code_ids : Typing_env.t -> t -> Code_id.Set.t meet_shortcut *)
Parameter meet_code_ids : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Code_id.Set_.t).
Extract Inlined Constant meet_code_ids => "Flambda2_types.meet_code_ids".
(* flambda2_types.mli:866  val meet_strings : Typing_env.t -> t -> String_info.Set.t meet_shortcut *)
Parameter meet_strings : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut String_info.Set_.t).
Extract Inlined Constant meet_strings => "Flambda2_types.meet_strings".
(* flambda2_types.mli:868  val prove_strings : Typing_env.t -> t -> String_info.Set.t proof_of_property *)
Parameter prove_strings : Flambda2_types.Typing_env.t -> t -> M (proof_of_property String_info.Set_.t).
Extract Inlined Constant prove_strings => "Flambda2_types.prove_strings".
(* flambda2_types.mli:883  val meet_tagging_of_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_tagging_of_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_tagging_of_simple => "Flambda2_types.meet_tagging_of_simple".
(* flambda2_types.mli:886  val meet_boxed_float32_containing_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_boxed_float32_containing_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_boxed_float32_containing_simple => "Flambda2_types.meet_boxed_float32_containing_simple".
(* flambda2_types.mli:889  val meet_boxed_float_containing_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_boxed_float_containing_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_boxed_float_containing_simple => "Flambda2_types.meet_boxed_float_containing_simple".
(* flambda2_types.mli:892  val meet_boxed_int32_containing_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_boxed_int32_containing_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_boxed_int32_containing_simple => "Flambda2_types.meet_boxed_int32_containing_simple".
(* flambda2_types.mli:895  val meet_boxed_int64_containing_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_boxed_int64_containing_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_boxed_int64_containing_simple => "Flambda2_types.meet_boxed_int64_containing_simple".
(* flambda2_types.mli:898  val meet_boxed_nativeint_containing_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_boxed_nativeint_containing_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_boxed_nativeint_containing_simple => "Flambda2_types.meet_boxed_nativeint_containing_simple".
(* flambda2_types.mli:901  val meet_boxed_vec128_containing_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_boxed_vec128_containing_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_boxed_vec128_containing_simple => "Flambda2_types.meet_boxed_vec128_containing_simple".
(* flambda2_types.mli:904  val meet_boxed_vec256_containing_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_boxed_vec256_containing_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_boxed_vec256_containing_simple => "Flambda2_types.meet_boxed_vec256_containing_simple".
(* flambda2_types.mli:907  val meet_boxed_vec512_containing_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_boxed_vec512_containing_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_boxed_vec512_containing_simple => "Flambda2_types.meet_boxed_vec512_containing_simple".
(* flambda2_types.mli:910  val meet_boxed_mask_containing_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Simple.t meet_shortcut *)
Parameter meet_boxed_mask_containing_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_boxed_mask_containing_simple => "Flambda2_types.meet_boxed_mask_containing_simple".
(* flambda2_types.mli:913  val meet_block_field_simple : Typing_env.t -> min_name_mode:Name_mode.t -> field_kind:Flambda_kind.t -> t -> Target_ocaml_int.t -> Simple.t meet_shortcut *)
Parameter meet_block_field_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> Flambda_kind.t -> t -> Target_ocaml_int.t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_block_field_simple => "Flambda2_types.meet_block_field_simple".
(* flambda2_types.mli:921  val meet_project_value_slot_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Value_slot.t -> Simple.t meet_shortcut *)
Parameter meet_project_value_slot_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> Value_slot.t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_project_value_slot_simple => "Flambda2_types.meet_project_value_slot_simple".
(* flambda2_types.mli:928  val meet_project_function_slot_simple : Typing_env.t -> min_name_mode:Name_mode.t -> t -> Function_slot.t -> Simple.t meet_shortcut *)
Parameter meet_project_function_slot_simple : Flambda2_types.Typing_env.t -> Name_mode.t -> t -> Function_slot.t -> M (meet_shortcut Simple.t).
Extract Inlined Constant meet_project_function_slot_simple => "Flambda2_types.meet_project_function_slot_simple".
(* flambda2_types.mli:935  val meet_rec_info : Typing_env.t -> t -> Rec_info_expr.t meet_shortcut *)
Parameter meet_rec_info : Flambda2_types.Typing_env.t -> t -> M (meet_shortcut Rec_info_expr.t).
Extract Inlined Constant meet_rec_info => "Flambda2_types.meet_rec_info".
(* flambda2_types.mli:937  val prove_alloc_mode_of_boxed_number : Typing_env.t -> t -> Alloc_mode.For_types.t proof_of_property *)
Parameter prove_alloc_mode_of_boxed_number : Flambda2_types.Typing_env.t -> t -> M (proof_of_property Alloc_mode.For_types.t).
Extract Inlined Constant prove_alloc_mode_of_boxed_number => "Flambda2_types.prove_alloc_mode_of_boxed_number".
(* flambda2_types.mli:940  val prove_physical_equality : Typing_env.t -> t -> t -> bool proof_of_property *)
Parameter prove_physical_equality : Flambda2_types.Typing_env.t -> t -> t -> M (proof_of_property bool).
Extract Inlined Constant prove_physical_equality => "Flambda2_types.prove_physical_equality".
(* flambda2_types.mli:942  type to_lift = private | Immutable_block of { tag : Tag.Scannable.t; is_unique : bool; shape : Flambda_kind.Scannable_block_shape.t; fields : Simple.t list } | Boxed_float32 of Numeric_types.Float32_by_bit_pattern.t | Boxed_float of Numeric_types.Float_by_bit_pattern.t | Boxed_int32 of Numeric_types.Int32.t | Boxed_int64 of Numeric_types.Int64.t | Boxed_nativeint of Targetint_32_64.t | Boxed_ve... *)
Inductive to_lift : Type :=
| Immutable_block : Tag.Scannable.t -> bool -> Flambda_kind.Scannable_block_shape.t -> list Simple.t -> to_lift
| Boxed_float32 : Numeric_types.Float32_by_bit_pattern.t -> to_lift
| Boxed_float : Numeric_types.Float_by_bit_pattern.t -> to_lift
| Boxed_int32 : Numeric_types.Int32.t -> to_lift
| Boxed_int64 : Numeric_types.Int64.t -> to_lift
| Boxed_nativeint : Targetint_32_64.t -> to_lift
| Boxed_vec128 : Vector_types.Vec128.Bit_pattern.t -> to_lift
| Boxed_vec256 : Vector_types.Vec256.Bit_pattern.t -> to_lift
| Boxed_vec512 : Vector_types.Vec512.Bit_pattern.t -> to_lift
| Boxed_mask : Vector_types.Mask.Bit_pattern.t -> to_lift
| Immutable_float32_array : list Numeric_types.Float32_by_bit_pattern.t -> to_lift
| Immutable_float_array : list Numeric_types.Float_by_bit_pattern.t -> to_lift
| Immutable_int_array : list Target_ocaml_int.t -> to_lift
| Immutable_int8_array : list Numeric_types.Int8.t -> to_lift
| Immutable_int16_array : list Numeric_types.Int16.t -> to_lift
| Immutable_int32_array : list Int32.t -> to_lift
| Immutable_int64_array : list Int64.t -> to_lift
| Immutable_nativeint_array : list Targetint_32_64.t -> to_lift
| Immutable_vec128_array : list Vector_types.Vec128.Bit_pattern.t -> to_lift
| Immutable_vec256_array : list Vector_types.Vec256.Bit_pattern.t -> to_lift
| Immutable_vec512_array : list Vector_types.Vec512.Bit_pattern.t -> to_lift
| Immutable_mask_array : list Vector_types.Mask.Bit_pattern.t -> to_lift
| Immutable_value_array : list Simple.t -> to_lift
| Empty_array : Empty_array_kind.t -> to_lift.
Extract Inductive to_lift => "Flambda2_types.to_lift" [ "(fun (x__1, x__2, x__3, x__4) -> (Flambda2_types.Immutable_block { tag = x__1; is_unique = x__2; shape = x__3; fields = x__4 } : Flambda2_types.to_lift))" "Flambda2_types.Boxed_float32" "Flambda2_types.Boxed_float" "Flambda2_types.Boxed_int32" "Flambda2_types.Boxed_int64" "Flambda2_types.Boxed_nativeint" "Flambda2_types.Boxed_vec128" "Flambda2_types.Boxed_vec256" "Flambda2_types.Boxed_vec512" "Flambda2_types.Boxed_mask" "(fun x__1 -> (Flambda2_types.Immutable_float32_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_float_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_int_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_int8_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_int16_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_int32_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_int64_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_nativeint_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_vec128_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_vec256_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_vec512_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_mask_array { fields = x__1 } : Flambda2_types.to_lift))" "(fun x__1 -> (Flambda2_types.Immutable_value_array { fields = x__1 } : Flambda2_types.to_lift))" "Flambda2_types.Empty_array" ] "(fun f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 f__9 f__10 f__11 f__12 f__13 f__14 f__15 f__16 f__17 f__18 f__19 f__20 f__21 f__22 f__23 f__24 x__0 -> match (x__0 : Flambda2_types.to_lift) with Flambda2_types.Immutable_block { tag = x__1; is_unique = x__2; shape = x__3; fields = x__4 } -> f__1 x__1 x__2 x__3 x__4 | Flambda2_types.Boxed_float32 x__1 -> f__2 x__1 | Flambda2_types.Boxed_float x__1 -> f__3 x__1 | Flambda2_types.Boxed_int32 x__1 -> f__4 x__1 | Flambda2_types.Boxed_int64 x__1 -> f__5 x__1 | Flambda2_types.Boxed_nativeint x__1 -> f__6 x__1 | Flambda2_types.Boxed_vec128 x__1 -> f__7 x__1 | Flambda2_types.Boxed_vec256 x__1 -> f__8 x__1 | Flambda2_types.Boxed_vec512 x__1 -> f__9 x__1 | Flambda2_types.Boxed_mask x__1 -> f__10 x__1 | Flambda2_types.Immutable_float32_array { fields = x__1 } -> f__11 x__1 | Flambda2_types.Immutable_float_array { fields = x__1 } -> f__12 x__1 | Flambda2_types.Immutable_int_array { fields = x__1 } -> f__13 x__1 | Flambda2_types.Immutable_int8_array { fields = x__1 } -> f__14 x__1 | Flambda2_types.Immutable_int16_array { fields = x__1 } -> f__15 x__1 | Flambda2_types.Immutable_int32_array { fields = x__1 } -> f__16 x__1 | Flambda2_types.Immutable_int64_array { fields = x__1 } -> f__17 x__1 | Flambda2_types.Immutable_nativeint_array { fields = x__1 } -> f__18 x__1 | Flambda2_types.Immutable_vec128_array { fields = x__1 } -> f__19 x__1 | Flambda2_types.Immutable_vec256_array { fields = x__1 } -> f__20 x__1 | Flambda2_types.Immutable_vec512_array { fields = x__1 } -> f__21 x__1 | Flambda2_types.Immutable_mask_array { fields = x__1 } -> f__22 x__1 | Flambda2_types.Immutable_value_array { fields = x__1 } -> f__23 x__1 | Flambda2_types.Empty_array x__1 -> f__24 x__1)".
(* flambda2_types.mli:978  type reification_result = private | Lift of to_lift | Simple of Simple.t | Cannot_reify | Invalid *)
Inductive reification_result : Type :=
| Lift : to_lift -> reification_result
| Simple : Simple.t -> reification_result
| Cannot_reify : reification_result
| Invalid_ : reification_result.
Extract Inductive reification_result => "Flambda2_types.reification_result" [ "Flambda2_types.Lift" "Flambda2_types.Simple" "Flambda2_types.Cannot_reify" "Flambda2_types.Invalid" ].
(* flambda2_types.mli:984  val reify : allowed_if_free_vars_defined_in:Typing_env.t -> var_is_defined_at_toplevel:(Variable.t -> bool) -> var_is_symbol_projection:(Variable.t -> bool) -> Typing_env.t -> t -> reification_result *)
Parameter reify : Flambda2_types.Typing_env.t -> (Variable_.t -> M bool) -> (Variable_.t -> M bool) -> Flambda2_types.Typing_env.t -> t -> M reification_result.
Extract Inlined Constant reify => "Flambda2_types.reify".
(* flambda2_types.mli:992  val never_holds_locally_allocated_values : Typing_env.t -> Variable.t -> unit proof_of_property *)
Parameter never_holds_locally_allocated_values : Flambda2_types.Typing_env.t -> Variable_.t -> M (proof_of_property unit).
Extract Inlined Constant never_holds_locally_allocated_values => "Flambda2_types.never_holds_locally_allocated_values".
(* flambda2_types.mli:995  val remove_outermost_alias : Typing_env.t -> t -> t *)
Parameter remove_outermost_alias : Flambda2_types.Typing_env.t -> t -> M t.
Extract Inlined Constant remove_outermost_alias => "Flambda2_types.remove_outermost_alias".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Flambda2_types. End Flambda2_types.
