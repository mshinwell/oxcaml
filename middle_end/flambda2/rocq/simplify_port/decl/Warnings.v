(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Pierre Weis && Damien Doligez, INRIA Rocquencourt          *)
(*                                                                        *)
(*   Copyright 1998 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Warnings], after its interface
   utils/warnings.mli
   (Git blob ab4998e25334b508d4fe7c8f516ac9ade5d6e4f4). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format_doc.

(* warnings.mli:23  type loc = { loc_start: Lexing.position; loc_end: Lexing.position; loc_ghost: bool; } *)
Parameter loc : Type.
Extract Inlined Constant loc => "Warnings.loc".
(* warnings.mli:32  type field_usage_warning = | Unused | Not_read | Not_mutated *)
Parameter field_usage_warning : Type.
Extract Inlined Constant field_usage_warning => "Warnings.field_usage_warning".
(* warnings.mli:37  type constructor_usage_warning = | Unused | Not_constructed | Only_exported_private *)
Parameter constructor_usage_warning : Type.
Extract Inlined Constant constructor_usage_warning => "Warnings.constructor_usage_warning".
(* warnings.mli:42  type upstream_compat_warning = | Non_value_sort of string | Unboxed_attribute of string | Immediate_void_variant | Separability_check | Unpacked_attribute *)
Parameter upstream_compat_warning : Type.
Extract Inlined Constant upstream_compat_warning => "Warnings.upstream_compat_warning".
(* warnings.mli:49  type name_out_of_scope_warning = | Name of string | Fields of { record_form : string ; fields : string list } *)
Parameter name_out_of_scope_warning : Type.
Extract Inlined Constant name_out_of_scope_warning => "Warnings.name_out_of_scope_warning".
(* warnings.mli:53  type type_declaration_usage_warning = | Declaration | Alias *)
Parameter type_declaration_usage_warning : Type.
Extract Inlined Constant type_declaration_usage_warning => "Warnings.type_declaration_usage_warning".
(* warnings.mli:57  type redundant_modifier_reason = | Default_bound | Implied_by of string *)
Parameter redundant_modifier_reason : Type.
Extract Inlined Constant redundant_modifier_reason => "Warnings.redundant_modifier_reason".
(* warnings.mli:61  type t = | Comment_start ( * 1 * ) | Comment_not_end ( * 2 * ) ( *| Deprecated --> alert 'deprecated' * ) ( * 3 * ) | Fragile_match of string ( * 4 * ) | Ignored_partial_application ( * 5 * ) | Labels_omitted of string list ( * 6 * ) | Method_override of string list ( * 7 * ) | Partial_match of Format_doc.t ( * 8 * ) | Missing_record_field_pattern of { form : string ; unbound : string } ( * 9 *... *)
Inductive t : Type :=
| Comment_start : t
| Comment_not_end : t
| Fragile_match : string -> t
| Ignored_partial_application : t
| Labels_omitted : list string -> t
| Method_override : list string -> t
| Partial_match : Format_doc.t -> t
| Missing_record_field_pattern : string -> string -> t
| Non_unit_statement : t
| Redundant_case : t
| Redundant_subpat : t
| Instance_variable_override : list string -> t
| Illegal_backslash : t
| Implicit_public_methods : list string -> t
| Unerasable_optional_argument : t
| Undeclared_virtual_method : string -> t
| Not_principal : Format_doc.t -> t
| Non_principal_labels : string -> t
| Ignored_extra_argument : t
| Nonreturning_statement : t
| Preprocessor : string -> t
| Useless_record_with : string -> t
| Bad_module_name : string -> t
| All_clauses_guarded : t
| Unused_var : string -> bool -> t
| Unused_var_strict : string -> bool -> t
| Wildcard_arg_to_constant_constr : t
| Eol_in_string : t
| Duplicate_definitions : string -> string -> string -> string -> t
| Unused_value_declaration : string -> t
| Unused_open : string -> t
| Unused_type_declaration : string -> type_declaration_usage_warning -> t
| Unused_for_index : string -> t
| Unused_ancestor : string -> t
| Unused_constructor : string -> constructor_usage_warning -> t
| Unused_extension : string -> bool -> constructor_usage_warning -> t
| Unused_rec_flag : t
| Name_out_of_scope : string -> name_out_of_scope_warning -> t
| Ambiguous_name : list string -> list string -> bool -> string -> t
| Disambiguated_name : string -> t
| Nonoptional_label : string -> t
| Open_shadow_identifier : string -> string -> t
| Open_shadow_label_constructor : string -> string -> t
| Bad_env_variable : string -> string -> t
| Attribute_payload : string -> string -> t
| Eliminated_optional_arguments : list string -> t
| No_cmi_file : string -> option string -> t
| Unexpected_docstring : bool -> t
| Wrong_tailcall_expectation : bool -> t
| Fragile_literal_pattern : t
| Misplaced_attribute : string -> t
| Duplicated_attribute : string -> t
| Inlining_impossible : string -> t
| Unreachable_case : t
| Ambiguous_var_in_pattern_guard : list string -> t
| No_cmx_file : string -> string -> t
| Flambda_assignment_to_non_mutable_value : t
| Unused_module : string -> t
| Unboxable_type_in_prim_decl : string -> t
| Constraint_on_gadt : t
| Erroneous_printed_signature : string -> t
| Unsafe_array_syntax_without_parsing : t
| Redefining_unit : string -> t
| Unused_open_bang : string -> t
| Unused_functor_parameter : string -> t
| Match_on_mutable_state_prevent_uncurry : t
| Unused_field : string -> string -> field_usage_warning -> t
| Missing_mli : t
| Unused_tmc_attribute : t
| Tmc_breaks_tailcall : t
| Generative_application_expects_unit : t
| Degraded_to_partial_match : t
| Unnecessarily_partial_tuple_pattern : t
| Imprecise_kind_annotation : string -> string -> string -> t
| Untagged_external_small_int_return : t
| Redundant_kind_modifier : string -> t
| Ignored_kind_modifier : string -> string -> t
| Unmutated_mutable : string -> t
| Incompatible_with_upstream : upstream_compat_warning -> t
| Unerasable_position_argument : t
| Probe_name_too_long : string -> t
| Unused_kind_declaration : string -> t
| Zero_alloc_all_hidden_arrow : string -> t
| Unchecked_zero_alloc_attribute : t
| Unboxing_impossible : t
| Redundant_modifier : string -> redundant_modifier_reason -> t
| Atomic_float_record_boxed : t
| Implied_attribute : string -> string -> t
| Use_during_borrowing : t
| Lpoly_in_letrec : t
| Useless_valpoly : t
| Redundant_modality : t
| Unused_alert_disable : string -> t.
Extract Inductive t => "Warnings.t" [ "Warnings.Comment_start" "Warnings.Comment_not_end" "Warnings.Fragile_match" "Warnings.Ignored_partial_application" "Warnings.Labels_omitted" "Warnings.Method_override" "Warnings.Partial_match" "(fun (x__1, x__2) -> (Warnings.Missing_record_field_pattern { form = x__1; unbound = x__2 } : Warnings.t))" "Warnings.Non_unit_statement" "Warnings.Redundant_case" "Warnings.Redundant_subpat" "Warnings.Instance_variable_override" "Warnings.Illegal_backslash" "Warnings.Implicit_public_methods" "Warnings.Unerasable_optional_argument" "Warnings.Undeclared_virtual_method" "Warnings.Not_principal" "Warnings.Non_principal_labels" "Warnings.Ignored_extra_argument" "Warnings.Nonreturning_statement" "Warnings.Preprocessor" "Warnings.Useless_record_with" "Warnings.Bad_module_name" "Warnings.All_clauses_guarded" "(fun (x__1, x__2) -> (Warnings.Unused_var { name = x__1; mutated = x__2 } : Warnings.t))" "(fun (x__1, x__2) -> (Warnings.Unused_var_strict { name = x__1; mutated = x__2 } : Warnings.t))" "Warnings.Wildcard_arg_to_constant_constr" "Warnings.Eol_in_string" "Warnings.Duplicate_definitions" "Warnings.Unused_value_declaration" "Warnings.Unused_open" "Warnings.Unused_type_declaration" "Warnings.Unused_for_index" "Warnings.Unused_ancestor" "Warnings.Unused_constructor" "Warnings.Unused_extension" "Warnings.Unused_rec_flag" "Warnings.Name_out_of_scope" "Warnings.Ambiguous_name" "Warnings.Disambiguated_name" "Warnings.Nonoptional_label" "Warnings.Open_shadow_identifier" "Warnings.Open_shadow_label_constructor" "Warnings.Bad_env_variable" "Warnings.Attribute_payload" "Warnings.Eliminated_optional_arguments" "Warnings.No_cmi_file" "Warnings.Unexpected_docstring" "Warnings.Wrong_tailcall_expectation" "Warnings.Fragile_literal_pattern" "Warnings.Misplaced_attribute" "Warnings.Duplicated_attribute" "Warnings.Inlining_impossible" "Warnings.Unreachable_case" "Warnings.Ambiguous_var_in_pattern_guard" "(fun (x__1, x__2) -> (Warnings.No_cmx_file { missing_extension = x__1; module_name = x__2 } : Warnings.t))" "Warnings.Flambda_assignment_to_non_mutable_value" "Warnings.Unused_module" "Warnings.Unboxable_type_in_prim_decl" "Warnings.Constraint_on_gadt" "Warnings.Erroneous_printed_signature" "Warnings.Unsafe_array_syntax_without_parsing" "Warnings.Redefining_unit" "Warnings.Unused_open_bang" "Warnings.Unused_functor_parameter" "Warnings.Match_on_mutable_state_prevent_uncurry" "(fun (x__1, x__2, x__3) -> (Warnings.Unused_field { form = x__1; field = x__2; complaint = x__3 } : Warnings.t))" "Warnings.Missing_mli" "Warnings.Unused_tmc_attribute" "Warnings.Tmc_breaks_tailcall" "Warnings.Generative_application_expects_unit" "Warnings.Degraded_to_partial_match" "Warnings.Unnecessarily_partial_tuple_pattern" "(fun (x__1, x__2, x__3) -> (Warnings.Imprecise_kind_annotation { name = x__1; annotated = x__2; inferred = x__3 } : Warnings.t))" "Warnings.Untagged_external_small_int_return" "Warnings.Redundant_kind_modifier" "(fun (x__1, x__2) -> (Warnings.Ignored_kind_modifier { modifier = x__1; abbrev = x__2 } : Warnings.t))" "Warnings.Unmutated_mutable" "Warnings.Incompatible_with_upstream" "Warnings.Unerasable_position_argument" "Warnings.Probe_name_too_long" "Warnings.Unused_kind_declaration" "Warnings.Zero_alloc_all_hidden_arrow" "Warnings.Unchecked_zero_alloc_attribute" "Warnings.Unboxing_impossible" "(fun (x__1, x__2) -> (Warnings.Redundant_modifier { modifier = x__1; reason = x__2 } : Warnings.t))" "Warnings.Atomic_float_record_boxed" "(fun (x__1, x__2) -> (Warnings.Implied_attribute { implying = x__1; implied = x__2 } : Warnings.t))" "Warnings.Use_during_borrowing" "Warnings.Lpoly_in_letrec" "Warnings.Useless_valpoly" "Warnings.Redundant_modality" "Warnings.Unused_alert_disable" ] "(fun f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 f__9 f__10 f__11 f__12 f__13 f__14 f__15 f__16 f__17 f__18 f__19 f__20 f__21 f__22 f__23 f__24 f__25 f__26 f__27 f__28 f__29 f__30 f__31 f__32 f__33 f__34 f__35 f__36 f__37 f__38 f__39 f__40 f__41 f__42 f__43 f__44 f__45 f__46 f__47 f__48 f__49 f__50 f__51 f__52 f__53 f__54 f__55 f__56 f__57 f__58 f__59 f__60 f__61 f__62 f__63 f__64 f__65 f__66 f__67 f__68 f__69 f__70 f__71 f__72 f__73 f__74 f__75 f__76 f__77 f__78 f__79 f__80 f__81 f__82 f__83 f__84 f__85 f__86 f__87 f__88 f__89 f__90 f__91 f__92 f__93 x__0 -> match (x__0 : Warnings.t) with Warnings.Comment_start -> f__1 () | Warnings.Comment_not_end -> f__2 () | Warnings.Fragile_match x__1 -> f__3 x__1 | Warnings.Ignored_partial_application -> f__4 () | Warnings.Labels_omitted x__1 -> f__5 x__1 | Warnings.Method_override x__1 -> f__6 x__1 | Warnings.Partial_match x__1 -> f__7 x__1 | Warnings.Missing_record_field_pattern { form = x__1; unbound = x__2 } -> f__8 x__1 x__2 | Warnings.Non_unit_statement -> f__9 () | Warnings.Redundant_case -> f__10 () | Warnings.Redundant_subpat -> f__11 () | Warnings.Instance_variable_override x__1 -> f__12 x__1 | Warnings.Illegal_backslash -> f__13 () | Warnings.Implicit_public_methods x__1 -> f__14 x__1 | Warnings.Unerasable_optional_argument -> f__15 () | Warnings.Undeclared_virtual_method x__1 -> f__16 x__1 | Warnings.Not_principal x__1 -> f__17 x__1 | Warnings.Non_principal_labels x__1 -> f__18 x__1 | Warnings.Ignored_extra_argument -> f__19 () | Warnings.Nonreturning_statement -> f__20 () | Warnings.Preprocessor x__1 -> f__21 x__1 | Warnings.Useless_record_with x__1 -> f__22 x__1 | Warnings.Bad_module_name x__1 -> f__23 x__1 | Warnings.All_clauses_guarded -> f__24 () | Warnings.Unused_var { name = x__1; mutated = x__2 } -> f__25 x__1 x__2 | Warnings.Unused_var_strict { name = x__1; mutated = x__2 } -> f__26 x__1 x__2 | Warnings.Wildcard_arg_to_constant_constr -> f__27 () | Warnings.Eol_in_string -> f__28 () | Warnings.Duplicate_definitions (x__1, x__2, x__3, x__4) -> f__29 x__1 x__2 x__3 x__4 | Warnings.Unused_value_declaration x__1 -> f__30 x__1 | Warnings.Unused_open x__1 -> f__31 x__1 | Warnings.Unused_type_declaration (x__1, x__2) -> f__32 x__1 x__2 | Warnings.Unused_for_index x__1 -> f__33 x__1 | Warnings.Unused_ancestor x__1 -> f__34 x__1 | Warnings.Unused_constructor (x__1, x__2) -> f__35 x__1 x__2 | Warnings.Unused_extension (x__1, x__2, x__3) -> f__36 x__1 x__2 x__3 | Warnings.Unused_rec_flag -> f__37 () | Warnings.Name_out_of_scope (x__1, x__2) -> f__38 x__1 x__2 | Warnings.Ambiguous_name (x__1, x__2, x__3, x__4) -> f__39 x__1 x__2 x__3 x__4 | Warnings.Disambiguated_name x__1 -> f__40 x__1 | Warnings.Nonoptional_label x__1 -> f__41 x__1 | Warnings.Open_shadow_identifier (x__1, x__2) -> f__42 x__1 x__2 | Warnings.Open_shadow_label_constructor (x__1, x__2) -> f__43 x__1 x__2 | Warnings.Bad_env_variable (x__1, x__2) -> f__44 x__1 x__2 | Warnings.Attribute_payload (x__1, x__2) -> f__45 x__1 x__2 | Warnings.Eliminated_optional_arguments x__1 -> f__46 x__1 | Warnings.No_cmi_file (x__1, x__2) -> f__47 x__1 x__2 | Warnings.Unexpected_docstring x__1 -> f__48 x__1 | Warnings.Wrong_tailcall_expectation x__1 -> f__49 x__1 | Warnings.Fragile_literal_pattern -> f__50 () | Warnings.Misplaced_attribute x__1 -> f__51 x__1 | Warnings.Duplicated_attribute x__1 -> f__52 x__1 | Warnings.Inlining_impossible x__1 -> f__53 x__1 | Warnings.Unreachable_case -> f__54 () | Warnings.Ambiguous_var_in_pattern_guard x__1 -> f__55 x__1 | Warnings.No_cmx_file { missing_extension = x__1; module_name = x__2 } -> f__56 x__1 x__2 | Warnings.Flambda_assignment_to_non_mutable_value -> f__57 () | Warnings.Unused_module x__1 -> f__58 x__1 | Warnings.Unboxable_type_in_prim_decl x__1 -> f__59 x__1 | Warnings.Constraint_on_gadt -> f__60 () | Warnings.Erroneous_printed_signature x__1 -> f__61 x__1 | Warnings.Unsafe_array_syntax_without_parsing -> f__62 () | Warnings.Redefining_unit x__1 -> f__63 x__1 | Warnings.Unused_open_bang x__1 -> f__64 x__1 | Warnings.Unused_functor_parameter x__1 -> f__65 x__1 | Warnings.Match_on_mutable_state_prevent_uncurry -> f__66 () | Warnings.Unused_field { form = x__1; field = x__2; complaint = x__3 } -> f__67 x__1 x__2 x__3 | Warnings.Missing_mli -> f__68 () | Warnings.Unused_tmc_attribute -> f__69 () | Warnings.Tmc_breaks_tailcall -> f__70 () | Warnings.Generative_application_expects_unit -> f__71 () | Warnings.Degraded_to_partial_match -> f__72 () | Warnings.Unnecessarily_partial_tuple_pattern -> f__73 () | Warnings.Imprecise_kind_annotation { name = x__1; annotated = x__2; inferred = x__3 } -> f__74 x__1 x__2 x__3 | Warnings.Untagged_external_small_int_return -> f__75 () | Warnings.Redundant_kind_modifier x__1 -> f__76 x__1 | Warnings.Ignored_kind_modifier { modifier = x__1; abbrev = x__2 } -> f__77 x__1 x__2 | Warnings.Unmutated_mutable x__1 -> f__78 x__1 | Warnings.Incompatible_with_upstream x__1 -> f__79 x__1 | Warnings.Unerasable_position_argument -> f__80 () | Warnings.Probe_name_too_long x__1 -> f__81 x__1 | Warnings.Unused_kind_declaration x__1 -> f__82 x__1 | Warnings.Zero_alloc_all_hidden_arrow x__1 -> f__83 x__1 | Warnings.Unchecked_zero_alloc_attribute -> f__84 () | Warnings.Unboxing_impossible -> f__85 () | Warnings.Redundant_modifier { modifier = x__1; reason = x__2 } -> f__86 x__1 x__2 | Warnings.Atomic_float_record_boxed -> f__87 () | Warnings.Implied_attribute { implying = x__1; implied = x__2 } -> f__88 x__1 x__2 | Warnings.Use_during_borrowing -> f__89 () | Warnings.Lpoly_in_letrec -> f__90 () | Warnings.Useless_valpoly -> f__91 () | Warnings.Redundant_modality -> f__92 () | Warnings.Unused_alert_disable x__1 -> f__93 x__1)".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Warnings. End Warnings.
