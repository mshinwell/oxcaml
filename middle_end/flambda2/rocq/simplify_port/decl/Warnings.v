(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Warnings], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

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
(* PORT-GAP(type): the name of the field [name] is taken in Rocq: abstract, with a maker for each constructor and one eliminator. *)
Parameter t : Type.
Extract Inlined Constant t => "Warnings.t".
Parameter mk_Comment_start : t.
Extract Inlined Constant mk_Comment_start => "Warnings.Comment_start".
Parameter mk_Comment_not_end : t.
Extract Inlined Constant mk_Comment_not_end => "Warnings.Comment_not_end".
Parameter mk_Fragile_match : string -> t.
Extract Inlined Constant mk_Fragile_match => "(fun x__1 -> Warnings.Fragile_match x__1)".
Parameter mk_Ignored_partial_application : t.
Extract Inlined Constant mk_Ignored_partial_application => "Warnings.Ignored_partial_application".
Parameter mk_Labels_omitted : list string -> t.
Extract Inlined Constant mk_Labels_omitted => "(fun x__1 -> Warnings.Labels_omitted x__1)".
Parameter mk_Method_override : list string -> t.
Extract Inlined Constant mk_Method_override => "(fun x__1 -> Warnings.Method_override x__1)".
Parameter mk_Partial_match : Format_doc.t -> t.
Extract Inlined Constant mk_Partial_match => "(fun x__1 -> Warnings.Partial_match x__1)".
Parameter mk_Missing_record_field_pattern : string -> string -> t.
Extract Inlined Constant mk_Missing_record_field_pattern => "(fun x__1 x__2 -> Warnings.Missing_record_field_pattern { form = x__1; unbound = x__2 })".
Parameter mk_Non_unit_statement : t.
Extract Inlined Constant mk_Non_unit_statement => "Warnings.Non_unit_statement".
Parameter mk_Redundant_case : t.
Extract Inlined Constant mk_Redundant_case => "Warnings.Redundant_case".
Parameter mk_Redundant_subpat : t.
Extract Inlined Constant mk_Redundant_subpat => "Warnings.Redundant_subpat".
Parameter mk_Instance_variable_override : list string -> t.
Extract Inlined Constant mk_Instance_variable_override => "(fun x__1 -> Warnings.Instance_variable_override x__1)".
Parameter mk_Illegal_backslash : t.
Extract Inlined Constant mk_Illegal_backslash => "Warnings.Illegal_backslash".
Parameter mk_Implicit_public_methods : list string -> t.
Extract Inlined Constant mk_Implicit_public_methods => "(fun x__1 -> Warnings.Implicit_public_methods x__1)".
Parameter mk_Unerasable_optional_argument : t.
Extract Inlined Constant mk_Unerasable_optional_argument => "Warnings.Unerasable_optional_argument".
Parameter mk_Undeclared_virtual_method : string -> t.
Extract Inlined Constant mk_Undeclared_virtual_method => "(fun x__1 -> Warnings.Undeclared_virtual_method x__1)".
Parameter mk_Not_principal : Format_doc.t -> t.
Extract Inlined Constant mk_Not_principal => "(fun x__1 -> Warnings.Not_principal x__1)".
Parameter mk_Non_principal_labels : string -> t.
Extract Inlined Constant mk_Non_principal_labels => "(fun x__1 -> Warnings.Non_principal_labels x__1)".
Parameter mk_Ignored_extra_argument : t.
Extract Inlined Constant mk_Ignored_extra_argument => "Warnings.Ignored_extra_argument".
Parameter mk_Nonreturning_statement : t.
Extract Inlined Constant mk_Nonreturning_statement => "Warnings.Nonreturning_statement".
Parameter mk_Preprocessor : string -> t.
Extract Inlined Constant mk_Preprocessor => "(fun x__1 -> Warnings.Preprocessor x__1)".
Parameter mk_Useless_record_with : string -> t.
Extract Inlined Constant mk_Useless_record_with => "(fun x__1 -> Warnings.Useless_record_with x__1)".
Parameter mk_Bad_module_name : string -> t.
Extract Inlined Constant mk_Bad_module_name => "(fun x__1 -> Warnings.Bad_module_name x__1)".
Parameter mk_All_clauses_guarded : t.
Extract Inlined Constant mk_All_clauses_guarded => "Warnings.All_clauses_guarded".
Parameter mk_Unused_var : string -> bool -> t.
Extract Inlined Constant mk_Unused_var => "(fun x__1 x__2 -> Warnings.Unused_var { name = x__1; mutated = x__2 })".
Parameter mk_Unused_var_strict : string -> bool -> t.
Extract Inlined Constant mk_Unused_var_strict => "(fun x__1 x__2 -> Warnings.Unused_var_strict { name = x__1; mutated = x__2 })".
Parameter mk_Wildcard_arg_to_constant_constr : t.
Extract Inlined Constant mk_Wildcard_arg_to_constant_constr => "Warnings.Wildcard_arg_to_constant_constr".
Parameter mk_Eol_in_string : t.
Extract Inlined Constant mk_Eol_in_string => "Warnings.Eol_in_string".
Parameter mk_Duplicate_definitions : string -> string -> string -> string -> t.
Extract Inlined Constant mk_Duplicate_definitions => "(fun x__1 x__2 x__3 x__4 -> Warnings.Duplicate_definitions (x__1, x__2, x__3, x__4))".
Parameter mk_Unused_value_declaration : string -> t.
Extract Inlined Constant mk_Unused_value_declaration => "(fun x__1 -> Warnings.Unused_value_declaration x__1)".
Parameter mk_Unused_open : string -> t.
Extract Inlined Constant mk_Unused_open => "(fun x__1 -> Warnings.Unused_open x__1)".
Parameter mk_Unused_type_declaration : string -> type_declaration_usage_warning -> t.
Extract Inlined Constant mk_Unused_type_declaration => "(fun x__1 x__2 -> Warnings.Unused_type_declaration (x__1, x__2))".
Parameter mk_Unused_for_index : string -> t.
Extract Inlined Constant mk_Unused_for_index => "(fun x__1 -> Warnings.Unused_for_index x__1)".
Parameter mk_Unused_ancestor : string -> t.
Extract Inlined Constant mk_Unused_ancestor => "(fun x__1 -> Warnings.Unused_ancestor x__1)".
Parameter mk_Unused_constructor : string -> constructor_usage_warning -> t.
Extract Inlined Constant mk_Unused_constructor => "(fun x__1 x__2 -> Warnings.Unused_constructor (x__1, x__2))".
Parameter mk_Unused_extension : string -> bool -> constructor_usage_warning -> t.
Extract Inlined Constant mk_Unused_extension => "(fun x__1 x__2 x__3 -> Warnings.Unused_extension (x__1, x__2, x__3))".
Parameter mk_Unused_rec_flag : t.
Extract Inlined Constant mk_Unused_rec_flag => "Warnings.Unused_rec_flag".
Parameter mk_Name_out_of_scope : string -> name_out_of_scope_warning -> t.
Extract Inlined Constant mk_Name_out_of_scope => "(fun x__1 x__2 -> Warnings.Name_out_of_scope (x__1, x__2))".
Parameter mk_Ambiguous_name : list string -> list string -> bool -> string -> t.
Extract Inlined Constant mk_Ambiguous_name => "(fun x__1 x__2 x__3 x__4 -> Warnings.Ambiguous_name (x__1, x__2, x__3, x__4))".
Parameter mk_Disambiguated_name : string -> t.
Extract Inlined Constant mk_Disambiguated_name => "(fun x__1 -> Warnings.Disambiguated_name x__1)".
Parameter mk_Nonoptional_label : string -> t.
Extract Inlined Constant mk_Nonoptional_label => "(fun x__1 -> Warnings.Nonoptional_label x__1)".
Parameter mk_Open_shadow_identifier : string -> string -> t.
Extract Inlined Constant mk_Open_shadow_identifier => "(fun x__1 x__2 -> Warnings.Open_shadow_identifier (x__1, x__2))".
Parameter mk_Open_shadow_label_constructor : string -> string -> t.
Extract Inlined Constant mk_Open_shadow_label_constructor => "(fun x__1 x__2 -> Warnings.Open_shadow_label_constructor (x__1, x__2))".
Parameter mk_Bad_env_variable : string -> string -> t.
Extract Inlined Constant mk_Bad_env_variable => "(fun x__1 x__2 -> Warnings.Bad_env_variable (x__1, x__2))".
Parameter mk_Attribute_payload : string -> string -> t.
Extract Inlined Constant mk_Attribute_payload => "(fun x__1 x__2 -> Warnings.Attribute_payload (x__1, x__2))".
Parameter mk_Eliminated_optional_arguments : list string -> t.
Extract Inlined Constant mk_Eliminated_optional_arguments => "(fun x__1 -> Warnings.Eliminated_optional_arguments x__1)".
Parameter mk_No_cmi_file : string -> option string -> t.
Extract Inlined Constant mk_No_cmi_file => "(fun x__1 x__2 -> Warnings.No_cmi_file (x__1, x__2))".
Parameter mk_Unexpected_docstring : bool -> t.
Extract Inlined Constant mk_Unexpected_docstring => "(fun x__1 -> Warnings.Unexpected_docstring x__1)".
Parameter mk_Wrong_tailcall_expectation : bool -> t.
Extract Inlined Constant mk_Wrong_tailcall_expectation => "(fun x__1 -> Warnings.Wrong_tailcall_expectation x__1)".
Parameter mk_Fragile_literal_pattern : t.
Extract Inlined Constant mk_Fragile_literal_pattern => "Warnings.Fragile_literal_pattern".
Parameter mk_Misplaced_attribute : string -> t.
Extract Inlined Constant mk_Misplaced_attribute => "(fun x__1 -> Warnings.Misplaced_attribute x__1)".
Parameter mk_Duplicated_attribute : string -> t.
Extract Inlined Constant mk_Duplicated_attribute => "(fun x__1 -> Warnings.Duplicated_attribute x__1)".
Parameter mk_Inlining_impossible : string -> t.
Extract Inlined Constant mk_Inlining_impossible => "(fun x__1 -> Warnings.Inlining_impossible x__1)".
Parameter mk_Unreachable_case : t.
Extract Inlined Constant mk_Unreachable_case => "Warnings.Unreachable_case".
Parameter mk_Ambiguous_var_in_pattern_guard : list string -> t.
Extract Inlined Constant mk_Ambiguous_var_in_pattern_guard => "(fun x__1 -> Warnings.Ambiguous_var_in_pattern_guard x__1)".
Parameter mk_No_cmx_file : string -> string -> t.
Extract Inlined Constant mk_No_cmx_file => "(fun x__1 x__2 -> Warnings.No_cmx_file { missing_extension = x__1; module_name = x__2 })".
Parameter mk_Flambda_assignment_to_non_mutable_value : t.
Extract Inlined Constant mk_Flambda_assignment_to_non_mutable_value => "Warnings.Flambda_assignment_to_non_mutable_value".
Parameter mk_Unused_module : string -> t.
Extract Inlined Constant mk_Unused_module => "(fun x__1 -> Warnings.Unused_module x__1)".
Parameter mk_Unboxable_type_in_prim_decl : string -> t.
Extract Inlined Constant mk_Unboxable_type_in_prim_decl => "(fun x__1 -> Warnings.Unboxable_type_in_prim_decl x__1)".
Parameter mk_Constraint_on_gadt : t.
Extract Inlined Constant mk_Constraint_on_gadt => "Warnings.Constraint_on_gadt".
Parameter mk_Erroneous_printed_signature : string -> t.
Extract Inlined Constant mk_Erroneous_printed_signature => "(fun x__1 -> Warnings.Erroneous_printed_signature x__1)".
Parameter mk_Unsafe_array_syntax_without_parsing : t.
Extract Inlined Constant mk_Unsafe_array_syntax_without_parsing => "Warnings.Unsafe_array_syntax_without_parsing".
Parameter mk_Redefining_unit : string -> t.
Extract Inlined Constant mk_Redefining_unit => "(fun x__1 -> Warnings.Redefining_unit x__1)".
Parameter mk_Unused_open_bang : string -> t.
Extract Inlined Constant mk_Unused_open_bang => "(fun x__1 -> Warnings.Unused_open_bang x__1)".
Parameter mk_Unused_functor_parameter : string -> t.
Extract Inlined Constant mk_Unused_functor_parameter => "(fun x__1 -> Warnings.Unused_functor_parameter x__1)".
Parameter mk_Match_on_mutable_state_prevent_uncurry : t.
Extract Inlined Constant mk_Match_on_mutable_state_prevent_uncurry => "Warnings.Match_on_mutable_state_prevent_uncurry".
Parameter mk_Unused_field : string -> string -> field_usage_warning -> t.
Extract Inlined Constant mk_Unused_field => "(fun x__1 x__2 x__3 -> Warnings.Unused_field { form = x__1; field = x__2; complaint = x__3 })".
Parameter mk_Missing_mli : t.
Extract Inlined Constant mk_Missing_mli => "Warnings.Missing_mli".
Parameter mk_Unused_tmc_attribute : t.
Extract Inlined Constant mk_Unused_tmc_attribute => "Warnings.Unused_tmc_attribute".
Parameter mk_Tmc_breaks_tailcall : t.
Extract Inlined Constant mk_Tmc_breaks_tailcall => "Warnings.Tmc_breaks_tailcall".
Parameter mk_Generative_application_expects_unit : t.
Extract Inlined Constant mk_Generative_application_expects_unit => "Warnings.Generative_application_expects_unit".
Parameter mk_Degraded_to_partial_match : t.
Extract Inlined Constant mk_Degraded_to_partial_match => "Warnings.Degraded_to_partial_match".
Parameter mk_Unnecessarily_partial_tuple_pattern : t.
Extract Inlined Constant mk_Unnecessarily_partial_tuple_pattern => "Warnings.Unnecessarily_partial_tuple_pattern".
Parameter mk_Imprecise_kind_annotation : string -> string -> string -> t.
Extract Inlined Constant mk_Imprecise_kind_annotation => "(fun x__1 x__2 x__3 -> Warnings.Imprecise_kind_annotation { name = x__1; annotated = x__2; inferred = x__3 })".
Parameter mk_Untagged_external_small_int_return : t.
Extract Inlined Constant mk_Untagged_external_small_int_return => "Warnings.Untagged_external_small_int_return".
Parameter mk_Redundant_kind_modifier : string -> t.
Extract Inlined Constant mk_Redundant_kind_modifier => "(fun x__1 -> Warnings.Redundant_kind_modifier x__1)".
Parameter mk_Ignored_kind_modifier : string -> string -> t.
Extract Inlined Constant mk_Ignored_kind_modifier => "(fun x__1 x__2 -> Warnings.Ignored_kind_modifier { modifier = x__1; abbrev = x__2 })".
Parameter mk_Unmutated_mutable : string -> t.
Extract Inlined Constant mk_Unmutated_mutable => "(fun x__1 -> Warnings.Unmutated_mutable x__1)".
Parameter mk_Incompatible_with_upstream : upstream_compat_warning -> t.
Extract Inlined Constant mk_Incompatible_with_upstream => "(fun x__1 -> Warnings.Incompatible_with_upstream x__1)".
Parameter mk_Unerasable_position_argument : t.
Extract Inlined Constant mk_Unerasable_position_argument => "Warnings.Unerasable_position_argument".
Parameter mk_Probe_name_too_long : string -> t.
Extract Inlined Constant mk_Probe_name_too_long => "(fun x__1 -> Warnings.Probe_name_too_long x__1)".
Parameter mk_Unused_kind_declaration : string -> t.
Extract Inlined Constant mk_Unused_kind_declaration => "(fun x__1 -> Warnings.Unused_kind_declaration x__1)".
Parameter mk_Zero_alloc_all_hidden_arrow : string -> t.
Extract Inlined Constant mk_Zero_alloc_all_hidden_arrow => "(fun x__1 -> Warnings.Zero_alloc_all_hidden_arrow x__1)".
Parameter mk_Unchecked_zero_alloc_attribute : t.
Extract Inlined Constant mk_Unchecked_zero_alloc_attribute => "Warnings.Unchecked_zero_alloc_attribute".
Parameter mk_Unboxing_impossible : t.
Extract Inlined Constant mk_Unboxing_impossible => "Warnings.Unboxing_impossible".
Parameter mk_Redundant_modifier : string -> redundant_modifier_reason -> t.
Extract Inlined Constant mk_Redundant_modifier => "(fun x__1 x__2 -> Warnings.Redundant_modifier { modifier = x__1; reason = x__2 })".
Parameter mk_Atomic_float_record_boxed : t.
Extract Inlined Constant mk_Atomic_float_record_boxed => "Warnings.Atomic_float_record_boxed".
Parameter mk_Implied_attribute : string -> string -> t.
Extract Inlined Constant mk_Implied_attribute => "(fun x__1 x__2 -> Warnings.Implied_attribute { implying = x__1; implied = x__2 })".
Parameter mk_Use_during_borrowing : t.
Extract Inlined Constant mk_Use_during_borrowing => "Warnings.Use_during_borrowing".
Parameter mk_Lpoly_in_letrec : t.
Extract Inlined Constant mk_Lpoly_in_letrec => "Warnings.Lpoly_in_letrec".
Parameter mk_Useless_valpoly : t.
Extract Inlined Constant mk_Useless_valpoly => "Warnings.Useless_valpoly".
Parameter mk_Redundant_modality : t.
Extract Inlined Constant mk_Redundant_modality => "Warnings.Redundant_modality".
Parameter mk_Unused_alert_disable : string -> t.
Extract Inlined Constant mk_Unused_alert_disable => "(fun x__1 -> Warnings.Unused_alert_disable x__1)".
Parameter match_t : forall {Res : Type}, t -> (unit -> M Res) -> (unit -> M Res) -> (string -> M Res) -> (unit -> M Res) -> (list string -> M Res) -> (list string -> M Res) -> (Format_doc.t -> M Res) -> (string -> string -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (list string -> M Res) -> (unit -> M Res) -> (list string -> M Res) -> (unit -> M Res) -> (string -> M Res) -> (Format_doc.t -> M Res) -> (string -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (string -> M Res) -> (string -> M Res) -> (string -> M Res) -> (unit -> M Res) -> (string -> bool -> M Res) -> (string -> bool -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (string -> string -> string -> string -> M Res) -> (string -> M Res) -> (string -> M Res) -> (string -> type_declaration_usage_warning -> M Res) -> (string -> M Res) -> (string -> M Res) -> (string -> constructor_usage_warning -> M Res) -> (string -> bool -> constructor_usage_warning -> M Res) -> (unit -> M Res) -> (string -> name_out_of_scope_warning -> M Res) -> (list string -> list string -> bool -> string -> M Res) -> (string -> M Res) -> (string -> M Res) -> (string -> string -> M Res) -> (string -> string -> M Res) -> (string -> string -> M Res) -> (string -> string -> M Res) -> (list string -> M Res) -> (string -> option string -> M Res) -> (bool -> M Res) -> (bool -> M Res) -> (unit -> M Res) -> (string -> M Res) -> (string -> M Res) -> (string -> M Res) -> (unit -> M Res) -> (list string -> M Res) -> (string -> string -> M Res) -> (unit -> M Res) -> (string -> M Res) -> (string -> M Res) -> (unit -> M Res) -> (string -> M Res) -> (unit -> M Res) -> (string -> M Res) -> (string -> M Res) -> (string -> M Res) -> (unit -> M Res) -> (string -> string -> field_usage_warning -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (string -> string -> string -> M Res) -> (unit -> M Res) -> (string -> M Res) -> (string -> string -> M Res) -> (string -> M Res) -> (upstream_compat_warning -> M Res) -> (unit -> M Res) -> (string -> M Res) -> (string -> M Res) -> (string -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (string -> redundant_modifier_reason -> M Res) -> (unit -> M Res) -> (string -> string -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (string -> M Res) -> M Res.
Extract Inlined Constant match_t => "(fun x__0 f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 f__9 f__10 f__11 f__12 f__13 f__14 f__15 f__16 f__17 f__18 f__19 f__20 f__21 f__22 f__23 f__24 f__25 f__26 f__27 f__28 f__29 f__30 f__31 f__32 f__33 f__34 f__35 f__36 f__37 f__38 f__39 f__40 f__41 f__42 f__43 f__44 f__45 f__46 f__47 f__48 f__49 f__50 f__51 f__52 f__53 f__54 f__55 f__56 f__57 f__58 f__59 f__60 f__61 f__62 f__63 f__64 f__65 f__66 f__67 f__68 f__69 f__70 f__71 f__72 f__73 f__74 f__75 f__76 f__77 f__78 f__79 f__80 f__81 f__82 f__83 f__84 f__85 f__86 f__87 f__88 f__89 f__90 f__91 f__92 f__93 -> match x__0 with Warnings.Comment_start -> f__1 () | Warnings.Comment_not_end -> f__2 () | Warnings.Fragile_match x__1 -> f__3 x__1 | Warnings.Ignored_partial_application -> f__4 () | Warnings.Labels_omitted x__1 -> f__5 x__1 | Warnings.Method_override x__1 -> f__6 x__1 | Warnings.Partial_match x__1 -> f__7 x__1 | Warnings.Missing_record_field_pattern { form = x__1; unbound = x__2 } -> f__8 x__1 x__2 | Warnings.Non_unit_statement -> f__9 () | Warnings.Redundant_case -> f__10 () | Warnings.Redundant_subpat -> f__11 () | Warnings.Instance_variable_override x__1 -> f__12 x__1 | Warnings.Illegal_backslash -> f__13 () | Warnings.Implicit_public_methods x__1 -> f__14 x__1 | Warnings.Unerasable_optional_argument -> f__15 () | Warnings.Undeclared_virtual_method x__1 -> f__16 x__1 | Warnings.Not_principal x__1 -> f__17 x__1 | Warnings.Non_principal_labels x__1 -> f__18 x__1 | Warnings.Ignored_extra_argument -> f__19 () | Warnings.Nonreturning_statement -> f__20 () | Warnings.Preprocessor x__1 -> f__21 x__1 | Warnings.Useless_record_with x__1 -> f__22 x__1 | Warnings.Bad_module_name x__1 -> f__23 x__1 | Warnings.All_clauses_guarded -> f__24 () | Warnings.Unused_var { name = x__1; mutated = x__2 } -> f__25 x__1 x__2 | Warnings.Unused_var_strict { name = x__1; mutated = x__2 } -> f__26 x__1 x__2 | Warnings.Wildcard_arg_to_constant_constr -> f__27 () | Warnings.Eol_in_string -> f__28 () | Warnings.Duplicate_definitions (x__1, x__2, x__3, x__4) -> f__29 x__1 x__2 x__3 x__4 | Warnings.Unused_value_declaration x__1 -> f__30 x__1 | Warnings.Unused_open x__1 -> f__31 x__1 | Warnings.Unused_type_declaration (x__1, x__2) -> f__32 x__1 x__2 | Warnings.Unused_for_index x__1 -> f__33 x__1 | Warnings.Unused_ancestor x__1 -> f__34 x__1 | Warnings.Unused_constructor (x__1, x__2) -> f__35 x__1 x__2 | Warnings.Unused_extension (x__1, x__2, x__3) -> f__36 x__1 x__2 x__3 | Warnings.Unused_rec_flag -> f__37 () | Warnings.Name_out_of_scope (x__1, x__2) -> f__38 x__1 x__2 | Warnings.Ambiguous_name (x__1, x__2, x__3, x__4) -> f__39 x__1 x__2 x__3 x__4 | Warnings.Disambiguated_name x__1 -> f__40 x__1 | Warnings.Nonoptional_label x__1 -> f__41 x__1 | Warnings.Open_shadow_identifier (x__1, x__2) -> f__42 x__1 x__2 | Warnings.Open_shadow_label_constructor (x__1, x__2) -> f__43 x__1 x__2 | Warnings.Bad_env_variable (x__1, x__2) -> f__44 x__1 x__2 | Warnings.Attribute_payload (x__1, x__2) -> f__45 x__1 x__2 | Warnings.Eliminated_optional_arguments x__1 -> f__46 x__1 | Warnings.No_cmi_file (x__1, x__2) -> f__47 x__1 x__2 | Warnings.Unexpected_docstring x__1 -> f__48 x__1 | Warnings.Wrong_tailcall_expectation x__1 -> f__49 x__1 | Warnings.Fragile_literal_pattern -> f__50 () | Warnings.Misplaced_attribute x__1 -> f__51 x__1 | Warnings.Duplicated_attribute x__1 -> f__52 x__1 | Warnings.Inlining_impossible x__1 -> f__53 x__1 | Warnings.Unreachable_case -> f__54 () | Warnings.Ambiguous_var_in_pattern_guard x__1 -> f__55 x__1 | Warnings.No_cmx_file { missing_extension = x__1; module_name = x__2 } -> f__56 x__1 x__2 | Warnings.Flambda_assignment_to_non_mutable_value -> f__57 () | Warnings.Unused_module x__1 -> f__58 x__1 | Warnings.Unboxable_type_in_prim_decl x__1 -> f__59 x__1 | Warnings.Constraint_on_gadt -> f__60 () | Warnings.Erroneous_printed_signature x__1 -> f__61 x__1 | Warnings.Unsafe_array_syntax_without_parsing -> f__62 () | Warnings.Redefining_unit x__1 -> f__63 x__1 | Warnings.Unused_open_bang x__1 -> f__64 x__1 | Warnings.Unused_functor_parameter x__1 -> f__65 x__1 | Warnings.Match_on_mutable_state_prevent_uncurry -> f__66 () | Warnings.Unused_field { form = x__1; field = x__2; complaint = x__3 } -> f__67 x__1 x__2 x__3 | Warnings.Missing_mli -> f__68 () | Warnings.Unused_tmc_attribute -> f__69 () | Warnings.Tmc_breaks_tailcall -> f__70 () | Warnings.Generative_application_expects_unit -> f__71 () | Warnings.Degraded_to_partial_match -> f__72 () | Warnings.Unnecessarily_partial_tuple_pattern -> f__73 () | Warnings.Imprecise_kind_annotation { name = x__1; annotated = x__2; inferred = x__3 } -> f__74 x__1 x__2 x__3 | Warnings.Untagged_external_small_int_return -> f__75 () | Warnings.Redundant_kind_modifier x__1 -> f__76 x__1 | Warnings.Ignored_kind_modifier { modifier = x__1; abbrev = x__2 } -> f__77 x__1 x__2 | Warnings.Unmutated_mutable x__1 -> f__78 x__1 | Warnings.Incompatible_with_upstream x__1 -> f__79 x__1 | Warnings.Unerasable_position_argument -> f__80 () | Warnings.Probe_name_too_long x__1 -> f__81 x__1 | Warnings.Unused_kind_declaration x__1 -> f__82 x__1 | Warnings.Zero_alloc_all_hidden_arrow x__1 -> f__83 x__1 | Warnings.Unchecked_zero_alloc_attribute -> f__84 () | Warnings.Unboxing_impossible -> f__85 () | Warnings.Redundant_modifier { modifier = x__1; reason = x__2 } -> f__86 x__1 x__2 | Warnings.Atomic_float_record_boxed -> f__87 () | Warnings.Implied_attribute { implying = x__1; implied = x__2 } -> f__88 x__1 x__2 | Warnings.Use_during_borrowing -> f__89 () | Warnings.Lpoly_in_letrec -> f__90 () | Warnings.Useless_valpoly -> f__91 () | Warnings.Redundant_modality -> f__92 () | Warnings.Unused_alert_disable x__1 -> f__93 x__1)".
