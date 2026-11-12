open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaBindingTime
open FlambdaCompareSpec
open FlambdaExpandHead
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeAccessSpec
open FlambdaTypeEqualSpec
open FlambdaTypeGrammar
open FlambdaTypeMeaningBoolSpec
open FlambdaTypingEnv
open List
open PeanoNat

type descr_oub =
  | Oub_value of head_of_kind_value or_unknown_or_bottom
  | Oub_naked_immediate of head_of_kind_naked_immediate or_unknown_or_bottom
  | Oub_naked_number of naked_number_kind * coq_Z list or_unknown_or_bottom
  | Oub_rec_info of unit or_unknown_or_bottom
  | Oub_region of unit or_unknown_or_bottom

val descr_oub_of_expanded : Expanded_type.t -> descr_oub

module Meet_shortcut : sig
  type 'a t =
    | Known_result of 'a
    | Need_meet
    | Invalid
end

module Proof_of_property : sig
  type 'a t =
    | Proved of 'a
    | Unknown
end

module Generic_proof : sig
  type 'a t =
    | Proved of 'a
    | Unknown
    | Invalid
end

module Provers : sig
  val is_bottom : Typing_env.t -> flambda_type -> bool option

  val expand_head : Typing_env.t -> flambda_type -> descr_oub option

  val wrong_kind : 'a1 -> 'a1

  val as_meet_shortcut : 'a1 Generic_proof.t -> 'a1 Meet_shortcut.t

  val as_property : 'a1 Generic_proof.t -> 'a1 Proof_of_property.t

  val gen_value_to_gen :
    (Typing_env.t -> head_of_kind_value_non_null -> 'a1 Generic_proof.t option) ->
    Typing_env.t ->
    flambda_type ->
    'a1 Generic_proof.t option

  val gen_value_to_proof :
    (Typing_env.t -> head_of_kind_value_non_null -> 'a1 Generic_proof.t option) ->
    Typing_env.t ->
    flambda_type ->
    'a1 Proof_of_property.t option

  val gen_value_to_meet :
    (Typing_env.t -> head_of_kind_value_non_null -> 'a1 Generic_proof.t option) ->
    Typing_env.t ->
    flambda_type ->
    'a1 Meet_shortcut.t option

  val prove_is_int_generic_value :
    bool ->
    Typing_env.t ->
    head_of_kind_value_non_null ->
    bool Generic_proof.t option

  val prove_is_int_generic :
    bool -> Typing_env.t -> flambda_type -> bool Generic_proof.t option

  val prove_is_int :
    Typing_env.t -> flambda_type -> bool Proof_of_property.t option

  val meet_is_int_variant_only :
    Typing_env.t -> flambda_type -> bool Meet_shortcut.t option

  val prove_get_tag_generic_value :
    Typing_env.t ->
    head_of_kind_value_non_null ->
    coq_Z list Generic_proof.t option

  val prove_get_tag_generic :
    Typing_env.t -> flambda_type -> coq_Z list Generic_proof.t option

  val prove_get_tag :
    Typing_env.t -> flambda_type -> coq_Z list Proof_of_property.t option

  val prove_is_null_generic :
    Typing_env.t -> flambda_type -> bool Generic_proof.t option

  val meet_is_null : Typing_env.t -> flambda_type -> bool Meet_shortcut.t option

  val these_immediates : coq_Z list -> coq_Z list Generic_proof.t

  val meet_these_immediates :
    coq_Z list -> coq_Z list Generic_proof.t -> coq_Z list Generic_proof.t

  val meet_this_immediate :
    coq_Z -> coq_Z list Generic_proof.t -> coq_Z list Generic_proof.t

  val prove_naked_immediates_relation :
    Typing_env.t ->
    Relation.t ->
    name ->
    coq_Z list Generic_proof.t ->
    coq_Z list Generic_proof.t option

  val prove_naked_immediates_generic :
    Typing_env.t -> flambda_type -> coq_Z list Generic_proof.t option

  val meet_naked_immediates :
    Typing_env.t -> flambda_type -> coq_Z list Meet_shortcut.t option

  val meet_equals_tagged_immediates_value :
    Typing_env.t ->
    head_of_kind_value_non_null ->
    coq_Z list Generic_proof.t option

  val meet_equals_tagged_immediates :
    Typing_env.t -> flambda_type -> coq_Z list Meet_shortcut.t option

  val canonical_simple_of_alias :
    Typing_env.t -> Name_mode.t -> flambda_type -> simple option option

  type tagging_proof_kind =
    | Prove
    | Meet

  val inspect_tagging_immediates :
    Name_mode.t ->
    Typing_env.t ->
    flambda_type Or_unknown.t ->
    simple Generic_proof.t option

  val inspect_tagging_of_simple_value :
    tagging_proof_kind ->
    Name_mode.t ->
    Typing_env.t ->
    head_of_kind_value_non_null ->
    simple Generic_proof.t option

  val meet_tagging_of_simple :
    Typing_env.t -> Name_mode.t -> flambda_type -> simple Meet_shortcut.t option

  val meet_boxed_number_containing_simple :
    boxable_number ->
    Typing_env.t ->
    Name_mode.t ->
    flambda_type ->
    simple Meet_shortcut.t option

  val meet_block_field_simple_value :
    Name_mode.t ->
    flambda_kind ->
    nat ->
    Typing_env.t ->
    head_of_kind_value_non_null ->
    simple Generic_proof.t option

  val meet_block_field_simple :
    Typing_env.t ->
    Name_mode.t ->
    flambda_kind ->
    flambda_type ->
    nat ->
    simple Meet_shortcut.t option

  val single_closures_entry_of_singleton :
    Alloc_mode.t ->
    bool ->
    function_slot ->
    closures_entry ->
    (((function_slot * Alloc_mode.t) * closures_entry) * function_type)
    Generic_proof.t

  val prove_single_closures_entry_generic_value :
    Typing_env.t ->
    head_of_kind_value_non_null ->
    (((function_slot * Alloc_mode.t) * closures_entry) * function_type)
    Generic_proof.t
    option

  val prove_single_closures_entry :
    Typing_env.t ->
    flambda_type ->
    (((function_slot * Alloc_mode.t) * closures_entry) * function_type)
    Proof_of_property.t
    option

  val meet_project_function_slot_simple_value :
    Name_mode.t ->
    function_slot ->
    Typing_env.t ->
    head_of_kind_value_non_null ->
    simple Generic_proof.t option

  val meet_project_function_slot_simple :
    Typing_env.t ->
    Name_mode.t ->
    flambda_type ->
    function_slot ->
    simple Meet_shortcut.t option

  val meet_project_value_slot_simple_value :
    Name_mode.t ->
    value_slot ->
    flambda_kind ->
    Typing_env.t ->
    head_of_kind_value_non_null ->
    simple Generic_proof.t option

  val meet_project_value_slot_simple :
    Typing_env.t ->
    Name_mode.t ->
    flambda_type ->
    value_slot ->
    flambda_kind ->
    simple Meet_shortcut.t option

  val incompatible_naked_numbers :
    Typing_env.t -> flambda_type -> flambda_type -> bool option

  val physical_equality_of_immediates :
    Typing_env.t -> flambda_type -> flambda_type -> bool Generic_proof.t option

  val physical_equality_of_blocks :
    row_like_for_blocks -> row_like_for_blocks -> bool Generic_proof.t

  val no_immediate_and_no_block :
    flambda_type Or_unknown.t -> row_like_for_blocks Or_unknown.t -> bool

  val physical_equality_of_parts :
    bool Generic_proof.t -> bool Generic_proof.t -> bool Proof_of_property.t

  val physical_equality_of_variants :
    Typing_env.t ->
    flambda_type Or_unknown.t ->
    flambda_type Or_unknown.t ->
    row_like_for_blocks Or_unknown.t ->
    row_like_for_blocks Or_unknown.t ->
    bool Proof_of_property.t option

  val physical_equality_of_heads :
    Typing_env.t ->
    head_of_kind_value_non_null ->
    head_of_kind_value_non_null ->
    bool Proof_of_property.t option

  val physical_equality_check_heads :
    Typing_env.t ->
    flambda_type ->
    flambda_type ->
    bool Proof_of_property.t option

  val prove_physical_equality :
    Typing_env.t ->
    flambda_type ->
    flambda_type ->
    bool Proof_of_property.t option
end
