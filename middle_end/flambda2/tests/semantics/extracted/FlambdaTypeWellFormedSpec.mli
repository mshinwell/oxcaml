open BinInt
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypeMeaningSpec
open List
open ListDef
open PeanoNat

val non_empty : 'a1 list -> bool

val keys : ('a1, 'a2) Keyed.finite_map -> 'a1 list

val has_naked_number_types : naked_number_kind -> bool

val block_shape_canonical_b : block_shape -> bool

val descr_well_formed : ('a1 -> bool) -> 'a1 type_descr -> bool

val head_of_kind_naked_immediate_well_formed :
  head_of_kind_naked_immediate -> bool

val block_product_fits :
  (nat, block_shape) row_like_index -> flambda_type list -> bool

val block_case_well_formed :
  (flambda_type -> bool) ->
  (env_extension -> bool) ->
  row_like_block_case ->
  bool

val closures_index_has_slot :
  function_slot -> (set_of_closures_contents, unit) row_like_index -> bool

val closures_entry_slots_fit :
  (set_of_closures_contents, unit) row_like_index ->
  function_slot list ->
  function_slot list ->
  value_slot list ->
  bool

val type_well_formed : flambda_type -> bool

val head_of_kind_value_well_formed : head_of_kind_value -> bool

val head_of_kind_value_non_null_well_formed :
  head_of_kind_value_non_null -> bool

val row_like_for_blocks_well_formed : row_like_for_blocks -> bool

val row_like_for_closures_well_formed : row_like_for_closures -> bool

val closures_entry_well_formed :
  (set_of_closures_contents, unit) row_like_index -> closures_entry -> bool

val env_extension_well_formed : env_extension -> bool
