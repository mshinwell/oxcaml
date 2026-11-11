open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaCompareSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaSemanticsSpec
open FlambdaTypeGrammar
open FlambdaTypeMeaningSpec
open FlambdaValueSpec
open List
open ListDef
open PeanoNat

val lists_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val value_eqb : value -> value -> bool

val is_poison_b : value -> bool

val is_tag_b : coq_Z -> bool

val relation_holds_b : static_env -> Relation.t -> value -> coq_Z -> bool

val block_has_shape_b : block_shape -> coq_Z -> value list -> bool

val block_index_satisfied_b :
  coq_Z -> value list -> (nat, block_shape) row_like_index -> bool

val closures_index_satisfied_b :
  (function_slot * code_id) list ->
  (value_slot * value) list ->
  (set_of_closures_contents, unit) row_like_index ->
  bool

val variable_is_b : env -> variable option -> coq_Z -> bool

val descr_satisfied_b :
  env -> flambda_kind -> ('a1 -> bool) -> value -> 'a1 type_descr -> bool

val head_of_kind_naked_immediate_satisfied_b :
  static_env -> env -> value -> head_of_kind_naked_immediate -> bool

val naked_numbers_satisfied_b : naked_number_kind -> value -> coq_Z list -> bool

val fields_satisfied_b :
  (value -> flambda_type -> bool) -> flambda_type list -> value list -> bool

val block_case_satisfied_b :
  (value -> flambda_type -> bool) ->
  (env_extension -> bool) ->
  coq_Z ->
  value list ->
  row_like_block_case ->
  bool

val closures_case_satisfied_b :
  (closures_entry -> bool) ->
  (env_extension -> bool) ->
  (function_slot * code_id) list ->
  (value_slot * value) list ->
  row_like_closures_case ->
  bool

val type_satisfied_b : static_env -> env -> value -> flambda_type -> bool

val closures_entry_satisfied_b :
  static_env ->
  env ->
  value ->
  function_slot ->
  (function_slot * code_id) list ->
  (value_slot * value) list ->
  closures_entry ->
  bool

val env_extension_satisfied_b : static_env -> env -> env_extension -> bool

val row_like_block_case_satisfied_b :
  static_env -> env -> coq_Z -> value list -> row_like_block_case -> bool

val row_like_closures_case_satisfied_b :
  static_env ->
  env ->
  value ->
  function_slot ->
  (function_slot * code_id) list ->
  (value_slot * value) list ->
  row_like_closures_case ->
  bool
