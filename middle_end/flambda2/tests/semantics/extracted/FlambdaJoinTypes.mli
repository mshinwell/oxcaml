open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaExpandHead
open FlambdaJoinEnv
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypeMeaningBoolSpec
open FlambdaTypingEnv
open List
open ListDef
open PeanoNat

module Expanded_type : sig
  type head = Expanded_type.head =
    | Head_value of head_of_kind_value
    | Head_naked_immediate of head_of_kind_naked_immediate
    | Head_naked_number of naked_number_kind * coq_Z list
    | Head_rec_info of unit
    | Head_region of unit

  val head_rect :
    (head_of_kind_value -> 'a1) ->
    (head_of_kind_naked_immediate -> 'a1) ->
    (naked_number_kind -> coq_Z list -> 'a1) ->
    (unit -> 'a1) ->
    (unit -> 'a1) ->
    head ->
    'a1

  val head_rec :
    (head_of_kind_value -> 'a1) ->
    (head_of_kind_naked_immediate -> 'a1) ->
    (naked_number_kind -> coq_Z list -> 'a1) ->
    (unit -> 'a1) ->
    (unit -> 'a1) ->
    head ->
    'a1

  type t = Expanded_type.t =
    { kind : flambda_kind;
      descr : head or_unknown_or_bottom
    }

  val kind : t -> flambda_kind

  val descr : t -> head or_unknown_or_bottom

  val create_bottom : flambda_kind -> t

  val create_unknown : flambda_kind -> t

  val create_value : head_of_kind_value -> t

  val create_naked_immediate : head_of_kind_naked_immediate -> t

  val create_naked_number : naked_number_kind -> coq_Z list -> t

  val create_rec_info : unit -> t

  val create_region : unit -> t

  val create_const : const -> t

  val bottom_like : t -> t

  val unknown_like : t -> t

  val is_bottom : t -> bool

  val is_unknown : t -> bool

  val to_type : t -> flambda_type

  val of_non_alias_type : flambda_type -> t option
end

val known_function_types :
  (Index.t * function_type Or_unknown.t) list -> function_type list option

val n_way_join_function_type :
  (Index.t * function_type Or_unknown.t) list -> function_type Or_unknown.t

val gather_function_types :
  (Index.t * function_type Or_unknown.t finite_map) list ->
  (Index.t * function_type Or_unknown.t) list finite_map

val n_way_join_function_types :
  (Index.t * function_type Or_unknown.t finite_map) list ->
  function_type Or_unknown.t finite_map

val or_unknown_map : ('a1 -> 'a2) -> 'a1 Or_unknown.t -> 'a2 Or_unknown.t

val join_alloc_mode : Alloc_mode.t -> Alloc_mode.t -> Alloc_mode.t

val numbers_union : coq_Z list -> coq_Z list -> coq_Z list

val untagged_const_bool : bool -> simple

val untagged_const_int : coq_Z -> simple

val row_like_for_blocks_all_tags :
  row_like_for_blocks -> coq_Z list Or_unknown.t

val deduce_is_int :
  row_like_for_blocks Or_unknown.t ->
  flambda_type Or_unknown.t ->
  bool Or_unknown.t

val deduce_is_int_simple :
  row_like_for_blocks Or_unknown.t ->
  flambda_type Or_unknown.t ->
  variable option ->
  simple option

val deduce_get_tag :
  row_like_for_blocks Or_unknown.t -> coq_Z or_unknown_or_bottom

val deduce_get_tag_simple :
  row_like_for_blocks Or_unknown.t ->
  variable option ->
  simple or_unknown_or_bottom

val known_contents :
  (Index.t * 'a1) list ->
  (Index.t * 'a1 Or_unknown.t) list ->
  (Index.t * 'a1) list option

val is_null_simples :
  (Index.t * head_of_kind_value) list -> (Index.t * simple) list option

val strings_union : coq_Z list list -> coq_Z list list -> coq_Z list list

val unknown_from_shape : block_shape -> nat -> flambda_type option

val env_extension_is_empty : env_extension -> bool

val closures_entry_function_types :
  closures_entry -> function_type Or_unknown.t finite_map

val closures_entry_closure_types : closures_entry -> flambda_type finite_map

val closures_entry_value_slot_types : closures_entry -> flambda_type finite_map

val row_like_known_tags :
  row_like_for_blocks ->
  (coq_Z, row_like_block_case Or_unknown.t) Keyed.finite_map

val row_like_other_tags : row_like_for_blocks -> row_like_block_case Or_bottom.t

val row_like_alloc_mode : row_like_for_blocks -> Alloc_mode.t

val row_like_known_closures :
  row_like_for_closures -> row_like_closures_case finite_map

val gather_components :
  (Index.t * 'a1 finite_map) list -> (Index.t * 'a1) list finite_map

val add_other :
  ('a2 -> 'a1) ->
  (Index.t * 'a1) list ->
  Index.t ->
  'a2 Or_bottom.t ->
  (Index.t * 'a1) list

val gather_known :
  ('a1 -> 'a1 -> bool) ->
  ('a3 -> 'a2) ->
  (Index.t * (('a1, 'a2) Keyed.finite_map * 'a3 Or_bottom.t)) list ->
  ('a1, (Index.t * 'a2) list) Keyed.finite_map

val all_known : (Index.t * 'a1 Or_unknown.t) list -> (Index.t * 'a1) list option

val non_bottom :
  (Index.t * 'a1) list ->
  (Index.t * 'a1 Or_bottom.t) list ->
  (Index.t * 'a1) list

val gather_extensions :
  (Index.t * env_extension) list ->
  (Index.t * env_extension) list ->
  (Index.t * variant_extensions) list ->
  ((Index.t * env_extension) list * (Index.t * env_extension) list) option

val non_null_heads :
  (Index.t * head_of_kind_value_non_null) list ->
  (Index.t * head_of_kind_value) list ->
  (Index.t * head_of_kind_value_non_null) list option

val gather_heads :
  (head_of_kind_value_non_null -> 'a1 option) ->
  (Index.t -> 'a1 -> 'a2 -> 'a2) ->
  (Index.t * head_of_kind_value_non_null) list ->
  'a2 ->
  'a2 option

type variant_parts =
  { parts_blocks : (Index.t * row_like_for_blocks Or_unknown.t) list;
    parts_immediates : (Index.t * flambda_type Or_unknown.t) list;
    parts_extensions : (Index.t * variant_extensions) list;
    parts_is_unique : bool;
    parts_is_int : (Index.t * simple) list option;
    parts_get_tag : (Index.t * simple) list option
  }

type variant_fields =
  { variant_is_int : variable option;
    variant_immediates : flambda_type Or_unknown.t;
    variant_get_tag : variable option;
    variant_blocks : row_like_for_blocks Or_unknown.t;
    variant_extensions_of : variant_extensions;
    variant_is_unique : bool
  }

val read_variant : head_of_kind_value_non_null -> variant_fields option

val first_variant_parts : Index.t -> variant_fields -> variant_parts

val add_variant_parts :
  Index.t -> variant_fields -> variant_parts -> variant_parts

val read_mutable_block : head_of_kind_value_non_null -> Alloc_mode.t option

val read_boxed_number :
  boxable_number ->
  head_of_kind_value_non_null ->
  (flambda_type * Alloc_mode.t) option

val read_closures :
  head_of_kind_value_non_null -> (row_like_for_closures * Alloc_mode.t) option

val read_string : head_of_kind_value_non_null -> coq_Z list list option

val extract_heads :
  (Expanded_type.head -> 'a1 option) ->
  (Index.t * Expanded_type.t) list ->
  (Index.t * 'a1) list option option

val alias_simples :
  (Index.t * flambda_type) list -> (Index.t * simple) list option

val fields_at :
  nat ->
  (Index.t * flambda_type list) list ->
  (Index.t * flambda_type) list option

type ('state, 'a) n_way_join_result = ('a Or_unknown.t * 'state) option

val map_join_result :
  ('a2 -> 'a3) -> ('a1, 'a2) n_way_join_result -> ('a1, 'a3) n_way_join_result

val n_way_join_unknown :
  ('a1 -> (Index.t * 'a2) list -> ('a1, 'a3) n_way_join_result) ->
  'a1 ->
  (Index.t * 'a2 Or_unknown.t) list ->
  ('a1, 'a3) n_way_join_result

val n_way_join_head_of_kind_naked_number :
  'a1 ->
  coq_Z list * Index.t ->
  (Index.t * coq_Z list) list ->
  ('a1, coq_Z list) n_way_join_result

val n_way_join_relation_simples :
  ('a1 ->
  flambda_kind ->
  (Index.t * simple) list ->
  (simple Or_bottom.t * 'a1) option) ->
  'a1 ->
  (Index.t * simple) list option ->
  (variable option * 'a1) option

val n_way_join_is_null :
  ('a1 ->
  flambda_kind ->
  (Index.t * simple) list ->
  (simple Or_bottom.t * 'a1) option) ->
  'a1 ->
  (Index.t * head_of_kind_value) list ->
  (is_null * 'a1) option

val join_naked_immediates :
  ('a1 -> Index.t -> Typing_env.t option) ->
  (Typing_env.t ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate Or_bottom.t) ->
  'a1 ->
  coq_Z list Or_unknown.t ->
  (Index.t * head_of_kind_naked_immediate) list ->
  coq_Z list Or_unknown.t option

val n_way_join_head_of_kind_naked_immediate :
  ('a1 -> Index.t -> Typing_env.t option) ->
  (Typing_env.t ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate Or_bottom.t) ->
  'a1 ->
  (Index.t * head_of_kind_naked_immediate) list ->
  ('a1, head_of_kind_naked_immediate) n_way_join_result

val n_way_join_head_of_kind_naked_numbers :
  'a1 ->
  coq_Z list * Index.t ->
  (Index.t * coq_Z list) list ->
  ('a1, coq_Z list) n_way_join_result

val n_way_join_head_of_kind_rec_info :
  'a1 ->
  unit * Index.t ->
  (Index.t * unit) list ->
  ('a1, unit) n_way_join_result

val n_way_join_head_of_kind_region :
  'a1 ->
  unit * Index.t ->
  (Index.t * unit) list ->
  ('a1, unit) n_way_join_result

val n_way_join_env_extension :
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  'a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) option

val generic_merge_map_known :
  ('a2 -> 'a2 -> bool) ->
  ('a4 -> 'a3) ->
  ('a1 -> (Index.t * 'a3) list -> ('a3 * 'a1) Or_bottom.t option) ->
  'a1 ->
  (Index.t * (('a2, 'a3) Keyed.finite_map * 'a4 Or_bottom.t)) list ->
  (('a2, 'a3) Keyed.finite_map * 'a1) option

val n_way_join_index :
  ('a1 -> 'a1 -> bool) ->
  ('a1 -> 'a1 -> 'a1) ->
  ('a2 list -> 'a2 or_unknown_or_bottom) ->
  ('a1, 'a2) row_like_index list ->
  ('a1, 'a2) row_like_index or_unknown_or_bottom

val n_way_join_case :
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  ('a1 -> 'a3 -> (Index.t * 'a4) list -> ('a4 * 'a1) option) ->
  ('a2 -> 'a2 -> bool) ->
  ('a2 -> 'a2 -> 'a2) ->
  ('a3 list -> 'a3 or_unknown_or_bottom) ->
  'a1 ->
  (Index.t * ('a2, 'a3, 'a4, env_extension) row_like_case) list ->
  (('a2, 'a3, 'a4, env_extension) row_like_case Or_unknown.t * 'a1) Or_bottom.t
  option

val n_way_join_knowns :
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  ('a1 -> 'a3 -> (Index.t * 'a4) list -> ('a4 * 'a1) option) ->
  ('a2 -> 'a2 -> bool) ->
  ('a2 -> 'a2 -> 'a2) ->
  ('a3 list -> 'a3 or_unknown_or_bottom) ->
  'a1 ->
  (Index.t * ('a2, 'a3, 'a4, env_extension) row_like_case Or_unknown.t) list ->
  (('a2, 'a3, 'a4, env_extension) row_like_case Or_unknown.t * 'a1) Or_bottom.t
  option

val n_way_join_row_like :
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  ('a1 -> 'a3 -> (Index.t * 'a4) list -> ('a4 * 'a1) option) ->
  ('a2 -> 'a2 -> bool) ->
  ('a2 -> 'a2 -> 'a2) ->
  ('a3 list -> 'a3 or_unknown_or_bottom) ->
  (('a1 ->
   (Index.t * ('a2, 'a3, 'a4, env_extension) row_like_case Or_unknown.t) list ->
   (('a2, 'a3, 'a4, env_extension) row_like_case Or_unknown.t * 'a1) Or_bottom.t
   option) ->
  'a1 ->
  (Index.t * ('a5 * ('a2, 'a3, 'a4, env_extension) row_like_case Or_bottom.t))
  list ->
  ('a5 * 'a1) option) ->
  'a1 ->
  (Index.t * ('a5 * ('a2, 'a3, 'a4, env_extension) row_like_case Or_bottom.t))
  list ->
  (Index.t * ('a2, 'a3, 'a4, env_extension) row_like_case Or_bottom.t) list ->
  ( 'a1,
    'a5 * ('a2, 'a3, 'a4, env_extension) row_like_case Or_bottom.t )
  n_way_join_result

val n_way_join_block_shape :
  (block_shape -> block_shape -> bool) ->
  block_shape list ->
  block_shape or_unknown_or_bottom

val n_way_join_generic_product :
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * flambda_type finite_map) list ->
  (flambda_type finite_map * 'a1) option

val n_way_join_function_slot_indexed_product :
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * flambda_type finite_map) list ->
  (flambda_type finite_map * 'a1) option

val n_way_join_value_slot_indexed_product :
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * flambda_type finite_map) list ->
  (flambda_type finite_map * 'a1) option

val fields_the_same :
  (flambda_type -> flambda_type -> bool) ->
  nat ->
  flambda_type list ->
  flambda_type list ->
  bool

val import_types :
  ('a1 -> flambda_type -> 'a1 option) -> 'a1 -> flambda_type list -> 'a1 option

val join_fields :
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  block_shape ->
  (Index.t * flambda_type list) list ->
  nat ->
  nat ->
  (flambda_type list * 'a1) option

val n_way_join_int_indexed_product :
  ('a1 -> flambda_type -> 'a1 option) ->
  (flambda_type -> flambda_type -> bool) ->
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  block_shape ->
  (Index.t * flambda_type list) list ->
  (flambda_type list * 'a1) option

val n_way_join_closures_entry :
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * closures_entry) list ->
  (closures_entry * 'a1) option

val n_way_join_row_like_for_blocks :
  ('a1 -> flambda_type -> 'a1 option) ->
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  (flambda_type -> flambda_type -> bool) ->
  (block_shape -> block_shape -> bool) ->
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * row_like_for_blocks) list ->
  ('a1, row_like_for_blocks) n_way_join_result

val n_way_join_row_like_for_closures :
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * row_like_for_closures) list ->
  (row_like_for_closures * 'a1) option

val n_way_join_variant :
  ('a1 -> flambda_type -> 'a1 option) ->
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  (flambda_type -> flambda_type -> bool) ->
  (block_shape -> block_shape -> bool) ->
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * row_like_for_blocks Or_unknown.t) list ->
  (Index.t * flambda_type Or_unknown.t) list ->
  (Index.t * variant_extensions) list ->
  ( 'a1,
    (row_like_for_blocks Or_unknown.t * flambda_type Or_unknown.t)
    * variant_extensions )
  n_way_join_result

val n_way_join_head_of_kind_value_non_null :
  ('a1 ->
  flambda_kind ->
  (Index.t * simple) list ->
  (simple Or_bottom.t * 'a1) option) ->
  ('a1 -> flambda_type -> 'a1 option) ->
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  (flambda_type -> flambda_type -> bool) ->
  (block_shape -> block_shape -> bool) ->
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * head_of_kind_value_non_null) list ->
  ('a1, head_of_kind_value_non_null) n_way_join_result

val n_way_join_head_of_kind_value :
  ('a1 ->
  flambda_kind ->
  (Index.t * simple) list ->
  (simple Or_bottom.t * 'a1) option) ->
  ('a1 -> flambda_type -> 'a1 option) ->
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  (flambda_type -> flambda_type -> bool) ->
  (block_shape -> block_shape -> bool) ->
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * head_of_kind_value) list ->
  ('a1, head_of_kind_value) n_way_join_result

val n_way_join_expanded_head :
  ('a1 -> Index.t -> Typing_env.t option) ->
  ('a1 ->
  flambda_kind ->
  (Index.t * simple) list ->
  (simple Or_bottom.t * 'a1) option) ->
  ('a1 -> flambda_type -> 'a1 option) ->
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  (Typing_env.t ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate Or_bottom.t) ->
  (flambda_type -> flambda_type -> bool) ->
  (block_shape -> block_shape -> bool) ->
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  flambda_kind ->
  (Index.t * Expanded_type.t) list ->
  ('a1, Expanded_type.t) n_way_join_result

val expand_heads :
  ('a1 -> Index.t -> Typing_env.t option) ->
  (Typing_env.t -> flambda_type -> Expanded_type.t option) ->
  'a1 ->
  (Index.t * flambda_type) list ->
  (Index.t * Expanded_type.t) list option

val n_way_join_body :
  ('a1 -> Index.t -> Typing_env.t option) ->
  ('a1 ->
  flambda_kind ->
  (Index.t * simple) list ->
  (simple Or_bottom.t * 'a1) option) ->
  ('a1 -> flambda_type -> 'a1 option) ->
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  (Typing_env.t -> flambda_type -> Expanded_type.t option) ->
  (Typing_env.t ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate Or_bottom.t) ->
  (flambda_type -> flambda_type -> bool) ->
  (block_shape -> block_shape -> bool) ->
  ('a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result) ->
  'a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result

val n_way_join :
  ('a1 -> Index.t -> Typing_env.t option) ->
  ('a1 ->
  flambda_kind ->
  (Index.t * simple) list ->
  (simple Or_bottom.t * 'a1) option) ->
  ('a1 -> flambda_type -> 'a1 option) ->
  ('a1 ->
  (Index.t * env_extension) list ->
  (env_extension * 'a1) Or_bottom.t option) ->
  (Typing_env.t -> flambda_type -> Expanded_type.t option) ->
  (Typing_env.t ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate Or_bottom.t) ->
  (flambda_type -> flambda_type -> bool) ->
  (block_shape -> block_shape -> bool) ->
  nat ->
  'a1 ->
  (Index.t * flambda_type) list ->
  ('a1, flambda_type) n_way_join_result
