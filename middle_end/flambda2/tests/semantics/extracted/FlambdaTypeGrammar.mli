open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef
open Nat

type name =
  | Name_var of variable
  | Name_symbol of symbol

val simple_of_name : name -> simple

val name_eqb : name -> name -> bool

module Or_unknown : sig
  type 'a t =
    | Known of 'a
    | Unknown
end

module Or_bottom : sig
  type 'a t =
    | Ok of 'a
    | Bottom
end

type 'a or_unknown_or_bottom =
  | Unknown
  | Ok of 'a
  | Bottom

type 'head descr =
  | No_alias of 'head
  | Equals of simple

type 'head type_descr = 'head descr or_unknown_or_bottom

module Alloc_mode : sig
  type t =
    | Heap
    | Local
    | Heap_or_local
end

type is_null =
  | Not_null
  | Maybe_null of variable option

module Relation : sig
  type t =
    | Is_null
    | Is_int
    | Get_tag

  val of_const : t -> const -> coq_Z Or_bottom.t
end

type head_of_kind_naked_immediate =
  { naked_immediates : coq_Z list Or_unknown.t;
    inverse_relations : (Relation.t * name) list
  }

type scannable_block_shape =
  | Value_only
  | Mixed_record of nat * naked_number_kind list

type block_shape =
  | Scannable of scannable_block_shape
  | Float_record

val no_scan_tag : coq_Z

val double_array_tag : coq_Z

module Row_like_index_domain : sig
  type 'lattice t =
    | Known of 'lattice
    | At_least of 'lattice
end

type ('lattice, 'shape) row_like_index =
  { index_domain : 'lattice Row_like_index_domain.t;
    index_shape : 'shape
  }

type ('lattice, 'shape, 'maps_to, 'extension) row_like_case =
  { case_maps_to : 'maps_to;
    case_index : ('lattice, 'shape) row_like_index;
    case_env_extension : 'extension
  }

type set_of_closures_contents =
  { contents_closures : function_slot list;
    contents_value_slots : value_slot list
  }

type function_type = { function_type_code_id : code_id }

type flambda_type =
  | Type_value of head_of_kind_value type_descr
  | Type_naked_immediate of head_of_kind_naked_immediate type_descr
  | Type_naked_number of naked_number_kind * coq_Z list type_descr
  | Type_rec_info of unit type_descr
  | Type_region of unit type_descr

and head_of_kind_value =
  | Head_of_kind_value of
      head_of_kind_value_non_null or_unknown_or_bottom * is_null

and head_of_kind_value_non_null =
  | Variant of
      variable option
      * flambda_type Or_unknown.t
      * variable option
      * row_like_for_blocks Or_unknown.t
      * variant_extensions
      * bool
  | Mutable_block of Alloc_mode.t
  | Boxed_number of boxable_number * flambda_type * Alloc_mode.t
  | Closures of row_like_for_closures * Alloc_mode.t
  | String of coq_Z list list

and row_like_for_blocks =
  | Row_like_for_blocks of
      ( coq_Z,
        (nat, block_shape, flambda_type list, env_extension) row_like_case
        Or_unknown.t )
      Keyed.finite_map
      * (nat, block_shape, flambda_type list, env_extension) row_like_case
        Or_bottom.t
      * Alloc_mode.t

and row_like_for_closures =
  | Row_like_for_closures of
      ( set_of_closures_contents,
        unit,
        closures_entry,
        env_extension )
      row_like_case
      finite_map

and closures_entry =
  | Closures_entry of
      function_type Or_unknown.t finite_map
      * flambda_type finite_map
      * flambda_type finite_map

and env_extension = Env_extension of (name, flambda_type) Keyed.finite_map

and variant_extensions =
  | No_extensions
  | Ext of env_extension * env_extension

type row_like_block_case =
  (nat, block_shape, flambda_type list, env_extension) row_like_case

type row_like_closures_case =
  (set_of_closures_contents, unit, closures_entry, env_extension) row_like_case

val kind : flambda_type -> flambda_kind

val field_kinds : block_shape -> nat -> flambda_kind list

val unknown : flambda_kind -> flambda_type

val bottom : flambda_kind -> flambda_type

val alias_type_of : flambda_kind -> simple -> flambda_type

val get_alias_opt : flambda_type -> simple option

val is_obviously_bottom : flambda_type -> bool

val is_obviously_unknown : flambda_type -> bool

val this_const : const -> flambda_type

val this_tagged_immediate : coq_Z -> flambda_type

val this_naked_immediate : coq_Z -> flambda_type

val null : flambda_type

val any_non_null_value : flambda_type

val type_for_const : const -> flambda_type

val non_null_value : head_of_kind_value_non_null -> flambda_type

val create_variant :
  bool ->
  flambda_type Or_unknown.t ->
  row_like_for_blocks Or_unknown.t ->
  variant_extensions ->
  flambda_type

val mutable_block : Alloc_mode.t -> flambda_type

val create_closures : Alloc_mode.t -> row_like_for_closures -> flambda_type

val box_number : boxable_number -> flambda_type -> Alloc_mode.t -> flambda_type

val this_immutable_string : coq_Z list -> flambda_type

val these_naked_immediates : coq_Z list -> flambda_type

val empty_env_extension : env_extension

val row_like_for_blocks_bottom : row_like_for_blocks

val row_like_for_blocks_is_bottom : row_like_for_blocks -> bool

val row_like_for_blocks_create_exactly :
  coq_Z ->
  nat ->
  block_shape ->
  flambda_type list ->
  Alloc_mode.t ->
  row_like_for_blocks

val row_like_for_blocks_create_at_least :
  coq_Z ->
  nat ->
  block_shape ->
  flambda_type list ->
  Alloc_mode.t ->
  row_like_for_blocks

val row_like_for_blocks_create_at_least_unknown_tag :
  nat -> block_shape -> flambda_type list -> Alloc_mode.t -> row_like_for_blocks

val tag_immediate : flambda_type -> flambda_type

val any_tagged_immediate : flambda_type

val these_tagged_immediates : coq_Z list -> flambda_type

val any_block : flambda_type

val blocks_with_these_tags : coq_Z list -> Alloc_mode.t -> flambda_type

val immutable_block :
  bool ->
  coq_Z ->
  block_shape ->
  Alloc_mode.t ->
  flambda_type list ->
  flambda_type

val is_int_for_scrutinee : name -> flambda_type

val get_tag_for_block : name -> flambda_type

val is_null_for_scrutinee : name -> flambda_type

val exactly_this_closure :
  function_slot ->
  function_type Or_unknown.t finite_map ->
  flambda_type finite_map ->
  flambda_type finite_map ->
  Alloc_mode.t ->
  flambda_type

val at_least_this_closure :
  function_slot ->
  function_type Or_unknown.t finite_map ->
  flambda_type finite_map ->
  flambda_type finite_map ->
  Alloc_mode.t ->
  flambda_type

val free_variables_of_simple : simple -> variable list

val free_variables_of_name : name -> variable list

val free_variables_of_option : variable option -> variable list

val free_variables_of_descr :
  ('a1 -> variable list) -> 'a1 type_descr -> variable list

val free_variables_of_naked_immediate :
  head_of_kind_naked_immediate -> variable list

val free_variables_of_block_case :
  (flambda_type -> variable list) ->
  (env_extension -> variable list) ->
  row_like_block_case ->
  variable list

val free_variables : flambda_type -> variable list

val free_variables_of_head_of_kind_value : head_of_kind_value -> variable list

val free_variables_of_head_of_kind_value_non_null :
  head_of_kind_value_non_null -> variable list

val free_variables_of_row_like_for_blocks : row_like_for_blocks -> variable list

val free_variables_of_row_like_for_closures :
  row_like_for_closures -> variable list

val free_variables_of_closures_entry : closures_entry -> variable list

val free_variables_of_env_extension : env_extension -> variable list

val block_shape_element_kind : block_shape -> nat -> flambda_kind option

val const_of_naked_number : naked_number_kind -> coq_Z -> const

val simple_must_be_const : simple -> const option

val must_be_singleton : flambda_type -> const option option

val head_of_kind_value_null : head_of_kind_value

val head_of_kind_value_tagged_immediate : coq_Z -> head_of_kind_value

val set_of_closures_contents_equal :
  set_of_closures_contents -> set_of_closures_contents -> bool

val set_of_closures_contents_subset :
  set_of_closures_contents -> set_of_closures_contents -> bool

val set_of_closures_contents_union :
  set_of_closures_contents ->
  set_of_closures_contents ->
  set_of_closures_contents

val set_of_closures_contents_inter :
  set_of_closures_contents ->
  set_of_closures_contents ->
  set_of_closures_contents

val unknown_like : flambda_type -> flambda_type

val bottom_like : flambda_type -> flambda_type

val unknown_from_shape : block_shape -> nat -> flambda_type option

val unknown_with_subkind : flambda_kind -> flambda_type

val kind_for_const : const -> flambda_kind

val is_alias_of_name : flambda_type -> name -> bool

val these_naked_numbers : naked_number_kind -> coq_Z list -> flambda_type

val all_bools : coq_Z list

val any_tagged_bool : flambda_type

val any_naked_bool : flambda_type

val any_tagged_immediate_or_null : flambda_type

val tagged_immediate_alias_to : variable -> flambda_type

val unboxed_number_kind : boxable_number -> naked_number_kind

val boxed_number_alias_to :
  boxable_number -> variable -> Alloc_mode.t -> flambda_type

val this_boxed_number : boxable_number -> coq_Z -> Alloc_mode.t -> flambda_type

val these_boxed_numbers :
  boxable_number -> coq_Z list -> Alloc_mode.t -> flambda_type

val any_boxed_number : boxable_number -> flambda_type

module Open_or_closed : sig
  type t =
    | Open of coq_Z Or_unknown.t
    | Closed of coq_Z
end

val row_like_for_blocks_create :
  block_shape ->
  flambda_type list ->
  Open_or_closed.t ->
  Alloc_mode.t ->
  row_like_for_blocks option

val unknown_types_from_shape : block_shape -> nat -> flambda_type list option

val size_at_least_field_tys :
  block_shape -> variable -> nat -> flambda_type list option

val immutable_block_with_size_at_least :
  coq_Z Or_unknown.t -> nat -> block_shape -> variable -> flambda_type option

val closure_with_at_least_these_function_slots :
  function_slot -> simple finite_map -> flambda_type

val static_closure_with_this_code :
  function_slot -> symbol option -> code_id -> flambda_type

val closure_with_at_least_these_value_slots :
  function_slot -> (variable * flambda_kind) finite_map -> flambda_type

val closure_with_at_least_this_value_slot :
  function_slot -> value_slot -> variable -> flambda_kind -> flambda_type
