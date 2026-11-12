open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaBindingTime
open FlambdaExpandHead
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaMeetEnv
open FlambdaMeetGrammar
open FlambdaModel
open FlambdaTypeEqualSpec
open FlambdaTypeGrammar
open FlambdaTypeMeaningBoolSpec
open FlambdaTypingEnv
open List
open ListDef
open PeanoNat

val map_return_value :
  ('a1 -> 'a2) -> 'a1 meet_return_value -> 'a2 meet_return_value

val combine_meet_return_values :
  'a1 meet_return_value ->
  'a2 meet_return_value ->
  (unit -> 'a3) ->
  'a3 meet_return_value

val sequence_return_value :
  'a1 option meet_return_value -> 'a1 meet_return_value option

val set_meet :
  ('a1 -> 'a1 -> bool) ->
  ('a1 list -> 'a2) ->
  Meet_env.t ->
  'a1 list ->
  'a1 list ->
  'a2 Meet_result.t

type ('k, 'a) mapping_acc =
  { all_left : bool;
    all_right : bool;
    mapping : ('k * 'a) list;
    mapping_env : Meet_env.t
  }

type ('k, 'a) mapping_state = ('k, 'a) mapping_acc Or_bottom.t option

val meet_mapping :
  (Meet_env.t -> 'a2 -> 'a2 -> 'a2 Meet_result.t option) ->
  (('a1 ->
   'a2 option ->
   'a2 option ->
   ('a1, 'a2) mapping_state ->
   ('a1, 'a2) mapping_state) ->
  'a3 ->
  'a3 ->
  ('a1, 'a2) mapping_state ->
  ('a1, 'a2) mapping_state) ->
  Meet_env.t ->
  'a3 ->
  'a3 ->
  (('a1 * 'a2) list -> 'a3) ->
  'a3 Meet_result.t option

val map_meet :
  ('a1 -> 'a1 -> bool) ->
  (Meet_env.t -> 'a2 -> 'a2 -> 'a2 Meet_result.t option) ->
  Meet_env.t ->
  ('a1, 'a2) Keyed.finite_map ->
  ('a1, 'a2) Keyed.finite_map ->
  ('a1, 'a2) Keyed.finite_map Meet_result.t option

val combine_results2 :
  Meet_env.t ->
  (Meet_env.t -> 'a1 -> 'a1 -> 'a1 Meet_result.t option) ->
  (Meet_env.t -> 'a2 -> 'a2 -> 'a2 Meet_result.t option) ->
  'a1 ->
  'a1 ->
  'a2 ->
  'a2 ->
  ('a1 -> 'a2 -> 'a3) ->
  'a3 Meet_result.t option

val combine_results3 :
  Meet_env.t ->
  (Meet_env.t -> 'a1 -> 'a1 -> 'a1 Meet_result.t option) ->
  (Meet_env.t -> 'a2 -> 'a2 -> 'a2 Meet_result.t option) ->
  (Meet_env.t -> 'a3 -> 'a3 -> 'a3 Meet_result.t option) ->
  'a1 ->
  'a1 ->
  'a2 ->
  'a2 ->
  'a3 ->
  'a3 ->
  ('a1 -> 'a2 -> 'a3 -> 'a4) ->
  'a4 Meet_result.t option

val meet_code_id : Meet_env.t -> code_id -> code_id -> code_id Meet_result.t

val meet_alloc_mode :
  Meet_env.t -> Alloc_mode.t -> Alloc_mode.t -> Alloc_mode.t Meet_result.t

val meet_unknown :
  (Meet_env.t -> 'a1 -> 'a1 -> 'a1 Meet_result.t option) ->
  ('a1 -> bool) ->
  Meet_env.t ->
  'a1 Or_unknown.t ->
  'a1 Or_unknown.t ->
  'a1 Or_unknown.t Meet_result.t option

val meet_or_unknown_or_bottom :
  (Meet_env.t -> 'a1 -> 'a1 -> 'a2 Meet_result.t option) ->
  Meet_env.t ->
  'a1 or_unknown_or_bottom ->
  'a1 or_unknown_or_bottom ->
  'a2 Meet_result.t option

val relation_eqb : Relation.t -> Relation.t -> bool

val inverse_relation_eqb : Relation.t * name -> Relation.t * name -> bool

val head_of_kind_naked_immediate_from_descr :
  coq_Z list Or_unknown.t ->
  (Relation.t * name) list ->
  head_of_kind_naked_immediate Or_bottom.t

val head_of_kind_naked_immediate_from_descr_non_empty :
  coq_Z list Or_unknown.t ->
  (Relation.t * name) list ->
  head_of_kind_naked_immediate option

type reduce_acc =
  { reduce_imms : coq_Z list Or_unknown.t;
    reduce_relations : (Relation.t * name) list;
    reduce_changed : bool
  }

val reduce_head_of_kind_naked_immediate :
  Typing_env.t ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate Or_bottom.t

type 'a reverse_mapping_meet_return_value =
  { left_inputs_only : 'a;
    meet_return_value_of : 'a meet_return_value;
    right_inputs_only : 'a
  }

val meet_inverse_relations :
  (Relation.t * name) list ->
  (Relation.t * name) list ->
  (Relation.t * name) list reverse_mapping_meet_return_value

val is_tag : coq_Z -> bool

val is_structured_block : coq_Z -> bool

val immediate_or_blocks_with_these_tags :
  coq_Z list -> Alloc_mode.t -> flambda_type

type meet_choices =
  { type_of_get_tag_scrutinee : coq_Z list -> Alloc_mode.t -> flambda_type;
    define_again : bool;
    lift_variables_of_single_case : bool
  }

val compiler_choices : meet_choices

val repaired_choices : meet_choices

val extension_of_level : Typing_env_level.t -> env_extension

val meet :
  meet_expanded_head ->
  Meet_env.t ->
  flambda_type ->
  flambda_type ->
  flambda_type Meet_result.t option

val define_in_types :
  meet_choices -> Meet_env.t -> variable -> flambda_kind -> Meet_env.t option

val add_defined_vars :
  meet_choices -> Meet_env.t -> Typing_env_level.t -> Meet_env.t option

val meet_disjunction :
  (meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option) ->
  meet_choices ->
  meet_expanded_head ->
  (Meet_env.t -> 'a1 -> 'a1 -> 'a1 Meet_result.t option) ->
  (Meet_env.t -> 'a2 -> 'a2 -> 'a2 Meet_result.t option) ->
  (unit -> 'a1) ->
  (unit -> 'a2) ->
  Meet_env.t ->
  'a1 ->
  'a2 ->
  variant_extensions ->
  'a1 ->
  'a2 ->
  variant_extensions ->
  (('a1 * 'a2) * variant_extensions) Meet_result.t option

type row_like_state =
  { extra_variables : (variable * flambda_kind) list;
    result_env : Typing_env.t list option;
    result_is_t1 : bool;
    result_is_t2 : bool;
    avoid : variable list
  }

val not_t1 : row_like_state -> row_like_state

val not_t2 : row_like_state -> row_like_state

val update_refs : 'a1 meet_return_value -> row_like_state -> row_like_state

val union_extra_variables :
  (variable * flambda_kind) list ->
  (variable * flambda_kind) list ->
  (variable * flambda_kind) list option

val meet_row_like :
  (meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option) ->
  meet_choices ->
  meet_expanded_head ->
  (Meet_env.t -> 'a3 -> 'a3 -> 'a3 Meet_result.t option) ->
  ('a1 -> 'a1 -> bool) ->
  ('a1 -> 'a1 -> bool) ->
  ('a1 -> 'a1 -> 'a1) ->
  ('a2 -> 'a2 -> 'a2 Or_bottom.t) ->
  ('a5 -> bool) ->
  ('a5 -> ('a4 * ('a1, 'a2, 'a3, env_extension) row_like_case) option) ->
  (('a4 ->
   ('a1, 'a2, 'a3, env_extension) row_like_case Or_unknown.t option ->
   ('a1, 'a2, 'a3, env_extension) row_like_case Or_unknown.t option ->
   row_like_state ->
   (('a1, 'a2, 'a3, env_extension) row_like_case Or_unknown.t option
   * row_like_state)
   option) ->
  'a5 ->
  'a5 ->
  row_like_state ->
  ('a5 * row_like_state) option) ->
  Meet_env.t ->
  'a5 ->
  'a5 ->
  ('a1, 'a2, 'a3, env_extension) row_like_case Or_bottom.t ->
  ('a1, 'a2, 'a3, env_extension) row_like_case Or_bottom.t ->
  ('a5 * ('a1, 'a2, 'a3, env_extension) row_like_case Or_bottom.t) Meet_result.t
  option

val meet_relation :
  meet_expanded_head ->
  Meet_env.t ->
  variable option ->
  variable option ->
  variable option Meet_result.t option

val meet_function_type :
  Meet_env.t ->
  function_type Or_unknown.t ->
  function_type Or_unknown.t ->
  function_type Or_unknown.t Meet_result.t option

val meet_array_of_types :
  meet_expanded_head ->
  Meet_env.t ->
  flambda_type list ->
  flambda_type list ->
  nat ->
  flambda_type list Meet_result.t option

val meet_int_indexed_product :
  meet_expanded_head ->
  Meet_env.t ->
  flambda_type list ->
  flambda_type list ->
  flambda_type list Meet_result.t option

val meet_product_function_slot_indexed :
  meet_expanded_head ->
  Meet_env.t ->
  flambda_type finite_map ->
  flambda_type finite_map ->
  flambda_type finite_map Meet_result.t option

val meet_product_value_slot_indexed :
  meet_expanded_head ->
  Meet_env.t ->
  flambda_type finite_map ->
  flambda_type finite_map ->
  flambda_type finite_map Meet_result.t option

val meet_closures_entry :
  meet_expanded_head ->
  Meet_env.t ->
  closures_entry ->
  closures_entry ->
  closures_entry Meet_result.t option

val merge_fold_failing :
  ('a1 -> 'a1 -> bool) ->
  'a1 list ->
  ('a1 -> 'a2 option -> 'a3 option -> 'a5 -> ('a4 option * 'a5) option) ->
  ('a1, 'a2) Keyed.finite_map ->
  ('a1, 'a3) Keyed.finite_map ->
  'a5 ->
  (('a1, 'a4) Keyed.finite_map * 'a5) option

val meet_row_like_for_blocks :
  (meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option) ->
  meet_choices ->
  meet_expanded_head ->
  Meet_env.t ->
  row_like_for_blocks ->
  row_like_for_blocks ->
  row_like_for_blocks Meet_result.t option

val meet_row_like_for_closures :
  (meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option) ->
  meet_choices ->
  meet_expanded_head ->
  Meet_env.t ->
  row_like_for_closures ->
  row_like_for_closures ->
  row_like_for_closures Meet_result.t option

val type_of_get_tag_scrutinee_or_unknown :
  meet_choices -> coq_Z list -> Alloc_mode.t -> flambda_type Or_unknown.t

val reduce_inverse_relations :
  meet_choices ->
  meet_expanded_head ->
  Meet_env.t ->
  coq_Z list Or_unknown.t ->
  (Relation.t * name) list ->
  Meet_env.t Or_bottom.t option

val meet_head_of_kind_naked_immediate :
  meet_choices ->
  meet_expanded_head ->
  Meet_env.t ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate Meet_result.t option

val meet_head_of_kind_naked_number :
  Meet_env.t -> coq_Z list -> coq_Z list -> coq_Z list Meet_result.t

val meet_head_of_kind_rec_info :
  Meet_env.t -> unit -> unit -> unit Meet_result.t

val meet_head_of_kind_region : Meet_env.t -> unit -> unit -> unit Meet_result.t

val meet_variant :
  (meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option) ->
  meet_choices ->
  meet_expanded_head ->
  Meet_env.t ->
  variable option ->
  variable option ->
  row_like_for_blocks Or_unknown.t ->
  flambda_type Or_unknown.t ->
  variable option ->
  variable option ->
  row_like_for_blocks Or_unknown.t ->
  flambda_type Or_unknown.t ->
  variant_extensions ->
  variant_extensions ->
  ((((variable option * variable option) * row_like_for_blocks Or_unknown.t)
   * flambda_type Or_unknown.t)
  * variant_extensions)
  Meet_result.t
  option

val meet_head_of_kind_value_non_null :
  (meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option) ->
  meet_choices ->
  meet_expanded_head ->
  Meet_env.t ->
  head_of_kind_value_non_null ->
  head_of_kind_value_non_null ->
  head_of_kind_value_non_null Meet_result.t option

val meet_head_of_kind_value :
  (meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option) ->
  meet_choices ->
  meet_expanded_head ->
  Meet_env.t ->
  head_of_kind_value ->
  head_of_kind_value ->
  head_of_kind_value Meet_result.t option

val meet_expanded_head0 :
  (meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option) ->
  meet_choices ->
  meet_expanded_head ->
  Meet_env.t ->
  Expanded_type.head ->
  Expanded_type.head ->
  Expanded_type.t Meet_result.t option

val meet_expanded_head_step :
  (meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option) ->
  meet_choices ->
  meet_expanded_head ->
  meet_expanded_head

module Meet : sig
  val meet_expanded_head :
    (meet_expanded_head ->
    Scope.t ->
    Meet_env.t ->
    Typing_env.t ->
    Typing_env.t list ->
    Meet_env.t option) ->
    meet_choices ->
    nat ->
    meet_expanded_head

  val meet :
    (meet_expanded_head ->
    Scope.t ->
    Meet_env.t ->
    Typing_env.t ->
    Typing_env.t list ->
    Meet_env.t option) ->
    meet_choices ->
    nat ->
    Typing_env.t ->
    flambda_type ->
    flambda_type ->
    (flambda_type * Typing_env.t) Or_bottom.t option
end

module Flambda2_types : sig
  val add_equation :
    (meet_expanded_head ->
    Scope.t ->
    Meet_env.t ->
    Typing_env.t ->
    Typing_env.t list ->
    Meet_env.t option) ->
    meet_choices ->
    nat ->
    Typing_env.t ->
    name ->
    flambda_type ->
    Typing_env.t option

  val add_relation :
    (meet_expanded_head ->
    Scope.t ->
    Meet_env.t ->
    Typing_env.t ->
    Typing_env.t list ->
    Meet_env.t option) ->
    meet_choices ->
    nat ->
    Typing_env.t ->
    name ->
    simple ->
    flambda_type ->
    (variable -> head_of_kind_value) ->
    Typing_env.t option

  val is_null_of_simple : simple -> flambda_type

  val is_int_of_simple : simple -> flambda_type

  val get_tag_of_simple : simple -> flambda_type

  val add_is_null_relation :
    (meet_expanded_head ->
    Scope.t ->
    Meet_env.t ->
    Typing_env.t ->
    Typing_env.t list ->
    Meet_env.t option) ->
    meet_choices ->
    nat ->
    Typing_env.t ->
    name ->
    simple ->
    Typing_env.t option

  val add_is_int_relation :
    (meet_expanded_head ->
    Scope.t ->
    Meet_env.t ->
    Typing_env.t ->
    Typing_env.t list ->
    Meet_env.t option) ->
    meet_choices ->
    nat ->
    Typing_env.t ->
    name ->
    simple ->
    Typing_env.t option

  val add_get_tag_relation :
    (meet_expanded_head ->
    Scope.t ->
    Meet_env.t ->
    Typing_env.t ->
    Typing_env.t list ->
    Meet_env.t option) ->
    meet_choices ->
    nat ->
    Typing_env.t ->
    name ->
    simple ->
    Typing_env.t option
end
