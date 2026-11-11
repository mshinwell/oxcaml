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

(** val non_empty : 'a1 list -> bool **)

let non_empty = function [] -> false | _ :: _ -> true

(** val keys : ('a1, 'a2) Keyed.finite_map -> 'a1 list **)

let keys bindings = map fst bindings

(** val has_naked_number_types : naked_number_kind -> bool **)

let has_naked_number_types = function
  | Kind_naked_immediate -> false
  | _ -> true

(** val block_shape_canonical_b : block_shape -> bool **)

let block_shape_canonical_b = function
  | Scannable shape0 -> (
    match shape0 with
    | Value_only -> true
    | Mixed_record (_, flat_suffix) -> non_empty flat_suffix)
  | Float_record -> true

(** val descr_well_formed : ('a1 -> bool) -> 'a1 type_descr -> bool **)

let descr_well_formed head_well_formed = function
  | Ok a -> (
    match a with No_alias head -> head_well_formed head | Equals _ -> true)
  | _ -> true

(** val head_of_kind_naked_immediate_well_formed : head_of_kind_naked_immediate
    -> bool **)

let head_of_kind_naked_immediate_well_formed head =
  match head.naked_immediates with
  | Or_unknown.Known numbers -> non_empty numbers
  | Or_unknown.Unknown -> true

(** val block_product_fits : (nat, block_shape) row_like_index -> flambda_type
    list -> bool **)

let block_product_fits index maps_to =
  match index.index_domain with
  | Row_like_index_domain.Known size -> Nat.eqb (length maps_to) size
  | Row_like_index_domain.At_least size -> Nat.leb (length maps_to) size

(** val block_case_well_formed : (flambda_type -> bool) -> (env_extension ->
    bool) -> row_like_block_case -> bool **)

let block_case_well_formed type_well_formed0 env_extension_well_formed0 case =
  ((block_product_fits case.case_index case.case_maps_to
   && block_shape_canonical_b case.case_index.index_shape)
  && forallb type_well_formed0 case.case_maps_to)
  && env_extension_well_formed0 case.case_env_extension

(** val closures_index_has_slot : function_slot -> (set_of_closures_contents,
    unit) row_like_index -> bool **)

let closures_index_has_slot slot index =
  match index.index_domain with
  | Row_like_index_domain.Known contents ->
    among slot contents.contents_closures
  | Row_like_index_domain.At_least _ -> true

(** val closures_entry_slots_fit : (set_of_closures_contents, unit)
    row_like_index -> function_slot list -> function_slot list -> value_slot
    list -> bool **)

let closures_entry_slots_fit index function_slots closure_slots value_slots =
  ((all_among function_slots (closures_index_contents index).contents_closures
   && all_among closure_slots (closures_index_contents index).contents_closures
   )
  && all_among value_slots (closures_index_contents index).contents_value_slots
  )
  &&
  match index.index_domain with
  | Row_like_index_domain.Known contents ->
    all_among contents.contents_closures function_slots
  | Row_like_index_domain.At_least _ -> true

(** val type_well_formed : flambda_type -> bool **)

let rec type_well_formed = function
  | Type_value ty -> descr_well_formed head_of_kind_value_well_formed ty
  | Type_naked_immediate ty ->
    descr_well_formed head_of_kind_naked_immediate_well_formed ty
  | Type_naked_number (k, ty) ->
    has_naked_number_types k && descr_well_formed non_empty ty
  | _ -> true

(** val head_of_kind_value_well_formed : head_of_kind_value -> bool **)

and head_of_kind_value_well_formed = function
  | Head_of_kind_value (non_null, _) -> (
    match non_null with
    | Ok head0 -> head_of_kind_value_non_null_well_formed head0
    | _ -> true)

(** val head_of_kind_value_non_null_well_formed : head_of_kind_value_non_null ->
    bool **)

and head_of_kind_value_non_null_well_formed = function
  | Variant (_, immediates, _, blocks, extensions, _) -> (
    ((match immediates with
       | Or_unknown.Known ty ->
         kind_eqb (kind ty) (Naked_number Kind_naked_immediate)
         && type_well_formed ty
       | Or_unknown.Unknown -> true)
    &&
    match blocks with
    | Or_unknown.Known blocks0 -> row_like_for_blocks_well_formed blocks0
    | Or_unknown.Unknown -> true)
    &&
    match extensions with
    | No_extensions -> true
    | Ext (when_immediate, when_block) ->
      env_extension_well_formed when_immediate
      && env_extension_well_formed when_block)
  | Mutable_block _ -> true
  | Boxed_number (k, contents, _) ->
    kind_eqb (kind contents) (unboxed_kind k) && type_well_formed contents
  | Closures (by_function_slot, _) ->
    row_like_for_closures_well_formed by_function_slot
  | String strs -> non_empty strs

(** val row_like_for_blocks_well_formed : row_like_for_blocks -> bool **)

and row_like_for_blocks_well_formed = function
  | Row_like_for_blocks (known_tags, other_tags, _) -> (
    (Keyed.distinct Z.eqb (keys known_tags)
    && Keyed.for_all_bindings_b Z.eqb
         (fun _ case ->
           match case with
           | Or_unknown.Known case0 ->
             block_case_well_formed type_well_formed env_extension_well_formed
               case0
           | Or_unknown.Unknown -> true)
         known_tags)
    &&
    match other_tags with
    | Or_bottom.Ok case ->
      block_case_well_formed type_well_formed env_extension_well_formed case
    | Or_bottom.Bottom -> true)

(** val row_like_for_closures_well_formed : row_like_for_closures -> bool **)

and row_like_for_closures_well_formed = function
  | Row_like_for_closures known_closures ->
    distinct (keys known_closures)
    && Keyed.for_all_bindings_b Pos.eqb
         (fun slot case ->
           (closures_index_has_slot slot case.case_index
           && closures_entry_well_formed case.case_index case.case_maps_to)
           && env_extension_well_formed case.case_env_extension)
         known_closures

(** val closures_entry_well_formed : (set_of_closures_contents, unit)
    row_like_index -> closures_entry -> bool **)

and closures_entry_well_formed index = function
  | Closures_entry (function_types, closure_types, value_slot_types) ->
    ((((closures_entry_slots_fit index (domain function_types)
          (domain closure_types) (domain value_slot_types)
       && distinct (keys function_types))
      && distinct (keys closure_types))
     && distinct (keys value_slot_types))
    && Keyed.for_all_bindings_b Pos.eqb
         (fun _ ty -> kind_eqb (kind ty) Value && type_well_formed ty)
         closure_types)
    && Keyed.for_all_bindings_b Pos.eqb
         (fun _ -> type_well_formed)
         value_slot_types

(** val env_extension_well_formed : env_extension -> bool **)

and env_extension_well_formed = function
  | Env_extension equations ->
    Keyed.distinct name_eqb (keys equations)
    && Keyed.for_all_bindings_b name_eqb (fun _ -> type_well_formed) equations
