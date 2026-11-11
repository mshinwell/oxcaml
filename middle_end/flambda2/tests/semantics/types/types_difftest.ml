(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(* The types library of the compiler against its Rocq model.

   Each function that the model has (FlambdaTypeGrammar.v, extracted) is run on
   generated inputs beside the function of the compiler that it transcribes, and
   the two answers are compared through the converter (type_converter.ml). What
   is printed is, for each comparison, how many cases were run, how many agreed,
   how many could not be run and why, and every disagreement with the seed of
   its case and a shrunk input.

   Everything is seeded and nothing depends on time or on the machine: the
   output is the same on every run, and is kept in types_difftest.expected. The
   number of cases of a comparison is its [~count] below.

   The functions of the compiler are those of the modules of its types library,
   which the build names [Flambda2_types__...]; the library does not export
   them. *)

open Flambda2_identifiers
open Flambda2_kinds
open Flambda2_numbers
open Flambda2_term_basics
open Flambda2_bound_identifiers
open Flambda2_lattices
open Flambda2_nominal
open Type_comparisons
module K = Flambda_kind
module TG = Flambda2_types__Type_grammar
module TE = Flambda2_types__Typing_env
module MTC = Flambda2_types__More_type_creators
module Binary = Flambda2_types__Meet_and_join
module N_way = Flambda2_types__Meet_and_n_way_join
module Binary_join = Flambda2_types__Join_levels_old
module N_way_join = Flambda2_types__Join_env
module ME = Flambda2_types__Meet_env
module M = Flambda2_rocq_semantics.FlambdaModel
module MK = Flambda2_rocq_semantics.FlambdaKindModel
module MT = Flambda2_rocq_semantics.FlambdaTypeGrammar
module V = Flambda2_rocq_semantics.FlambdaValueSpec
module Meaning = Flambda2_rocq_semantics.FlambdaTypeMeaningBoolSpec
module Primitive_spec = Flambda2_rocq_semantics.FlambdaPrimitiveSpec
module Type_equal = Flambda2_rocq_semantics.FlambdaTypeEqualSpec
module Z = Flambda2_rocq_semantics.BinInt.Z
module Converter = Flambda2_rocq_types_converter.Type_converter
module Model_names = Flambda2_rocq_types_converter.Model_names
module Model_type = Flambda2_rocq_types_converter.Model_type
module N = Flambda2_rocq_types_converter.Model_numbers
module G = Type_generator
module Random = Minicheck.Splittable_random

(* How a join decides that the types it is given are one type, which it then
   keeps instead of joining: the compiler's flag [-flambda2-join-sharing]. With
   the default, physical equality, the result of a join depends on how its
   arguments are shared in memory (T7-7). The model has no physical equality:
   the tests run with the structural setting, and the comparisons of shared and
   unshared arguments are run with the default as well. *)
let with_join_sharing (setting : Oxcaml_flags.join_sharing) (f : unit -> 'a) :
    'a =
  let before = !Oxcaml_flags.Flambda2.join_sharing in
  Oxcaml_flags.Flambda2.join_sharing := Oxcaml_flags.Set setting;
  Fun.protect f ~finally:(fun () ->
      Oxcaml_flags.Flambda2.join_sharing := before)

(* ======================================================================== *)
(* The names of the tests                                                   *)
(* ======================================================================== *)

(* A few names of each sort, made once, numbered in this order. The variables
   and the symbols are defined in a typing environment, with nothing known of
   them, for the functions of the compiler that want one. *)
type names =
  { numbering : Model_names.t;
    pool : G.pool;
    env : TE.t;
    (* The variables and the symbols that [env] defines, with their kinds. *)
    defined : (Name.t * K.t) list;
    (* A parameter of a continuation of each kind, for the joins. They are not
       in the pool: no generated type mentions them. *)
    parameters : (MK.flambda_kind * Variable.t) list;
    (* A variable of kind value that only one use of a continuation binds, for
       the chosen joins. It is numbered after the variables of the tests: what a
       join says of it is read like what it says of a variable of its own. *)
    local : Variable.t;
    (* A naked immediate that a join may have its source define for types only,
       for the chosen joins. It is numbered after [local], and read like it. *)
    for_types_only : Variable.t;
    (* The variables of the tests are numbered from 1 to this. *)
    variables_of_the_tests : int;
    (* The variables numbered up to this are printed by their numbers: those of
       the tests, [local] and [for_types_only]. *)
    variables_with_a_name : int
  }

let create_names () : names =
  let numbering = Model_names.create () in
  let unit = Current_unit.get_cu_exn () in
  let variables kind names =
    List.map (fun name -> Variable.create name kind) names
  in
  let value_variables = variables K.value ["x"; "y"; "z"] in
  let naked_immediate_variables = variables K.naked_immediate ["i"; "j"] in
  let naked_float_variables = variables K.naked_float ["f"] in
  let region_variables = variables K.region ["r"] in
  let rec_info_variables = variables K.rec_info ["d"] in
  let symbols =
    List.map
      (fun name -> Symbol.create unit (Linkage_name.of_string name))
      ["s"; "t"]
  in
  let code_ids =
    List.map
      (fun name -> Code_id.create ~name ~debug:Debuginfo.none unit)
      ["c"; "c'"]
  in
  let function_slots =
    List.map (fun name -> Function_slot.create unit ~name ~size:2) ["g"; "h"]
  in
  let value_slots =
    List.map
      (fun name ->
        Value_slot.create unit ~name ~is_always_immediate:false K.value)
      ["w"; "w'"]
  in
  let number (sort : _ Model_names.sort) = List.map sort.number in
  let all_variables =
    value_variables @ naked_immediate_variables @ naked_float_variables
    @ region_variables @ rec_info_variables
  in
  let env =
    List.fold_left
      (fun env var ->
        TE.add_definition env
          (Bound_name.create_var
             (Bound_var.create var Flambda_debug_uid.none Name_mode.normal))
          (Variable.kind var))
      (TE.create ~machine_width ~resolver:(fun _ -> None))
      all_variables
  in
  let env =
    List.fold_left
      (fun env symbol ->
        TE.add_definition env (Bound_name.create_symbol symbol) K.value)
      env symbols
  in
  let defined =
    List.map (fun var -> Name.var var, Variable.kind var) all_variables
    @ List.map (fun symbol -> Name.symbol symbol, K.value) symbols
  in
  let parameters =
    List.map
      (fun kind -> kind, Variable.create "p" (Converter.kind_of_model kind))
      G.all_kinds
  in
  let local = Variable.create "u" K.value in
  let for_types_only = Variable.create "n" K.naked_immediate in
  let value_variables = number numbering.variables value_variables in
  let naked_immediate_variables =
    number numbering.variables naked_immediate_variables
  in
  let naked_float_variables =
    number numbering.variables naked_float_variables
  in
  let region_variables = number numbering.variables region_variables in
  let rec_info_variables = number numbering.variables rec_info_variables in
  (* The parameters are numbered after the variables of the pool. *)
  List.iter
    (fun (_, parameter) ->
      ignore (numbering.variables.number parameter : N.positive))
    parameters;
  ignore (numbering.variables.number local : N.positive);
  ignore (numbering.variables.number for_types_only : N.positive);
  { numbering;
    pool =
      { value_variables;
        naked_immediate_variables;
        naked_float_variables;
        region_variables;
        rec_info_variables;
        symbols = number numbering.symbols symbols;
        code_ids = number numbering.code_ids code_ids;
        function_slots = number numbering.function_slots function_slots;
        value_slots = number numbering.value_slots value_slots;
        unknown_name = N.positive_of_int 1000
      };
    env;
    defined;
    parameters;
    local;
    for_types_only;
    variables_of_the_tests = List.length all_variables + List.length parameters;
    variables_with_a_name =
      List.length all_variables + List.length parameters + 2
  }

let parameter (names : names) (kind : MK.flambda_kind) : Variable.t =
  List.assoc kind names.parameters

(* ======================================================================== *)
(* The comparisons of one type                                              *)
(* ======================================================================== *)

(* The comparisons themselves are in type_comparisons.ml, which the other tools
   of this directory use too. *)

let to_compiler (names : names) (t : MT.flambda_type) : TG.t =
  Converter.type_of_model names.numbering machine_width t

let to_model (names : names) (t : TG.t) : MT.flambda_type =
  Converter.type_to_model names.numbering t

let both (names : names) (m : MT.flambda_type) : both =
  { model = m; compiler = to_compiler names m }

let comparisons_of_one_type (names : names) : both comparison list =
  Type_comparisons.comparisons_of_one_type names.numbering

let well_formed_types (names : names) : both comparison list =
  Type_comparisons.well_formed_types names.numbering

let round_trip_from_the_compiler (names : names) : both comparison list =
  Type_comparisons.round_trip_from_the_compiler names.numbering names.env

(* ======================================================================== *)
(* The creation functions                                                   *)
(* ======================================================================== *)

(* A call of a creation function that the model has, with its arguments as the
   model has them. It is run in the model as it is, and in the compiler on the
   arguments converted; the two types are then compared. *)
type slots_and_types =
  { this_function_slot : M.function_slot;
    function_types : (M.function_slot * MT.function_type MT.Or_unknown.t) list;
    closure_types : (M.function_slot * MT.flambda_type) list;
    value_slot_types : (M.value_slot * MT.flambda_type) list;
    closure_alloc_mode : MT.Alloc_mode.t
  }

type block =
  { tag : N.z;
    shape : MT.block_shape;
    fields : MT.flambda_type list;
    block_alloc_mode : MT.Alloc_mode.t
  }

type call =
  | Unknown of MK.flambda_kind
  | Bottom of MK.flambda_kind
  | Alias_type_of of MK.flambda_kind * M.simple
  | Type_for_const of M.const
  | Null
  | Any_non_null_value
  | This_tagged_immediate of N.z
  | This_naked_immediate of N.z
  | These_naked_immediates of N.z list
  | These_tagged_immediates of N.z list
  | Any_tagged_immediate
  | Any_block
  | Tag_immediate of MT.flambda_type
  | Box_number of MK.boxable_number * MT.flambda_type * MT.Alloc_mode.t
  | Mutable_block of MT.Alloc_mode.t
  | This_immutable_string of N.z list
  | Create_variant of
      bool
      * MT.flambda_type MT.Or_unknown.t
      * MT.row_like_for_blocks MT.Or_unknown.t
      * MT.variant_extensions
  | Create_closures of MT.Alloc_mode.t * MT.row_like_for_closures
  | Blocks_with_these_tags of N.z list * MT.Alloc_mode.t
  | Immutable_block of bool * block
  | Row_like_create_exactly of block
  | Row_like_create_at_least of block
  | Row_like_create_at_least_unknown_tag of block
  | Is_int_for_scrutinee of MT.name
  | Get_tag_for_block of MT.name
  | Is_null_for_scrutinee of MT.name
  | Exactly_this_closure of slots_and_types
  | At_least_this_closure of slots_and_types
  | Unknown_like of MT.flambda_type
  | Bottom_like of MT.flambda_type
  | Unknown_from_shape of MT.block_shape * int
  | Unknown_with_subkind of MK.flambda_kind
  | Kind_for_const of M.const
  | These_naked_numbers of MK.naked_number_kind * N.z list
  | Any_tagged_bool
  | Any_naked_bool
  | Any_tagged_immediate_or_null
  | Tagged_immediate_alias_to of M.variable
  | Boxed_number_alias_to of MK.boxable_number * M.variable * MT.Alloc_mode.t
  | This_boxed_number of MK.boxable_number * N.z * MT.Alloc_mode.t
  | These_boxed_numbers of MK.boxable_number * N.z list * MT.Alloc_mode.t
  | Any_boxed_number of MK.boxable_number
  | Row_like_create of block * MT.Open_or_closed.t
      (** The tag is that of the second argument, and not the block's. *)
  | Immutable_block_with_size_at_least of
      N.z MT.Or_unknown.t * int * MT.block_shape * M.variable
  | Closure_with_at_least_these_function_slots of
      M.function_slot * (M.function_slot * M.simple) list
  | Static_closure_with_this_code of
      M.function_slot * M.symbol option * M.code_id
  | Closure_with_at_least_these_value_slots of
      M.function_slot * (M.value_slot * (M.variable * MK.flambda_kind)) list
  | Closure_with_at_least_this_value_slot of
      M.function_slot * M.value_slot * M.variable * MK.flambda_kind

let name_of_call (call : call) =
  match call with
  | Unknown _ -> "unknown"
  | Bottom _ -> "bottom"
  | Alias_type_of _ -> "alias_type_of"
  | Type_for_const _ -> "type_for_const"
  | Null -> "null"
  | Any_non_null_value -> "any_non_null_value"
  | This_tagged_immediate _ -> "this_tagged_immediate"
  | This_naked_immediate _ -> "this_naked_immediate"
  | These_naked_immediates _ -> "these_naked_immediates"
  | These_tagged_immediates _ -> "these_tagged_immediates"
  | Any_tagged_immediate -> "any_tagged_immediate"
  | Any_block -> "any_block"
  | Tag_immediate _ -> "tag_immediate"
  | Box_number _ -> "box_number"
  | Mutable_block _ -> "mutable_block"
  | This_immutable_string _ -> "this_immutable_string"
  | Create_variant _ -> "create_variant"
  | Create_closures _ -> "create_closures"
  | Blocks_with_these_tags _ -> "blocks_with_these_tags"
  | Immutable_block _ -> "immutable_block"
  | Row_like_create_exactly _ -> "row_like_for_blocks_create_exactly"
  | Row_like_create_at_least _ -> "row_like_for_blocks_create_at_least"
  | Row_like_create_at_least_unknown_tag _ ->
    "row_like_for_blocks_create_at_least_unknown_tag"
  | Is_int_for_scrutinee _ -> "is_int_for_scrutinee"
  | Get_tag_for_block _ -> "get_tag_for_block"
  | Is_null_for_scrutinee _ -> "is_null_for_scrutinee"
  | Exactly_this_closure _ -> "exactly_this_closure"
  | At_least_this_closure _ -> "at_least_this_closure"
  | Unknown_like _ -> "unknown_like"
  | Bottom_like _ -> "bottom_like"
  | Unknown_from_shape _ -> "unknown_from_shape"
  | Unknown_with_subkind _ -> "unknown_with_subkind, of a kind"
  | Kind_for_const _ -> "kind_for_const, as the unknown type of the kind"
  | These_naked_numbers _ -> "these_naked_numbers"
  | Any_tagged_bool -> "any_tagged_bool"
  | Any_naked_bool -> "any_naked_bool"
  | Any_tagged_immediate_or_null -> "any_tagged_immediate_or_null"
  | Tagged_immediate_alias_to _ -> "tagged_immediate_alias_to"
  | Boxed_number_alias_to _ -> "boxed_number_alias_to"
  | This_boxed_number _ -> "this_boxed_number"
  | These_boxed_numbers _ -> "these_boxed_numbers"
  | Any_boxed_number _ -> "any_boxed_number"
  | Row_like_create _ -> "row_like_for_blocks_create"
  | Immutable_block_with_size_at_least _ -> "immutable_block_with_size_at_least"
  | Closure_with_at_least_these_function_slots _ ->
    "closure_with_at_least_these_function_slots"
  | Static_closure_with_this_code _ -> "static_closure_with_this_code"
  | Closure_with_at_least_these_value_slots _ ->
    "closure_with_at_least_these_value_slots"
  | Closure_with_at_least_this_value_slot _ ->
    "closure_with_at_least_this_value_slot"

let names_of_calls =
  [ "unknown";
    "bottom";
    "alias_type_of";
    "type_for_const";
    "null";
    "any_non_null_value";
    "this_tagged_immediate";
    "this_naked_immediate";
    "these_naked_immediates";
    "these_tagged_immediates";
    "any_tagged_immediate";
    "any_block";
    "tag_immediate";
    "box_number";
    "mutable_block";
    "this_immutable_string";
    "create_variant";
    "create_closures";
    "blocks_with_these_tags";
    "immutable_block";
    "row_like_for_blocks_create_exactly";
    "row_like_for_blocks_create_at_least";
    "row_like_for_blocks_create_at_least_unknown_tag";
    "is_int_for_scrutinee";
    "get_tag_for_block";
    "is_null_for_scrutinee";
    "exactly_this_closure";
    "at_least_this_closure";
    "unknown_like";
    "bottom_like";
    "unknown_from_shape";
    "unknown_with_subkind, of a kind";
    "kind_for_const, as the unknown type of the kind";
    "these_naked_numbers";
    "any_tagged_bool";
    "any_naked_bool";
    "any_tagged_immediate_or_null";
    "tagged_immediate_alias_to";
    "boxed_number_alias_to";
    "this_boxed_number";
    "these_boxed_numbers";
    "any_boxed_number";
    "row_like_for_blocks_create";
    "immutable_block_with_size_at_least";
    "closure_with_at_least_these_function_slots";
    "static_closure_with_this_code";
    "closure_with_at_least_these_value_slots";
    "closure_with_at_least_this_value_slot" ]

(* A row-like structure of blocks as a type, to compare it as one. *)
let blocks_as_type_of_model (blocks : MT.row_like_for_blocks) =
  MT.create_variant false MT.Or_unknown.Unknown (MT.Or_unknown.Known blocks)
    MT.No_extensions

let blocks_as_type_of_compiler (blocks : TG.row_like_for_blocks) =
  TG.create_variant ~is_unique:false ~immediates:Unknown ~blocks:(Known blocks)
    ~extensions:No_extensions

(* A function of the model that answers [None] where the compiler's function
   stops (a fatal error, an index outside an array) has no type to compare: the
   compiler's function is then to stop too. *)
exception No_answer

let call_in_the_model (call : call) : MT.flambda_type =
  let answer (result : _ option) =
    match result with Some result -> result | None -> raise No_answer
  in
  match call with
  | Unknown kind -> MT.unknown kind
  | Bottom kind -> MT.bottom kind
  | Alias_type_of (kind, simple) -> MT.alias_type_of kind simple
  | Type_for_const const -> MT.type_for_const const
  | Null -> MT.null
  | Any_non_null_value -> MT.any_non_null_value
  | This_tagged_immediate i -> MT.this_tagged_immediate i
  | This_naked_immediate i -> MT.this_naked_immediate i
  | These_naked_immediates imms -> MT.these_naked_immediates imms
  | These_tagged_immediates imms -> MT.these_tagged_immediates imms
  | Any_tagged_immediate -> MT.any_tagged_immediate
  | Any_block -> MT.any_block
  | Tag_immediate t -> MT.tag_immediate t
  | Box_number (number, contents, alloc_mode) ->
    MT.box_number number contents alloc_mode
  | Mutable_block alloc_mode -> MT.mutable_block alloc_mode
  | This_immutable_string bytes -> MT.this_immutable_string bytes
  | Create_variant (is_unique, immediates, blocks, extensions) ->
    MT.create_variant is_unique immediates blocks extensions
  | Create_closures (alloc_mode, closures) ->
    MT.create_closures alloc_mode closures
  | Blocks_with_these_tags (tags, alloc_mode) ->
    MT.blocks_with_these_tags tags alloc_mode
  | Immutable_block (is_unique, { tag; shape; fields; block_alloc_mode }) ->
    MT.immutable_block is_unique tag shape block_alloc_mode fields
  | Row_like_create_exactly { tag; shape; fields; block_alloc_mode } ->
    blocks_as_type_of_model
      (MT.row_like_for_blocks_create_exactly tag
         (N.nat_of_int (List.length fields))
         shape fields block_alloc_mode)
  | Row_like_create_at_least { tag; shape; fields; block_alloc_mode } ->
    blocks_as_type_of_model
      (MT.row_like_for_blocks_create_at_least tag
         (N.nat_of_int (List.length fields))
         shape fields block_alloc_mode)
  | Row_like_create_at_least_unknown_tag
      { tag = _; shape; fields; block_alloc_mode } ->
    blocks_as_type_of_model
      (MT.row_like_for_blocks_create_at_least_unknown_tag
         (N.nat_of_int (List.length fields))
         shape fields block_alloc_mode)
  | Is_int_for_scrutinee name -> MT.is_int_for_scrutinee name
  | Get_tag_for_block name -> MT.get_tag_for_block name
  | Is_null_for_scrutinee name -> MT.is_null_for_scrutinee name
  | Exactly_this_closure
      { this_function_slot;
        function_types;
        closure_types;
        value_slot_types;
        closure_alloc_mode
      } ->
    MT.exactly_this_closure this_function_slot function_types closure_types
      value_slot_types closure_alloc_mode
  | At_least_this_closure
      { this_function_slot;
        function_types;
        closure_types;
        value_slot_types;
        closure_alloc_mode
      } ->
    MT.at_least_this_closure this_function_slot function_types closure_types
      value_slot_types closure_alloc_mode
  | Unknown_like t -> MT.unknown_like t
  | Bottom_like t -> MT.bottom_like t
  | Unknown_from_shape (shape, index) ->
    answer (MT.unknown_from_shape shape (N.nat_of_int index))
  | Unknown_with_subkind kind -> MT.unknown_with_subkind kind
  | Kind_for_const const -> MT.unknown (MT.kind_for_const const)
  | These_naked_numbers (kind, numbers) -> MT.these_naked_numbers kind numbers
  | Any_tagged_bool -> MT.any_tagged_bool
  | Any_naked_bool -> MT.any_naked_bool
  | Any_tagged_immediate_or_null -> MT.any_tagged_immediate_or_null
  | Tagged_immediate_alias_to variable -> MT.tagged_immediate_alias_to variable
  | Boxed_number_alias_to (number, variable, alloc_mode) ->
    MT.boxed_number_alias_to number variable alloc_mode
  | This_boxed_number (number, i, alloc_mode) ->
    MT.this_boxed_number number i alloc_mode
  | These_boxed_numbers (number, numbers, alloc_mode) ->
    MT.these_boxed_numbers number numbers alloc_mode
  | Any_boxed_number number -> MT.any_boxed_number number
  | Row_like_create
      ({ tag = _; shape; fields; block_alloc_mode }, open_or_closed) ->
    blocks_as_type_of_model
      (answer
         (MT.row_like_for_blocks_create shape fields open_or_closed
            block_alloc_mode))
  | Immutable_block_with_size_at_least (tag, n, shape, x) ->
    answer (MT.immutable_block_with_size_at_least tag (N.nat_of_int n) shape x)
  | Closure_with_at_least_these_function_slots (function_slot, bindings) ->
    MT.closure_with_at_least_these_function_slots function_slot bindings
  | Static_closure_with_this_code (function_slot, symbol, code) ->
    MT.static_closure_with_this_code function_slot symbol code
  | Closure_with_at_least_these_value_slots (function_slot, value_slots) ->
    MT.closure_with_at_least_these_value_slots function_slot value_slots
  | Closure_with_at_least_this_value_slot
      (function_slot, value_slot, variable, kind) ->
    MT.closure_with_at_least_this_value_slot function_slot value_slot variable
      kind

exception No_such_function of string

let call_in_the_compiler (names : names) (call : call) : TG.t =
  let module C = Converter in
  let numbering = names.numbering in
  let ty = to_compiler names in
  let immediate = C.in_range "an immediate" (C.target_int_of_z machine_width) in
  let immediates imms =
    Target_ocaml_int.Set.of_list (List.map immediate imms)
  in
  let scrutinee name = Simple.name (C.name_of_model numbering name) in
  let variable = C.variable_of_model numbering in
  let function_slot = C.function_slot_of_model numbering in
  let numbers what of_z of_list numbers =
    of_list (List.map (C.in_range what of_z) numbers)
  in
  let no_function_for_vectors () =
    raise
      (No_such_function
         "the compiler has no such function for the vectors and the masks")
  in
  let create_blocks { tag; shape; fields; block_alloc_mode } open_or_closed =
    TG.Row_like_for_blocks.create ~machine_width
      ~shape:(C.block_shape_of_model shape)
      ~field_tys:(List.map ty fields)
      (open_or_closed (C.tag_of_model machine_width tag))
      (C.alloc_mode_of_model block_alloc_mode)
  in
  let closure_arguments
      { this_function_slot;
        function_types;
        closure_types;
        value_slot_types;
        closure_alloc_mode
      } =
    let function_slot = C.function_slot_of_model numbering in
    let slot_map of_model bindings =
      C.map_of_model ~empty:Function_slot.Map.empty ~mem:Function_slot.Map.mem
        ~add:Function_slot.Map.add function_slot of_model bindings
    in
    ( function_slot this_function_slot,
      slot_map
        (C.or_unknown_of_model
           (fun ({ function_type_code_id = code_id } : MT.function_type) ->
             TG.Function_type.create
               (C.code_id_of_model numbering code_id)
               ~rec_info:TG.any_rec_info))
        function_types,
      slot_map ty closure_types,
      C.map_of_model ~empty:Value_slot.Map.empty ~mem:Value_slot.Map.mem
        ~add:Value_slot.Map.add
        (C.value_slot_of_model numbering)
        ty value_slot_types,
      C.alloc_mode_of_model closure_alloc_mode )
  in
  match call with
  | Unknown kind -> MTC.unknown (C.kind_of_model kind)
  | Bottom kind -> MTC.bottom (C.kind_of_model kind)
  | Alias_type_of (kind, simple) ->
    TG.alias_type_of (C.kind_of_model kind)
      (C.simple_of_model numbering machine_width simple)
  | Type_for_const const ->
    MTC.type_for_const (C.const_of_model machine_width const)
  | Null -> TG.null
  | Any_non_null_value -> TG.any_non_null_value
  | This_tagged_immediate i -> TG.this_tagged_immediate (immediate i)
  | This_naked_immediate i -> TG.this_naked_immediate (immediate i)
  | These_naked_immediates imms -> TG.these_naked_immediates (immediates imms)
  | These_tagged_immediates imms ->
    MTC.these_tagged_immediates (immediates imms)
  | Any_tagged_immediate -> MTC.any_tagged_immediate
  | Any_block -> MTC.any_block
  | Tag_immediate t -> TG.tag_immediate (ty t)
  | Box_number (number, contents, alloc_mode) -> (
    let contents = ty contents in
    let alloc_mode = C.alloc_mode_of_model alloc_mode in
    match number with
    | Boxable_naked_float32 -> TG.box_float32 contents alloc_mode
    | Boxable_naked_float -> TG.box_float contents alloc_mode
    | Boxable_naked_int32 -> TG.box_int32 contents alloc_mode
    | Boxable_naked_int64 -> TG.box_int64 contents alloc_mode
    | Boxable_naked_nativeint -> TG.box_nativeint contents alloc_mode
    | Boxable_naked_vec128 -> TG.box_vec128 contents alloc_mode
    | Boxable_naked_vec256 -> TG.box_vec256 contents alloc_mode
    | Boxable_naked_vec512 -> TG.box_vec512 contents alloc_mode
    | Boxable_naked_mask -> TG.box_mask contents alloc_mode)
  | Mutable_block alloc_mode ->
    TG.mutable_block (C.alloc_mode_of_model alloc_mode)
  | This_immutable_string bytes ->
    TG.this_immutable_string
      (String.of_seq
         (Seq.map
            (fun byte ->
              Char.chr (C.in_range "a byte" (fun z -> N.int_of_z z) byte))
            (List.to_seq bytes)))
  | Create_variant (is_unique, immediates, blocks, extensions) ->
    TG.create_variant ~is_unique
      ~immediates:(C.or_unknown_of_model ty immediates)
      ~blocks:
        (C.or_unknown_of_model
           (C.row_like_for_blocks_of_model numbering machine_width)
           blocks)
      ~extensions:
        (C.variant_extensions_of_model numbering machine_width extensions)
  | Create_closures (alloc_mode, closures) ->
    TG.create_closures
      (C.alloc_mode_of_model alloc_mode)
      (C.row_like_for_closures_of_model numbering machine_width closures)
  | Blocks_with_these_tags (tags, alloc_mode) -> (
    match
      MTC.blocks_with_these_tags ~machine_width
        (Tag.Set.of_list (List.map (C.tag_of_model machine_width) tags))
        (C.alloc_mode_of_model alloc_mode)
    with
    | Known t -> t
    | Unknown ->
      raise (No_such_function "the compiler has no answer for these tags"))
  | Immutable_block (is_unique, { tag; shape; fields; block_alloc_mode }) ->
    MTC.immutable_block ~machine_width ~is_unique
      (C.tag_of_model machine_width tag)
      ~shape:(C.block_shape_of_model shape)
      (C.alloc_mode_of_model block_alloc_mode)
      ~fields:(List.map ty fields)
  | Row_like_create_exactly block ->
    blocks_as_type_of_compiler (create_blocks block (fun tag -> Closed tag))
  | Row_like_create_at_least block ->
    blocks_as_type_of_compiler
      (create_blocks block (fun tag -> Open (Known tag)))
  | Row_like_create_at_least_unknown_tag block ->
    blocks_as_type_of_compiler (create_blocks block (fun _ -> Open Unknown))
  | Is_int_for_scrutinee name ->
    TG.is_int_for_scrutinee ~machine_width ~scrutinee:(scrutinee name)
  | Get_tag_for_block name -> TG.get_tag_for_block ~block:(scrutinee name)
  | Is_null_for_scrutinee name ->
    TG.is_null ~machine_width ~scrutinee:(scrutinee name)
  | Exactly_this_closure arguments ->
    let ( this_function_slot,
          all_function_slots_in_set,
          all_closure_types_in_set,
          all_value_slots_in_set,
          alloc_mode ) =
      closure_arguments arguments
    in
    MTC.exactly_this_closure this_function_slot ~all_function_slots_in_set
      ~all_closure_types_in_set ~all_value_slots_in_set alloc_mode
  | At_least_this_closure arguments ->
    let ( this_function_slot,
          at_least_these_function_slots,
          at_least_these_closure_types,
          at_least_these_value_slots,
          alloc_mode ) =
      closure_arguments arguments
    in
    MTC.at_least_this_closure this_function_slot ~at_least_these_function_slots
      ~at_least_these_closure_types ~at_least_these_value_slots alloc_mode
  | Unknown_like t -> MTC.unknown_like (ty t)
  | Bottom_like t -> MTC.bottom_like (ty t)
  | Unknown_from_shape (shape, index) ->
    MTC.unknown_from_shape (C.block_shape_of_model shape) index
  | Unknown_with_subkind kind ->
    MTC.unknown_with_subkind ~machine_width
      (K.With_subkind.anything (C.kind_of_model kind))
  | Kind_for_const const ->
    MTC.unknown (MTC.kind_for_const (C.const_of_model machine_width const))
  | These_naked_numbers (kind, ns) -> (
    match kind with
    | Kind_naked_immediate -> TG.these_naked_immediates (immediates ns)
    | Kind_naked_float32 ->
      TG.these_naked_float32s
        (numbers "the bits of a float32" C.float32_of_z
           Numeric_types.Float32_by_bit_pattern.Set.of_list ns)
    | Kind_naked_float ->
      TG.these_naked_floats
        (numbers "the bits of a float" C.float_of_z
           Numeric_types.Float_by_bit_pattern.Set.of_list ns)
    | Kind_naked_int8 ->
      TG.these_naked_int8s
        (numbers "an int8" C.int8_of_z Numeric_types.Int8.Set.of_list ns)
    | Kind_naked_int16 ->
      TG.these_naked_int16s
        (numbers "an int16" C.int16_of_z Numeric_types.Int16.Set.of_list ns)
    | Kind_naked_int32 ->
      TG.these_naked_int32s
        (numbers "an int32" C.int32_of_z Numeric_types.Int32.Set.of_list ns)
    | Kind_naked_int64 ->
      TG.these_naked_int64s
        (numbers "an int64" C.int64_of_z Numeric_types.Int64.Set.of_list ns)
    | Kind_naked_nativeint ->
      TG.these_naked_nativeints
        (numbers "a nativeint"
           (C.nativeint_of_z machine_width)
           Targetint_32_64.Set.of_list ns)
    | Kind_naked_vec128 ->
      TG.these_naked_vec128s
        (numbers "the bits of a vec128" C.vec128_of_z
           Vector_types.Vec128.Bit_pattern.Set.of_list ns)
    | Kind_naked_vec256 ->
      TG.these_naked_vec256s
        (numbers "the bits of a vec256" C.vec256_of_z
           Vector_types.Vec256.Bit_pattern.Set.of_list ns)
    | Kind_naked_vec512 ->
      TG.these_naked_vec512s
        (numbers "the bits of a vec512" C.vec512_of_z
           Vector_types.Vec512.Bit_pattern.Set.of_list ns)
    | Kind_naked_mask ->
      TG.these_naked_masks
        (numbers "the bits of a mask" C.mask_of_z
           Vector_types.Mask.Bit_pattern.Set.of_list ns))
  | Any_tagged_bool -> MTC.any_tagged_bool ~machine_width
  | Any_naked_bool -> MTC.any_naked_bool ~machine_width
  | Any_tagged_immediate_or_null -> MTC.any_tagged_immediate_or_null
  | Tagged_immediate_alias_to x ->
    TG.tagged_immediate_alias_to ~naked_immediate:(variable x)
  | Boxed_number_alias_to (number, x, alloc_mode) -> (
    let x = variable x in
    let alloc_mode = C.alloc_mode_of_model alloc_mode in
    match number with
    | Boxable_naked_float32 ->
      TG.boxed_float32_alias_to ~naked_float32:x alloc_mode
    | Boxable_naked_float -> TG.boxed_float_alias_to ~naked_float:x alloc_mode
    | Boxable_naked_int32 -> TG.boxed_int32_alias_to ~naked_int32:x alloc_mode
    | Boxable_naked_int64 -> TG.boxed_int64_alias_to ~naked_int64:x alloc_mode
    | Boxable_naked_nativeint ->
      TG.boxed_nativeint_alias_to ~naked_nativeint:x alloc_mode
    | Boxable_naked_vec128 ->
      TG.boxed_vec128_alias_to ~naked_vec128:x alloc_mode
    | Boxable_naked_vec256 ->
      TG.boxed_vec256_alias_to ~naked_vec256:x alloc_mode
    | Boxable_naked_vec512 ->
      TG.boxed_vec512_alias_to ~naked_vec512:x alloc_mode
    | Boxable_naked_mask -> TG.boxed_mask_alias_to ~naked_mask:x alloc_mode)
  | This_boxed_number (number, i, alloc_mode) -> (
    let alloc_mode = C.alloc_mode_of_model alloc_mode in
    match number with
    | Boxable_naked_float32 ->
      MTC.this_boxed_float32
        (C.in_range "the bits of a float32" C.float32_of_z i)
        alloc_mode
    | Boxable_naked_float ->
      MTC.this_boxed_float
        (C.in_range "the bits of a float" C.float_of_z i)
        alloc_mode
    | Boxable_naked_int32 ->
      MTC.this_boxed_int32 (C.in_range "an int32" C.int32_of_z i) alloc_mode
    | Boxable_naked_int64 ->
      MTC.this_boxed_int64 (C.in_range "an int64" C.int64_of_z i) alloc_mode
    | Boxable_naked_nativeint ->
      MTC.this_boxed_nativeint
        (C.in_range "a nativeint" (C.nativeint_of_z machine_width) i)
        alloc_mode
    | Boxable_naked_vec128 ->
      MTC.this_boxed_vec128
        (C.in_range "the bits of a vec128" C.vec128_of_z i)
        alloc_mode
    | Boxable_naked_vec256 ->
      MTC.this_boxed_vec256
        (C.in_range "the bits of a vec256" C.vec256_of_z i)
        alloc_mode
    | Boxable_naked_vec512 ->
      MTC.this_boxed_vec512
        (C.in_range "the bits of a vec512" C.vec512_of_z i)
        alloc_mode
    | Boxable_naked_mask ->
      MTC.this_boxed_mask
        (C.in_range "the bits of a mask" C.mask_of_z i)
        alloc_mode)
  | These_boxed_numbers (number, ns, alloc_mode) -> (
    let alloc_mode = C.alloc_mode_of_model alloc_mode in
    match number with
    | Boxable_naked_float32 ->
      MTC.these_boxed_float32s
        (numbers "the bits of a float32" C.float32_of_z
           Numeric_types.Float32_by_bit_pattern.Set.of_list ns)
        alloc_mode
    | Boxable_naked_float ->
      MTC.these_boxed_floats
        (numbers "the bits of a float" C.float_of_z
           Numeric_types.Float_by_bit_pattern.Set.of_list ns)
        alloc_mode
    | Boxable_naked_int32 ->
      MTC.these_boxed_int32s
        (numbers "an int32" C.int32_of_z Numeric_types.Int32.Set.of_list ns)
        alloc_mode
    | Boxable_naked_int64 ->
      MTC.these_boxed_int64s
        (numbers "an int64" C.int64_of_z Numeric_types.Int64.Set.of_list ns)
        alloc_mode
    | Boxable_naked_nativeint ->
      MTC.these_boxed_nativeints
        (numbers "a nativeint"
           (C.nativeint_of_z machine_width)
           Targetint_32_64.Set.of_list ns)
        alloc_mode
    | Boxable_naked_vec128 | Boxable_naked_vec256 | Boxable_naked_vec512
    | Boxable_naked_mask ->
      no_function_for_vectors ())
  | Any_boxed_number number -> (
    match number with
    | Boxable_naked_float32 -> MTC.any_boxed_float32
    | Boxable_naked_float -> MTC.any_boxed_float
    | Boxable_naked_int32 -> MTC.any_boxed_int32
    | Boxable_naked_int64 -> MTC.any_boxed_int64
    | Boxable_naked_nativeint -> MTC.any_boxed_nativeint
    | Boxable_naked_vec128 | Boxable_naked_vec256 | Boxable_naked_vec512
    | Boxable_naked_mask ->
      no_function_for_vectors ())
  | Row_like_create (block, open_or_closed) ->
    let tag = C.tag_of_model machine_width in
    blocks_as_type_of_compiler
      (create_blocks block (fun (_ : Tag.t) ->
           match open_or_closed with
           | Open (Known t) -> Open (Known (tag t))
           | Open Unknown -> Open Unknown
           | Closed t -> Closed (tag t)))
  | Immutable_block_with_size_at_least (tag, n, shape, x) ->
    MTC.immutable_block_with_size_at_least ~machine_width
      ~tag:(C.or_unknown_of_model (C.tag_of_model machine_width) tag)
      ~n:(Target_ocaml_int.of_int machine_width n)
      ~shape:(C.block_shape_of_model shape)
      ~field_n_minus_one:(variable x)
  | Closure_with_at_least_these_function_slots (this_function_slot, bindings) ->
    MTC.closure_with_at_least_these_function_slots
      ~this_function_slot:(function_slot this_function_slot)
      (C.map_of_model ~empty:Function_slot.Map.empty ~mem:Function_slot.Map.mem
         ~add:Function_slot.Map.add function_slot
         (C.simple_of_model numbering machine_width)
         bindings)
  | Static_closure_with_this_code (this_function_slot, symbol, code) ->
    MTC.static_closure_with_this_code
      ~this_function_slot:(function_slot this_function_slot)
      ~closure_symbol:(Option.map (C.symbol_of_model numbering) symbol)
      ~code_id:(C.code_id_of_model numbering code)
  | Closure_with_at_least_these_value_slots (this_function_slot, value_slots) ->
    MTC.closure_with_at_least_these_value_slots
      ~this_function_slot:(function_slot this_function_slot)
      (C.map_of_model ~empty:Value_slot.Map.empty ~mem:Value_slot.Map.mem
         ~add:Value_slot.Map.add
         (C.value_slot_of_model numbering)
         (fun (x, kind) -> variable x, C.kind_of_model kind)
         value_slots)
  | Closure_with_at_least_this_value_slot
      (this_function_slot, value_slot, x, kind) ->
    MTC.closure_with_at_least_this_value_slot
      ~this_function_slot:(function_slot this_function_slot)
      (C.value_slot_of_model numbering value_slot)
      ~value_slot_var:(variable x) ~value_slot_kind:(C.kind_of_model kind)

(* A call within what the compiler's function asks of its arguments: the kinds
   that it checks, a tag that the shape permits, fields of the kinds of the
   shape, sets given without repeats, maps without shadowed bindings. *)
let generate_call (names : names) r : call =
  let pool = names.pool in
  let config : G.config = { well_formed = true; depth = 2 } in
  let ty kind = G.type_of_kind config r pool kind in
  let alloc_mode () = G.alloc_mode config r in
  let numbers () =
    Model_type.set N.compare_z (G.list r ~max:4 (fun () -> G.small_number r))
  in
  let block () : block =
    let shape = G.block_shape r in
    let tag =
      match shape with
      | Scannable (Value_only | Mixed_record _) ->
        N.z_of_int (G.pick r [0; 1; 2; 250])
      | Float_record -> MT.double_array_tag
    in
    let size =
      match shape with
      | Scannable (Mixed_record (value_prefix_size, flat_suffix)) ->
        N.int_of_nat value_prefix_size + List.length flat_suffix
      | Scannable Value_only | Float_record -> G.below r 4
    in
    { tag;
      shape;
      fields = List.map ty (MT.field_kinds shape (N.nat_of_int size));
      block_alloc_mode = alloc_mode ()
    }
  in
  (* [Row_like_for_blocks.create] gives a block of floats its one tag, known or
     not: no exported function of the compiler makes a structure of float blocks
     of an unknown tag, so that case of the model's function is compared with
     nothing. *)
  let rec scannable_block () =
    let block = block () in
    match block.shape with
    | Scannable (Value_only | Mixed_record _) -> block
    | Float_record -> scannable_block ()
  in
  let distinct_keys bindings =
    Model_type.map N.compare_positive Fun.id bindings
  in
  let slots_and_types () : slots_and_types =
    { this_function_slot = G.pick r pool.function_slots;
      function_types =
        distinct_keys
          (G.list r ~max:2 (fun () ->
               ( G.pick r pool.function_slots,
                 if G.chance r ~percent:25
                 then MT.Or_unknown.Unknown
                 else
                   MT.Or_unknown.Known
                     { MT.function_type_code_id = G.pick r pool.code_ids } )));
      closure_types =
        distinct_keys
          (G.list r ~max:2 (fun () ->
               let slot = G.pick r pool.function_slots in
               slot, ty MK.Value));
      value_slot_types =
        distinct_keys
          (G.list r ~max:2 (fun () -> G.pick r pool.value_slots, ty MK.Value));
      closure_alloc_mode = alloc_mode ()
    }
  in
  let kind () = G.kind r in
  let name () = G.name config r pool in
  let naked_immediate = MK.Naked_number Kind_naked_immediate in
  (* A variable of the pool, of whatever kind: the functions that are given one
     do not look at its kind. *)
  let variable () =
    G.pick r
      (pool.value_variables @ pool.naked_immediate_variables
     @ pool.naked_float_variables)
  in
  let boxable_number () = G.pick r G.all_boxable_numbers in
  let naked_number_kind () = G.pick r G.all_naked_number_kinds in
  (* A tag that a block of values may have, one that it may not, and the tag of
     the blocks of floats. *)
  let any_tag () = N.z_of_int (G.pick r [0; 1; 2; 250; 251; 254]) in
  let open_or_closed () : MT.Open_or_closed.t =
    match G.below r 3 with
    | 0 -> Closed (any_tag ())
    | 1 -> Open (Known (any_tag ()))
    | _ -> Open Unknown
  in
  let generators : (unit -> call) list =
    [ (fun () -> Unknown (kind ()));
      (fun () -> Bottom (kind ()));
      (fun () ->
        let kind = kind () in
        match G.simple config r pool kind with
        | Some simple -> Alias_type_of (kind, simple)
        | None -> Unknown kind);
      (fun () ->
        let kind = kind () in
        match G.const_of_kind config r kind with
        | Some const -> Type_for_const const
        | None -> Type_for_const (Poison kind));
      (fun () -> Null);
      (fun () -> Any_non_null_value);
      (fun () -> This_tagged_immediate (G.small_number r));
      (fun () -> This_naked_immediate (G.small_number r));
      (fun () -> These_naked_immediates (numbers ()));
      (fun () -> These_tagged_immediates (numbers ()));
      (fun () -> Any_tagged_immediate);
      (fun () -> Any_block);
      (fun () -> Tag_immediate (ty naked_immediate));
      (fun () ->
        let number = G.pick r G.all_boxable_numbers in
        Box_number (number, ty (MK.unboxed_kind number), alloc_mode ()));
      (fun () -> Mutable_block (alloc_mode ()));
      (fun () ->
        This_immutable_string
          (G.list r ~max:4 (fun () -> N.z_of_int (G.below r 256))));
      (fun () ->
        Create_variant
          ( G.chance r ~percent:20,
            (if G.chance r ~percent:30
             then MT.Or_unknown.Unknown
             else MT.Or_unknown.Known (ty naked_immediate)),
            (if G.chance r ~percent:30
             then MT.Or_unknown.Unknown
             else MT.Or_unknown.Known (G.row_like_for_blocks config r pool)),
            if G.chance r ~percent:70
            then MT.No_extensions
            else
              MT.Ext
                (G.env_extension config r pool, G.env_extension config r pool)
          ));
      (fun () ->
        Create_closures (alloc_mode (), G.row_like_for_closures config r pool));
      (fun () ->
        Blocks_with_these_tags
          ( Model_type.set N.compare_z
              (G.list r ~max:3 (fun () ->
                   let tag = G.pick r [0; 1; 2; 250] in
                   N.z_of_int tag)),
            alloc_mode () ));
      (fun () -> Immutable_block (G.chance r ~percent:20, block ()));
      (fun () -> Row_like_create_exactly (block ()));
      (fun () -> Row_like_create_at_least (block ()));
      (fun () -> Row_like_create_at_least_unknown_tag (scannable_block ()));
      (fun () -> Is_int_for_scrutinee (name ()));
      (fun () -> Get_tag_for_block (name ()));
      (fun () -> Is_null_for_scrutinee (name ()));
      (fun () -> Exactly_this_closure (slots_and_types ()));
      (fun () -> At_least_this_closure (slots_and_types ()));
      (fun () -> Unknown_like (ty (kind ())));
      (fun () -> Bottom_like (ty (kind ())));
      (* An index that the shape has, or one past its fields. *)
      (fun () -> Unknown_from_shape (G.block_shape r, G.below r 5));
      (fun () -> Unknown_with_subkind (kind ()));
      (fun () ->
        let kind = kind () in
        match G.const_of_kind config r kind with
        | Some const -> Kind_for_const const
        | None -> Kind_for_const (Poison kind));
      (fun () -> These_naked_numbers (naked_number_kind (), numbers ()));
      (fun () -> Any_tagged_bool);
      (fun () -> Any_naked_bool);
      (fun () -> Any_tagged_immediate_or_null);
      (fun () -> Tagged_immediate_alias_to (variable ()));
      (fun () ->
        Boxed_number_alias_to (boxable_number (), variable (), alloc_mode ()));
      (fun () ->
        This_boxed_number (boxable_number (), G.small_number r, alloc_mode ()));
      (fun () ->
        These_boxed_numbers (boxable_number (), numbers (), alloc_mode ()));
      (fun () -> Any_boxed_number (boxable_number ()));
      (fun () -> Row_like_create (block (), open_or_closed ()));
      (fun () ->
        Immutable_block_with_size_at_least
          ( (if G.chance r ~percent:30
             then MT.Or_unknown.Unknown
             else MT.Or_unknown.Known (any_tag ())),
            G.below r 5,
            G.block_shape r,
            variable () ));
      (fun () ->
        Closure_with_at_least_these_function_slots
          ( G.pick r pool.function_slots,
            distinct_keys
              (G.list r ~max:2 (fun () ->
                   ( G.pick r pool.function_slots,
                     match G.simple config r pool MK.Value with
                     | Some simple -> simple
                     | None -> M.Var (variable ()) ))) ));
      (fun () ->
        Static_closure_with_this_code
          ( G.pick r pool.function_slots,
            (if G.chance r ~percent:50
             then Some (G.pick r pool.symbols)
             else None),
            G.pick r pool.code_ids ));
      (fun () ->
        Closure_with_at_least_these_value_slots
          ( G.pick r pool.function_slots,
            distinct_keys
              (G.list r ~max:2 (fun () ->
                   G.pick r pool.value_slots, (variable (), kind ()))) ));
      (fun () ->
        Closure_with_at_least_this_value_slot
          ( G.pick r pool.function_slots,
            G.pick r pool.value_slots,
            variable (),
            kind () )) ]
  in
  (G.pick r generators) ()

(* A call is shown by the type that the model makes of it. *)
let model_on_call (call : call) : MT.flambda_type option =
  match call_in_the_model call with
  | of_model -> Some of_model
  | exception No_answer -> None

let print_call ppf (call : call) =
  match model_on_call call with
  | Some of_model ->
    Format.fprintf ppf "@[<v>a call of %s, which in the model gives@ %a@]"
      (name_of_call call) Model_type.print of_model
  | None ->
    Format.fprintf ppf "a call of %s, which in the model has no answer"
      (name_of_call call)

(* What the compiler's function does on a call: a type, as the model has it, or
   it stops (a fatal error, or the exception of an index outside an array). *)
let compiler_on_call (names : names) (call : call) :
    (MT.flambda_type, string) result =
  match
    or_fatal_error (fun () ->
        match call_in_the_compiler names call with
        | of_compiler -> Ok (to_model names of_compiler)
        | exception Invalid_argument what -> Error ("an exception: " ^ what))
  with
  | Ok result -> result
  | Error line -> Error ("a fatal error: " ^ line)

let creation_functions (names : names) : call comparison list =
  List.map
    (fun name ->
      { name;
        compare =
          (fun call ->
            if not (String.equal (name_of_call call) name)
            then Not_this_comparison
            else
              match compiler_on_call names call, model_on_call call with
              | exception No_such_function why -> Not_run why
              | Ok of_compiler, Some of_model ->
                agree_if
                  (Model_type.same of_model of_compiler)
                  (Format.asprintf "the compiler gives %a" Model_type.print
                     of_compiler)
              | Ok of_compiler, None ->
                Disagree
                  (Format.asprintf
                     "the model has no answer and the compiler gives %a"
                     Model_type.print of_compiler)
              | Error _, None -> Agree
              | Error why, Some (_ : MT.flambda_type) ->
                Disagree ("the compiler stops: " ^ why))
      })
    names_of_calls
  @ [ { name = "a creation function that is not in the list above";
        compare =
          (fun call ->
            if List.mem (name_of_call call) names_of_calls
            then Not_this_comparison
            else Disagree "it is compared with nothing")
      };
      (* These calls are counted above with those that agree. *)
      { name = "the calls on which the model has no answer: the compiler stops";
        compare =
          (fun call ->
            match model_on_call call with
            | Some (_ : MT.flambda_type) -> Not_this_comparison
            | None -> (
              match compiler_on_call names call with
              | exception No_such_function why -> Not_run why
              | Error (_ : string) -> Agree
              | Ok of_compiler ->
                Disagree
                  (Format.asprintf "the compiler gives %a" Model_type.print
                     of_compiler)))
      };
      { name =
          "type_well_formed of what a creation function gives, in the model \
           and in the compiler";
        compare =
          (fun call ->
            match compiler_on_call names call, model_on_call call with
            | exception No_such_function why -> Not_run why
            | (Error _ | Ok _), None -> Not_run "the model has no answer"
            | Error why, Some (_ : MT.flambda_type) ->
              Not_run ("the compiler stops: " ^ why)
            | Ok of_compiler, Some of_model ->
              (* The lists given to a call may bind a key twice. *)
              let of_model = is_well_formed (Model_type.normalise of_model) in
              let of_compiler = is_well_formed of_compiler in
              agree_if
                (Bool.equal of_model of_compiler)
                (Printf.sprintf
                   "it is %b of what the model gives and %b of what the \
                    compiler gives"
                   of_model of_compiler))
      };
      { name = "the calls that give a type of which type_well_formed is true";
        compare =
          (fun call ->
            match model_on_call call with
            | None -> Not_run "the model has no answer"
            | Some of_model ->
              if is_well_formed (Model_type.normalise of_model)
              then Agree
              else Not_run "it is false of the type")
      } ]

(* ======================================================================== *)
(* A relation on a constant, and the bottom test of a row-like structure    *)
(* ======================================================================== *)

(* [Relation.of_const]: each relation on a constant of each kind. *)
let relation_of_const (names : names) :
    (MT.Relation.t * M.const) comparison list =
  ignore (names : names);
  let print ppf (x : N.z MT.Or_bottom.t) =
    match x with
    | Ok n -> N.print_z ppf n
    | Bottom -> Format.pp_print_string ppf "Bottom"
  in
  [ { name = "Relation.of_const";
      compare =
        (fun (relation, const) ->
          let of_model = MT.Relation.of_const relation const in
          let of_compiler =
            Converter.or_bottom_to_model Converter.z_of_target_int
              (TG.Relation.of_const ~machine_width
                 (Converter.relation_of_model relation)
                 (Converter.const_of_model machine_width const))
          in
          agree_if
            (Stdlib.( = ) of_model of_compiler)
            (Format.asprintf "the model answers %a, the compiler %a" print
               of_model print of_compiler))
    } ]

(* [Row_like_for_blocks.is_bottom], on raw structures. *)
let row_like_bottom (names : names) : MT.row_like_for_blocks comparison list =
  [ { name = "Row_like_for_blocks.is_bottom";
      compare =
        (fun blocks ->
          let of_model = MT.row_like_for_blocks_is_bottom blocks in
          let of_compiler =
            TG.Row_like_for_blocks.is_bottom
              (Converter.row_like_for_blocks_of_model names.numbering
                 machine_width blocks)
          in
          agree_if
            (Bool.equal of_model of_compiler)
            (Printf.sprintf "the model answers %b, the compiler %b" of_model
               of_compiler))
    } ]

(* ======================================================================== *)
(* The two implementations of meet and join                                 *)
(* ======================================================================== *)

(* The compiler has two: [Meet_and_join], with [Join_levels_old], which is the
   one it runs unless told otherwise, and [Meet_and_n_way_join], with
   [Join_env], which it runs for the n-way join algorithm
   ([Flambda_features.join_algorithm], from the flag [-flambda2-join-algorithm]
   of driver/oxcaml_flags.ml; [Meet.meet] and [Join_levels.cut_and_n_way_join]
   choose by it). Here each is called by its own module, so both run in one
   process whatever the flag.

   Until the model has a meet and a join, the two are compared with each other:
   on the same two types, the same answer, as types of the model. *)

type implementation =
  { implementation : string;
    meet : TE.t -> TG.t -> TG.t -> (TG.t * TE.t) Or_bottom.t;
    (* The environment at a continuation with one parameter, from the
       environments at its uses: the definition environment, the environments at
       the uses, the parameter, and the scope to cut after. *)
    join :
      TE.t ->
      TE.t list ->
      params:Bound_parameters.t ->
      cut_after:Scope.t ->
      TE.t;
    meet_expanded_head : ME.meet_expanded_head
  }

let binary : implementation =
  { implementation = "binary";
    meet = Binary.meet;
    join =
      (fun env use_envs ~params ~cut_after ->
        Binary_join.cut_and_n_way_join env
          (List.map
             (fun use_env ->
               ( use_env,
                 Apply_cont_rewrite_id.create (),
                 Continuation_use_kind.Inlinable ))
             use_envs)
          ~params ~cut_after ~extra_lifted_consts_in_use_envs:Symbol.Set.empty
          ~extra_allowed_names:Name_occurrences.empty);
    meet_expanded_head = Binary.meet_expanded_head
  }

let n_way : implementation =
  { implementation = "n-way";
    meet = N_way.meet;
    join =
      (fun env use_envs ~params:_ ~cut_after ->
        fst
          (N_way_join.cut_and_n_way_join_with_analysis
             ~meet_expanded_head:N_way.meet_expanded_head
             ~n_way_join_type:N_way.n_way_join env ~cut_after
             (List.map (fun use_env -> (), use_env) use_envs)));
    meet_expanded_head = N_way.meet_expanded_head
  }

(* What an environment knows of the names of the tests, as types of the
   model. *)
let types_of_names (names : names) (env : TE.t) : MT.flambda_type list =
  List.map
    (fun (name, kind) -> to_model names (TE.find env name (Some kind)))
    names.defined

let print_types ppf types = Model_type.print_list Model_type.print ppf types

(* The meet of two types, and what it teaches of the names. *)
let meet_as_model (names : names) (implementation : implementation) t1 t2 :
    (MT.flambda_type * MT.flambda_type list) option =
  match implementation.meet names.env t1 t2 with
  | Bottom -> None
  | Ok (t, env) -> Some (to_model names t, types_of_names names env)

(* What a join gives: the type of the parameter, and the variables that the join
   made of its own (those that are not of the tests) that this type mentions, or
   the type of one of them, each with what the joined environment says of it.
   Where other types are read from the joined environment besides, the variables
   that they mention are among these too ([reached_from] below). *)
type joined =
  { joined : MT.flambda_type;
    own : (M.variable * MT.flambda_type) list;
    (* Those of [own] that the joined environment lets terms mention (their name
       mode is normal); the others are for types only. *)
    own_in_terms : M.variable list
  }

let is_own (names : names) (x : M.variable) =
  match N.int_of_positive x with
  | Some number -> number > names.variables_of_the_tests
  | None -> true

(* The variables of a type that are not of the tests, once each, in the order in
   which the type as written in one way mentions them. *)
let own_variables_of (names : names) (t : MT.flambda_type) : M.variable list =
  List.fold_left
    (fun found x ->
      if is_own names x && not (List.mem x found) then found @ [x] else found)
    []
    (MT.free_variables (Model_type.normalise t))

let joined_of_env ?(reached_from = []) (names : names) (env : TE.t)
    (parameter : Variable.t) : joined =
  let type_of variable =
    to_model names
      (TE.find env (Name.var variable) (Some (Variable.kind variable)))
  in
  let joined = type_of parameter in
  let rec close own (pending : M.variable list) =
    match pending with
    | [] -> List.rev own
    | x :: pending ->
      if List.mem_assoc x own
      then close own pending
      else
        let variable = Converter.variable_of_model names.numbering x in
        if not (TE.mem env (Name.var variable))
        then
          raise (Not_defined (Format.asprintf "%a" Model_type.print_variable x))
        else
          let t = type_of variable in
          close ((x, t) :: own) (pending @ own_variables_of names t)
  in
  let own =
    close [] (List.concat_map (own_variables_of names) (joined :: reached_from))
  in
  let own_in_terms =
    List.filter
      (fun x ->
        TE.mem ~min_name_mode:Name_mode.normal env
          (Name.var (Converter.variable_of_model names.numbering x)))
      (List.map fst own)
  in
  { joined; own; own_in_terms }

(* The join at a continuation with one parameter of a kind, which is applied to
   a value of each of the types given, one at each use: the joined environment
   and the parameter. For the use of a position in the list, [known] gives what
   that use knows of the names of the tests besides, and [locals] the variables
   that only that use binds, with their types. [in_types] are variables that the
   environment of the continuation's definition defines for types only.
   [observe] is given the environments of the uses before they are joined. *)
let join_env (names : names) (implementation : implementation)
    ?(known = fun (_ : int) -> []) ?(locals = fun (_ : int) -> [])
    ?(in_types = []) ?(observe = fun (_ : TE.t list) -> ())
    (kind : MK.flambda_kind) (types : TG.t list) : TE.t * Variable.t =
  let variable = parameter names kind in
  let compiler_kind = Converter.kind_of_model kind in
  let meet_expanded_head = implementation.meet_expanded_head in
  let define mode env variable =
    TE.add_definition env
      (Bound_name.create_var
         (Bound_var.create variable Flambda_debug_uid.none mode))
      (Variable.kind variable)
  in
  let env =
    List.fold_left
      (define Name_mode.in_types)
      (define Name_mode.normal names.env variable)
      in_types
  in
  let use_envs =
    List.mapi
      (fun i t ->
        let locals = locals i in
        let env =
          List.fold_left
            (fun env (local, _) -> define Name_mode.normal env local)
            (TE.increment_scope env) locals
        in
        ME.use_meet_env ~meet_expanded_head env ~f:(fun env ->
            List.fold_left
              (fun env (name, t) ->
                ME.add_equation env name t ~meet_expanded_head)
              env
              (known i
              @ List.map (fun (local, t) -> Name.var local, t) locals
              @ [Name.var variable, t])))
      types
  in
  observe use_envs;
  let joined =
    implementation.join env use_envs
      ~params:
        (Bound_parameters.create
           [ Bound_parameter.create variable
               (K.With_subkind.anything compiler_kind)
               Flambda_debug_uid.none ])
      ~cut_after:(TE.current_scope env)
  in
  joined, variable

let join (names : names) (implementation : implementation) ?known ?locals
    (kind : MK.flambda_kind) (types : TG.t list) : joined =
  let env, parameter =
    join_env names implementation ?known ?locals kind types
  in
  joined_of_env names env parameter

(* What is printed, with the variables that are not those of the tests named
   [e0], [e1], ... in the order they come. *)
let rename_own_variables (names : names) (printed : string) : string =
  let own = Hashtbl.create 4 in
  let buffer = Buffer.create (String.length printed) in
  let is_digit c = c >= '0' && c <= '9' in
  let length = String.length printed in
  let rec copy i =
    if i < length
    then
      if
        Char.equal printed.[i] 'v'
        && i + 1 < length
        && is_digit printed.[i + 1]
        && (i = 0 || not (is_digit printed.[i - 1]))
      then (
        let rec end_of_number j =
          if j < length && is_digit printed.[j]
          then end_of_number (j + 1)
          else j
        in
        let j = end_of_number (i + 1) in
        let number = int_of_string (String.sub printed (i + 1) (j - i - 1)) in
        if number <= names.variables_with_a_name
        then Buffer.add_string buffer (String.sub printed i (j - i))
        else (
          if not (Hashtbl.mem own number)
          then Hashtbl.add own number (Hashtbl.length own);
          Buffer.add_string buffer
            (Printf.sprintf "e%d" (Hashtbl.find own number)));
        copy j)
      else (
        Buffer.add_char buffer printed.[i];
        copy (i + 1))
  in
  copy 0;
  Buffer.contents buffer

(* Whether two texts are the same but for how they are laid out. The lines of a
   text are broken before its variables are renamed, so where they are broken
   depends on how long the numbers of the variables were: two texts that differ
   only there are one answer. Nothing else is forgiven: the printer brackets
   every part of a type, so the words of a text in their order say what the type
   is. *)
let same_text (text : string) (text' : string) : bool =
  let words text =
    List.filter
      (fun word -> not (String.equal word ""))
      (String.split_on_char ' '
         (String.map (fun c -> if Char.equal c '\n' then ' ' else c) text))
  in
  List.equal String.equal (words text) (words text')

(* Types as printed, each written in one way. The variables that are not of the
   tests are renamed once, over the whole text: a variable that two of the types
   mention has one name in both, so two texts are equal only if one renaming of
   those variables takes the types of the one to the types of the other. *)
let print_with_own_variables (names : names) (types : MT.flambda_type list) :
    string =
  rename_own_variables names
    (String.concat "\n"
       (List.map
          (fun m ->
            Format.asprintf "%a" Model_type.print (Model_type.normalise m))
          types))

(* What a join gives, as printed: the type, then what is said of each of its own
   variables. *)
let print_joined_as_numbered ({ joined; own; own_in_terms } : joined) : string =
  let print ppf t = Model_type.print ppf (Model_type.normalise t) in
  Format.asprintf "@[<v>%a%a@]" print joined
    (fun ppf own ->
      List.iter
        (fun (x, t) ->
          Format.fprintf ppf "@ where %a%s : %a" Model_type.print_variable x
            (if List.mem x own_in_terms
             then ", which terms may mention,"
             else "")
            print t)
        own)
    own

let print_joined (names : names) (joined : joined) : string =
  rename_own_variables names (print_joined_as_numbered joined)

(* What a joined environment says, as printed: the type of the parameter, the
   types of the names of the tests, and what is said of each variable that is
   not of the tests and that any of these types reaches. *)
let print_joined_with_names (names : names) (env : TE.t)
    (parameter : Variable.t) : string =
  let learnt = types_of_names names env in
  rename_own_variables names
    (Format.asprintf "@[<v>%s@ and for the names %a@]"
       (print_joined_as_numbered
          (joined_of_env ~reached_from:learnt names env parameter))
       print_types
       (List.map Model_type.normalise learnt))

let two_implementations (names : names) :
    (MT.flambda_type * MT.flambda_type) comparison list =
  let print_meet ppf result =
    match result with
    | None -> Format.pp_print_string ppf "Bottom"
    | Some (t, types) ->
      Format.fprintf ppf "@[<v>%a@ and for the names %a@]" Model_type.print t
        print_types types
  in
  (* A meet may answer a type that mentions a variable made on the way. The
     environment answered with it is to define every such variable. *)
  let defined_in_the_answer (implementation : implementation) =
    { name =
        Printf.sprintf
          "meet (%s): the variables of the answer are defined in the \
           environment answered"
          implementation.implementation;
      compare =
        (fun (m1, m2) ->
          let t1 = to_compiler names m1 and t2 = to_compiler names m2 in
          match implementation.meet names.env t1 t2 with
          | Bottom -> Not_run "the meet is bottom"
          | Ok (t, env) -> (
            let of_the_names =
              List.map
                (fun (name, kind) -> TE.find env name (Some kind))
                names.defined
            in
            let not_defined =
              List.concat_map
                (fun t ->
                  Name_occurrences.fold_names (TG.free_names t) ~init:[]
                    ~f:(fun not_defined name ->
                      if TE.mem env name
                      then not_defined
                      else name :: not_defined))
                (t :: of_the_names)
            in
            match not_defined with
            | [] -> Agree
            | name :: _ ->
              Known_to_disagree
                ( "T4-9",
                  Format.asprintf
                    "@[<v>the meet answers@ %a@ and the environment answered \
                     does not define %a@]"
                    Model_type.print (to_model names t) Model_type.print_name
                    (Converter.name_to_model names.numbering name) )))
    }
  in
  let well_formed_meet (implementation : implementation) =
    { name =
        Printf.sprintf
          "meet (%s) of two types of which type_well_formed is true: it is \
           true of the answer and of what it teaches"
          implementation.implementation;
      compare =
        (fun (m1, m2) ->
          if not (is_well_formed m1 && is_well_formed m2)
          then Not_run "it is false of one of the two types"
          else
            let t1 = to_compiler names m1 and t2 = to_compiler names m2 in
            match meet_as_model names implementation t1 t2 with
            | None -> Not_run "the meet is bottom"
            | Some (meet, types) -> well_formed (meet :: types))
    }
  in
  let well_formed_join (implementation : implementation) =
    { name =
        Printf.sprintf
          "join (%s) of two types of which type_well_formed is true: it is \
           true of the answer and of what it says of its own variables"
          implementation.implementation;
      compare =
        (fun (m1, m2) ->
          if not (is_well_formed m1 && is_well_formed m2)
          then Not_run "it is false of one of the two types"
          else
            let types = [to_compiler names m1; to_compiler names m2] in
            let joined = join names implementation Value types in
            well_formed (joined.joined :: List.map snd joined.own))
    }
  in
  [ defined_in_the_answer binary;
    defined_in_the_answer n_way;
    well_formed_meet binary;
    well_formed_meet n_way;
    well_formed_join binary;
    well_formed_join n_way;
    { name = "meet: the binary and the n-way implementation";
      compare =
        (fun (m1, m2) ->
          let t1 = to_compiler names m1 and t2 = to_compiler names m2 in
          let of_binary = meet_as_model names binary t1 t2 in
          let of_n_way = meet_as_model names n_way t1 t2 in
          let same =
            match of_binary, of_n_way with
            | None, None -> true
            | Some (t, types), Some (t', types') ->
              Model_type.same t t' && List.equal Model_type.same types types'
            | None, Some _ | Some _, None -> false
          in
          agree_if same
            (Format.asprintf
               "@[<v>the binary meet gives@ %a@ the n-way meet@ %a@]" print_meet
               of_binary print_meet of_n_way))
    };
    { name = "join: the binary and the n-way implementation";
      compare =
        (fun (m1, m2) ->
          let types = [to_compiler names m1; to_compiler names m2] in
          let of_binary = join names binary Value types in
          let of_n_way = join names n_way Value types in
          (* A join may make variables of its own, which are not the same
             variables in the two: the two results are compared as they are
             printed, with those variables named in the order they come. *)
          let printed joined = print_joined names joined in
          if same_text (printed of_binary) (printed of_n_way)
          then Agree
          else
            (* The two may differ in how much they keep: that is recorded and
               not a failure. Whether each is above the types joined is for the
               comparison with the meaning of types. *)
            Known_to_disagree
              ( (match
                   ( MT.is_obviously_unknown of_binary.joined,
                     MT.is_obviously_unknown of_n_way.joined )
                 with
                | true, false ->
                  "T7-3, the binary join is unknown and the n-way join is not"
                | false, true ->
                  "T7-3, the n-way join is unknown and the binary join is not"
                | false, false | true, true ->
                  "T7-3, the two joins know different things"),
                Format.asprintf
                  "@[<v>the binary join gives@ %s@ the n-way join@ %s@]"
                  (printed of_binary) (printed of_n_way) ))
    } ]

(* ======================================================================== *)
(* The equality of types                                                    *)
(* ======================================================================== *)

(* [type_eqb] of FlambdaTypeEqualSpec.v against the compiler's
   [Type_grammar.equal], which the joins ask with the structural setting of the
   flag for sharing, and against the sameness that these tests use
   ([Model_type.same]: two types of the model written in one way are equal). The
   pairs are a type twice (converted twice: two values), a type and one of the
   smaller types that the shrinker gives for it, and two types generated
   apart. *)
let equality_of_types (names : names) :
    (MT.flambda_type * MT.flambda_type) comparison list =
  [ { name = "type_eqb against Type_grammar.equal";
      compare =
        (fun (m1, m2) ->
          let of_model = Type_equal.type_eqb m1 m2 in
          let of_compiler =
            TG.equal (to_compiler names m1) (to_compiler names m2)
          in
          agree_if
            (Bool.equal of_model of_compiler)
            (Format.asprintf "the model answers %b, the compiler %b" of_model
               of_compiler))
    };
    { name = "type_eqb against the sameness of the tests";
      compare =
        (fun (m1, m2) ->
          let of_model = Type_equal.type_eqb m1 m2 in
          let of_tests = Model_type.same m1 m2 in
          agree_if
            (Bool.equal of_model of_tests)
            (Format.asprintf "type_eqb answers %b, the tests %b" of_model
               of_tests))
    };
    { name = "the pairs that type_eqb answers to be the same";
      compare =
        (fun (m1, m2) ->
          if Type_equal.type_eqb m1 m2 then Agree else Not_run "not the same")
    } ]

let generate_pair_for_equality (names : names) (config : G.config) r :
    MT.flambda_type * MT.flambda_type =
  let first = G.flambda_type config r names.pool in
  match G.below r 3 with
  | 0 -> first, first
  | 1 -> (
    match G.shrink first with
    | [] -> first, first
    | _ :: _ as smaller -> first, G.pick r smaller)
  | _ -> first, G.flambda_type config r names.pool

(* ======================================================================== *)
(* Meet and join against the meaning of types                               *)
(* ======================================================================== *)

(* What a type means is [type_satisfied] of FlambdaTypeMeaningSpec.v, which
   [type_satisfied_b] decides (FlambdaTypeMeaningBoolSpec.v, extracted). So what
   a meet and a join of the compiler owe to the meaning can be tested on values,
   before the model has a meet or a join of its own: - a value that has one of
   two types has their join; - a value that has two types has their meet, and
   what the meet teaches of the names is true; and a value that has the meet,
   where what it teaches is true, has the two types. A world is a static
   environment and the values of the variables of the tests. No value of kind
   value in it is poison: typing facts are about values that are not. *)
type world =
  { statics : V.static_env;
    vars : (M.variable * V.value) list
  }

let tagged i : V.value = Value_const (Tagged_immediate (N.z_of_int i))

let naked_immediate i : V.value = Value_const (Naked_immediate (N.z_of_int i))

let const_of_number (k : MK.naked_number_kind) (n : N.z) : M.const =
  match k with
  | Kind_naked_immediate -> Naked_immediate n
  | Kind_naked_float32 -> Naked_float32 n
  | Kind_naked_float -> Naked_float n
  | Kind_naked_int8 -> Naked_int8 n
  | Kind_naked_int16 -> Naked_int16 n
  | Kind_naked_int32 -> Naked_int32 n
  | Kind_naked_int64 -> Naked_int64 n
  | Kind_naked_nativeint -> Naked_nativeint n
  | Kind_naked_vec128 -> Naked_vec128 n
  | Kind_naked_vec256 -> Naked_vec256 n
  | Kind_naked_vec512 -> Naked_vec512 n
  | Kind_naked_mask -> Naked_mask n

let naked_immediate_of_const (c : M.const) : N.z option =
  match c with
  | Naked_immediate i -> Some i
  | Tagged_immediate _ | Naked_float32 _ | Naked_float _ | Naked_int8 _
  | Naked_int16 _ | Naked_int32 _ | Naked_int64 _ | Naked_nativeint _
  | Naked_vec128 _ | Naked_vec256 _ | Naked_vec512 _ | Naked_mask _ | Null
  | Poison _ ->
    None

(* Some value of a kind. *)
let default_of_kind (k : MK.flambda_kind) : V.value =
  match k with
  | Value -> tagged 0
  | Naked_number k -> Value_const (const_of_number k (N.z_of_int 0))
  | Region | Rec_info -> Value_const (Poison k)

(* A value of kind value that is not poison. *)
let rec generate_value (names : names) r depth : V.value =
  let pool = names.pool in
  match if depth <= 0 then 0 else G.below r 10 with
  | 0 | 1 | 2 | 3 -> tagged (G.below r 4)
  | 4 -> Value_const Null
  | 5 | 6 ->
    if G.chance r ~percent:15
    then
      Value_block
        ( MT.double_array_tag,
          G.list r ~max:3 (fun () : V.value ->
              Value_const (Naked_float (N.z_of_int (G.below r 5)))) )
    else
      Value_block
        ( N.z_of_int (G.pick r [0; 1; 2; 250]),
          G.list r ~max:3 (fun () -> generate_value names r (depth - 1)) )
  | 7 ->
    let kind = G.pick r G.boxable_kinds in
    Value_boxed_number (const_of_number kind (N.z_of_int (G.below r 5)))
  | 8 -> (
    let value_slots =
      Model_type.map N.compare_positive Fun.id
        (G.list r ~max:2 (fun () ->
             G.pick r pool.value_slots, generate_value names r (depth - 1)))
    in
    (* The closure of a set of one function with no slot named, or the closure
       at one of the function slots of a set. *)
    let functions =
      if G.chance r ~percent:50
      then []
      else
        List.filter_map
          (fun slot ->
            if G.chance r ~percent:70
            then Some (slot, G.pick r pool.code_ids)
            else None)
          pool.function_slots
    in
    match functions with
    | [] -> Value_closure (G.pick r pool.code_ids, value_slots)
    | _ :: _ ->
      Value_closure_of_set (fst (G.pick r functions), functions, value_slots))
  | _ -> Value_symbol (G.pick r pool.symbols)

let generate_world (names : names) r : world =
  let pool = names.pool in
  let bind variables value = List.map (fun x -> x, value ()) variables in
  (* A static set of closures with a function at each function slot of the pool,
     whose closures are the symbols of the pool in their order. A symbol may be
     bound to its closure of this set; where the others are not, the projection
     of their slots from it gives a symbol that is something else, which the
     machine allows. *)
  let functions =
    List.map (fun slot -> slot, G.pick r pool.code_ids) pool.function_slots
  in
  let closure_symbols =
    List.filteri
      (fun i _ -> i < List.length pool.symbols)
      (List.mapi
         (fun i slot ->
           slot, List.nth pool.symbols (i mod List.length pool.symbols))
         pool.function_slots)
  in
  let value_slots_of_the_set =
    Model_type.map N.compare_positive Fun.id
      (G.list r ~max:2 (fun () ->
           G.pick r pool.value_slots, generate_value names r 1))
  in
  { statics =
      { static_code = [];
        static_values =
          List.map
            (fun symbol : (_ * V.statically_allocated_value) ->
              ( symbol,
                match G.below r 5 with
                | 4 -> (
                  match
                    List.find_opt
                      (fun (_, symbol') -> Stdlib.( = ) symbol symbol')
                      closure_symbols
                  with
                  | Some (slot, _) ->
                    Static_closure_of_set
                      (slot, closure_symbols, functions, value_slots_of_the_set)
                  | None -> Static_block (N.z_of_int 0, []))
                | 0 ->
                  Static_closure
                    ( G.pick r pool.code_ids,
                      [G.pick r pool.value_slots, generate_value names r 1] )
                | 1 ->
                  Static_string
                    (G.list r ~max:3 (fun () -> N.z_of_int (97 + G.below r 3)))
                | 2 ->
                  Static_boxed_number
                    (Value_const (Naked_float (N.z_of_int (G.below r 5))))
                | _ ->
                  Static_block
                    ( N.z_of_int (G.pick r [0; 1; 2]),
                      G.list r ~max:3 (fun () -> generate_value names r 1) ) ))
            pool.symbols
      };
    vars =
      bind pool.value_variables (fun () -> generate_value names r 2)
      @ bind pool.naked_immediate_variables (fun () ->
          naked_immediate (G.below r 3))
      @ bind pool.naked_float_variables (fun () : V.value ->
          Value_const (Naked_float (N.z_of_int (G.below r 5))))
      @ bind pool.region_variables (fun () -> default_of_kind Region)
      @ bind pool.rec_info_variables (fun () -> default_of_kind Rec_info)
  }

let value_of_simple (world : world) (simple : M.simple) : V.value list =
  match simple with
  | Var x -> Option.to_list (List.assoc_opt x world.vars)
  | Symbol s -> [V.Value_symbol s]
  | Const c -> [V.Value_const c]

(* Values that may well have a type: made from the type, to be tried. They are a
   help to the tests and are trusted for nothing: every use of a value asks
   [type_satisfied_b] whether it has the type. *)
let rec values_for (names : names) (world : world) (t : MT.flambda_type) :
    V.value list =
  let descr kind head (ty : _ MT.type_descr) =
    match ty with
    | Unknown -> [default_of_kind kind]
    | Bottom -> []
    | Ok (Equals simple) -> value_of_simple world simple
    | Ok (No_alias h) -> head h
  in
  match t with
  | Type_value ty ->
    descr Value
      (fun (Head_of_kind_value (non_null, is_null) : MT.head_of_kind_value) ->
        (match is_null with
          | Not_null -> []
          | Maybe_null _ -> [V.Value_const Null])
        @
        match non_null with
        | Unknown -> [tagged 0; V.Value_block (N.z_of_int 0, [])]
        | Bottom -> []
        | Ok head -> values_for_head names world head)
      ty
  | Type_naked_immediate ty ->
    descr (Naked_number Kind_naked_immediate)
      (fun (head : MT.head_of_kind_naked_immediate) ->
        match head.naked_immediates with
        | Known numbers ->
          List.map (fun n : V.value -> Value_const (Naked_immediate n)) numbers
        | Unknown -> List.init 4 naked_immediate)
      ty
  | Type_naked_number (k, ty) ->
    descr (Naked_number k)
      (List.map (fun n : V.value -> Value_const (const_of_number k n)))
      ty
  | Type_rec_info _ -> [default_of_kind Rec_info]
  | Type_region _ -> [default_of_kind Region]

and values_for_head names world (head : MT.head_of_kind_value_non_null) :
    V.value list =
  let first_or_default kind t =
    match values_for names world t with
    | v :: _ -> v
    | [] -> default_of_kind kind
  in
  let block tag (case : MT.row_like_block_case) : V.value =
    let size =
      match case.case_index.index_domain with
      | Known size | At_least size -> size
    in
    let kinds = MT.field_kinds case.case_index.index_shape size in
    Value_block
      ( tag,
        List.mapi
          (fun i kind ->
            match List.nth_opt case.case_maps_to i with
            | Some t -> first_or_default kind t
            | None -> default_of_kind kind)
          kinds )
  in
  match head with
  | Variant (_, immediates, _, blocks, _, _) -> (
    (match immediates with
      | Unknown -> [tagged 0; tagged 1]
      | Known t ->
        List.filter_map
          (fun (v : V.value) : V.value option ->
            match v with
            | Value_const c ->
              Option.map
                (fun i : V.value -> Value_const (Tagged_immediate i))
                (naked_immediate_of_const c)
            | Value_closure _ | Value_closure_of_set _ | Value_symbol _
            | Value_block _ | Value_boxed_number _ | Value_location _
            | Value_partial_application _ ->
              None)
          (values_for names world t))
    @
    match blocks with
    | Unknown -> [V.Value_block (N.z_of_int 0, [])]
    | Known (Row_like_for_blocks (known_tags, other_tags, _)) -> (
      List.map
        (fun (tag, (case : _ MT.Or_unknown.t)) ->
          match case with
          | Unknown -> V.Value_block (tag, [])
          | Known case -> block tag case)
        known_tags
      @
      match other_tags with
      | Bottom -> []
      | Ok case -> [block (N.z_of_int 3) case]))
  | Mutable_block _ | String _ -> []
  | Boxed_number (_, contents, _) ->
    List.filter_map
      (fun (v : V.value) : V.value option ->
        match v with
        | Value_const c -> Some (Value_boxed_number c)
        | Value_closure _ | Value_closure_of_set _ | Value_symbol _
        | Value_block _ | Value_boxed_number _ | Value_location _
        | Value_partial_application _ ->
          None)
      (values_for names world contents)
  | Closures (Row_like_for_closures cases, _) ->
    (* For each case, the closure at its function slot of a set with the
       functions and the value slots of the index: each function has the code
       that the case says, or else one code of the pool, tried in turn. Where
       the set is of the one function with no slot named, also the closure that
       names no slot. *)
    List.concat_map
      (fun (slot, (case : (_, _, _, _) MT.row_like_case)) ->
        let (Closures_entry (function_types, _, value_slot_types)
              : MT.closures_entry) =
          case.case_maps_to
        in
        let (contents : MT.set_of_closures_contents) =
          match case.case_index.index_domain with
          | Known contents | At_least contents -> contents
        in
        let value_slots =
          List.map
            (fun slot ->
              ( slot,
                match List.assoc_opt slot value_slot_types with
                | Some t -> first_or_default Value t
                | None -> tagged 0 ))
            (Model_type.set N.compare_positive contents.contents_value_slots)
        in
        let function_slots =
          Model_type.set N.compare_positive (slot :: contents.contents_closures)
        in
        List.concat_map
          (fun code : V.value list ->
            let functions =
              List.map
                (fun slot ->
                  ( slot,
                    match List.assoc_opt slot function_types with
                    | Some (Known { function_type_code_id }) ->
                      function_type_code_id
                    | Some Unknown | None -> code ))
                function_slots
            in
            Value_closure_of_set (slot, functions, value_slots)
            ::
            (match functions with
            | [(slot, code)] when Stdlib.( = ) slot V.unnamed_function_slot ->
              [V.Value_closure (code, value_slots)]
            | [] | _ :: _ -> []))
          names.pool.code_ids)
      cases

(* The values tried against two types: those made from the types, the values of
   the variables and the symbols, and a few more. *)
let candidates (names : names) (world : world) r types : V.value list =
  let not_poison v = not (Meaning.is_poison_b v) in
  List.filter not_poison
    (List.concat_map (values_for names world) types
    @ List.map snd world.vars
    @ List.map (fun symbol -> V.Value_symbol symbol) names.pool.symbols
    @ List.init 8 (fun _ -> generate_value names r 2))

let has (world : world) (v : V.value) (t : MT.flambda_type) : bool =
  Meaning.type_satisfied_b world.statics world.vars v t

let rec parts_of_value (v : V.value) : V.value list =
  v
  ::
  (match v with
  | Value_const _ | Value_symbol _ | Value_boxed_number _ | Value_location _ ->
    []
  | Value_block (_, fields) -> List.concat_map parts_of_value fields
  | Value_closure (_, value_slots) | Value_closure_of_set (_, _, value_slots) ->
    List.concat_map (fun (_, v) -> parts_of_value v) value_slots
  | Value_partial_application (callee, args, _) ->
    parts_of_value callee @ List.concat_map parts_of_value args)

(* A join may make variables of its own, which stand for some value. A value has
   what a join gives if, with the parameter holding the value and for some
   values of those variables, it has the type of the parameter and each of those
   variables has the type that the joined environment gives it. (These types may
   mention the parameter: a relation between it and a variable.) A variable may
   also have no value, and then nothing is asked of its type: it stands for a
   variable that only some of the uses bind, and what satisfies a typing
   environment need not give every variable a value. The values tried for a
   variable are those made from its type, small numbers and the parts of the
   value, of its kind. *)
type own_variables_answer =
  | Has  (** Values were found. *)
  | Has_not
      (** There is no variable to find a value for, and the test fails. *)
  | Unresolved
      (** No values were found for the variables. The search is finite, so this
          decides nothing: it is neither that the value has what the join gives
          nor that it has not. *)

let has_joined (names : names) (world : world) (v : V.value)
    ({ joined; own; own_in_terms = _ } : joined) : own_variables_answer =
  let values_of (x_type : MT.flambda_type) =
    let kind = MT.kind x_type in
    List.fold_left
      (fun values value ->
        if
          Stdlib.( = ) (V.kind_of_value value) kind
          && not (List.exists (Meaning.value_eqb value) values)
        then values @ [value]
        else values)
      []
      (values_for names world x_type
      @ List.map naked_immediate [0; 1; 2; 3; 4; 5; 250; 254]
      @ parts_of_value v)
  in
  let rec for_some vars (rest : (M.variable * MT.flambda_type) list) =
    match rest with
    | [] ->
      Meaning.type_satisfied_b world.statics vars v joined
      && List.for_all
           (fun (x, x_type) ->
             match List.assoc_opt x vars with
             | Some value ->
               Meaning.type_satisfied_b world.statics vars value x_type
             | None -> true)
           own
    | (x, x_type) :: rest ->
      for_some vars rest
      || List.exists
           (fun value -> for_some ((x, value) :: vars) rest)
           (values_of x_type)
  in
  let vars =
    ( Converter.variable_to_model names.numbering
        (parameter names (MT.kind joined)),
      v )
    :: world.vars
  in
  match own with
  | [] ->
    (* No variable of its own: the test decides. *)
    if for_some vars [] then Has else Has_not
  | _ :: _ ->
    (* The search is finite: finding values shows that the value has what the
       join gives; not finding any shows nothing. *)
    if List.compare_length_with own 3 <= 0 && for_some vars own
    then Has
    else Unresolved

let print_value ppf (v : V.value) =
  let rec print ppf (v : V.value) =
    match v with
    | Value_const c -> Model_type.print_const ppf c
    | Value_symbol s -> Model_type.print_symbol ppf s
    | Value_block (tag, fields) ->
      Format.fprintf ppf "@[<hov 1>(block %a@ %a)@]" N.print_z tag
        (Model_type.print_list print)
        fields
    | Value_boxed_number c ->
      Format.fprintf ppf "(boxed %a)" Model_type.print_const c
    | Value_location l -> Format.fprintf ppf "<location %a>" N.print_positive l
    | Value_partial_application (callee, args, _) ->
      Format.fprintf ppf "@[<hov 1>(partial %a@ %a)@]" print callee
        (Model_type.print_list print)
        args
    | Value_closure (code, value_slots) ->
      Format.fprintf ppf "@[<hov 1>(closure code%a@ %a)@]" N.print_positive code
        print_value_slots value_slots
    | Value_closure_of_set (slot, functions, value_slots) ->
      Format.fprintf ppf "@[<hov 1>(closure at %a of@ %a@ %a)@]"
        N.print_positive slot
        (Model_type.print_list (fun ppf (slot, code) ->
             Format.fprintf ppf "%a = code%a" N.print_positive slot
               N.print_positive code))
        functions print_value_slots value_slots
  and print_value_slots ppf value_slots =
    Model_type.print_list
      (fun ppf (slot, v) ->
        Format.fprintf ppf "%a = %a" N.print_positive slot print v)
      ppf value_slots
  in
  print ppf v

type semantic_case =
  { world_seed : int;
    first : MT.flambda_type;
    second : MT.flambda_type
  }

let semantic_comparisons (names : names) : semantic_case comparison list =
  let setting { world_seed; first; second } =
    let r = Random.of_int world_seed in
    let world = generate_world names r in
    let values = candidates names world r [first; second] in
    world, values, to_compiler names first, to_compiler names second
  in
  let join_is_above (implementation : implementation) =
    { name =
        Printf.sprintf "join (%s): a value of one of the types has the join"
          implementation.implementation;
      compare =
        (fun ({ world_seed = _; first; second } as case) ->
          let world, values, t1, t2 = setting case in
          let kind = MT.kind first in
          if not (Stdlib.( = ) kind (MT.kind second))
          then Not_run "the two types are not of one kind"
          else
            let join = join names implementation kind [t1; t2] in
            let of_an_input =
              List.filter
                (fun v -> has world v first || has world v second)
                values
            in
            let outside =
              List.find_opt
                (fun v ->
                  match has_joined names world v join with
                  | Has_not -> true
                  | Has | Unresolved -> false)
                of_an_input
            in
            match outside, of_an_input with
            | Some v, _ ->
              let what =
                Format.asprintf
                  "@[<v>the value %a has one of the types and not their join,@ \
                   %s@]"
                  print_value v (print_joined names join)
              in
              (* Before its repair in the compiler the n-way join kept a
                 function type that only one of the types has (T1-4), and such a
                 case was shown as recorded. It is a failure like any other
                 now. *)
              Disagree what
            | None, [] -> Not_run "no value tried has either type"
            | None, _ :: _ ->
              if
                List.exists
                  (fun v ->
                    match has_joined names world v join with
                    | Unresolved -> true
                    | Has | Has_not -> false)
                  of_an_input
              then
                Not_run
                  "the join has variables of its own, and no values were found \
                   for them"
              else Agree)
    }
  in
  let types_of_names_in world env =
    List.filter_map
      (fun (name, kind) ->
        let value : V.value option =
          Name.pattern_match name
            ~var:(fun var ->
              List.assoc_opt
                (Converter.variable_to_model names.numbering var)
                world.vars)
            ~symbol:(fun symbol ->
              Some
                (V.Value_symbol
                   (Converter.symbol_to_model names.numbering symbol)))
        in
        match value with
        | Some value when not (Meaning.is_poison_b value) ->
          Some (name, value, to_model names (TE.find env name (Some kind)))
        | Some _ | None -> None)
      names.defined
  in
  let contains ~part whole =
    let length = String.length part in
    let rec at i =
      i + length <= String.length whole
      && (String.equal (String.sub whole i length) part || at (i + 1))
    in
    at 0
  in
  let meet_is_the_values_of_both (implementation : implementation) =
    { name =
        Printf.sprintf "meet (%s): a value of both types has the meet"
          implementation.implementation;
      compare =
        (fun ({ world_seed = _; first; second } as case) ->
          let world, values, t1, t2 = setting case in
          let of_both =
            List.filter
              (fun v -> has world v first && has world v second)
              values
          in
          match implementation.meet names.env t1 t2 with
          | Bottom -> (
            match of_both with
            | v :: _ ->
              Disagree
                (Format.asprintf
                   "the meet is bottom, and the value %a has both types"
                   print_value v)
            | [] -> Not_run "no value tried has both types")
          | Ok (meet, env) -> (
            let meet = to_model names meet in
            let learnt = types_of_names_in world env in
            let untrue =
              List.find_opt
                (fun (_, value, t) -> not (has world value t))
                learnt
            in
            match
              List.find_opt (fun v -> not (has world v meet)) of_both, untrue
            with
            | Some v, _ ->
              Disagree
                (Format.asprintf
                   "@[<v>the value %a has both types and not their meet,@ %a@]"
                   print_value v Model_type.print meet)
            | None, Some (name, value, t) when of_both <> [] ->
              let what =
                Format.asprintf
                  "@[<v>a value has both types, and the meet says of %a, which \
                   is %a, that it has the type@ %a@]"
                  Model_type.print_name
                  (Converter.name_to_model names.numbering name)
                  print_value value Model_type.print t
              in
              (* What [reduce_inverse_relations] deduces from [Get_tag]: one of
                 the types has that relation somewhere, at the top or in the
                 immediates of a variant. *)
              let printed =
                Format.asprintf "%a %a" Model_type.print first Model_type.print
                  second
              in
              if contains ~part:"Get_tag " printed
              then Known_to_disagree ("T1-1", what)
              else Disagree what
            | None, (Some _ | None) ->
              if of_both = []
              then Not_run "no value tried has both types"
              else Agree))
    }
  in
  (* The other way, which is about how much a meet keeps and not about whether
     it is right: where what the meet teaches of the names is true, a value of
     the meet has both types. Where it has not, the meet is larger than the two
     types together. *)
  let meet_is_no_larger (implementation : implementation) =
    { name =
        Printf.sprintf "meet (%s): a value of the meet has both types"
          implementation.implementation;
      compare =
        (fun ({ world_seed = _; first; second } as case) ->
          let world, values, t1, t2 = setting case in
          match implementation.meet names.env t1 t2 with
          | Bottom -> Not_run "the meet is bottom: no value has it"
          | Ok (meet, env) -> (
            let meet = to_model names meet in
            let learnt = types_of_names_in world env in
            if
              not (List.for_all (fun (_, value, t) -> has world value t) learnt)
            then Not_run "what the meet teaches is not true in the world"
            else
              match
                List.find_opt
                  (fun v ->
                    has world v meet
                    && not (has world v first && has world v second))
                  values
              with
              | None ->
                if List.exists (fun v -> has world v meet) values
                then Agree
                else Not_run "no value tried has the meet"
              | Some v ->
                let what =
                  Format.asprintf
                    "@[<v>the value %a has the meet,@ %a@ and not both types@]"
                    print_value v Model_type.print meet
                in
                let printed =
                  Format.asprintf "%a %a" Model_type.print first
                    Model_type.print second
                in
                if contains ~part:"Mutable_block" printed
                then
                  Known_to_disagree
                    ("T7-5, the meet with a mutable block keeps too much", what)
                else if
                  contains ~part:"(Maybe_null (Some" printed
                  || contains ~part:"(is_int (Some" printed
                  || contains ~part:"(get_tag (Some" printed
                then
                  Known_to_disagree
                    ( "T7-4, the meet forgets what a variable of a type holds",
                      what )
                else if
                  contains ~part:"Is_null " printed
                  || contains ~part:"Is_int " printed
                  || contains ~part:"Get_tag " printed
                then
                  Known_to_disagree
                    ( "T7-6, the meet forgets a relation of a naked immediate",
                      what )
                else Disagree what))
    }
  in
  [ join_is_above binary;
    join_is_above n_way;
    meet_is_the_values_of_both binary;
    meet_is_the_values_of_both n_way;
    meet_is_no_larger binary;
    meet_is_no_larger n_way ]

let print_semantic_case ppf { world_seed; first; second } =
  Format.fprintf ppf "@[<v>%a@ and@ %a@ in the world of seed %d@]"
    Model_type.print first Model_type.print second world_seed

let shrink_semantic_case ({ world_seed = _; first; second } as case) =
  List.map (fun first -> { case with first }) (G.shrink first)
  @ List.map (fun second -> { case with second }) (G.shrink second)

(* ======================================================================== *)
(* Shared and not                                                           *)
(* ======================================================================== *)

(* The results of meet and join are to be functions of the structure of their
   inputs: a type built once and given twice (shared: the two arguments are one
   value) and the same type built twice (not shared) are to give the same
   result. Where they do not, the result depends on physical equality. *)
let shared_and_not (names : names) (sharing : sharing) :
    MT.flambda_type comparison list =
  let compare_results name of_types =
    { name;
      compare =
        (fun m ->
          let t = to_compiler names m in
          let again = to_compiler names m in
          if t == again
          then Not_run "the type built twice is one value"
          else
            let shared = of_types t t in
            let not_shared = of_types t again in
            if same_text shared not_shared
            then Agree
            else
              depends_on_sharing sharing
                (Format.asprintf
                   "@[<v>with the two arguments one value:@ %s@ with the type \
                    built twice:@ %s@]"
                   shared not_shared))
    }
  in
  let join implementation t t' =
    print_joined names (join names implementation Value [t; t'])
  in
  let meet implementation t t' =
    match meet_as_model names implementation t t' with
    | None -> "Bottom"
    | Some (meet, types) -> print_with_own_variables names (meet :: types)
  in
  [ compare_results "join (binary) of a type with itself" (join binary);
    compare_results "join (n-way) of a type with itself" (join n_way);
    compare_results "meet (binary) of a type with itself" (meet binary);
    compare_results "meet (n-way) of a type with itself" (meet n_way) ]

(* ======================================================================== *)
(* Shared parts                                                             *)
(* ======================================================================== *)

(* The same for two different types that have a part in common: the part is
   converted once and put in both (the two types share one value), or converted
   twice. The types are made around the parts by the compiler's own functions: -
   two blocks of tag 0 whose first field is the common part; - two variants of
   immediates whose immediate case says of a variable that it has the common
   part as its type; - two uses of a continuation that pass the same variable,
   each knowing that the variable has the common part as its type. What is
   compared is the type of the parameter with what the join says of the names of
   the tests and of each variable of its own that any of these types reaches. *)
type parts =
  { common : MT.flambda_type;
    left : MT.flambda_type;
    right : MT.flambda_type
  }

let shared_parts (names : names) (sharing : sharing) : parts comparison list =
  let variable =
    Converter.variable_of_model names.numbering
      (List.hd names.pool.value_variables)
  in
  let block fields =
    MTC.immutable_block ~machine_width ~is_unique:false
      (Converter.tag_of_model machine_width (N.z_of_int 0))
      ~shape:(Converter.block_shape_of_model (Scannable Value_only))
      (Converter.alloc_mode_of_model Heap)
      ~fields
  in
  let variant numbers said =
    TG.create_variant ~is_unique:false
      ~immediates:
        (Known
           (to_compiler names
              (MT.these_naked_immediates (List.map N.z_of_int numbers))))
      ~blocks:
        (Known
           (Converter.row_like_for_blocks_of_model names.numbering machine_width
              MT.row_like_for_blocks_bottom))
      ~extensions:
        (Ext
           { when_immediate =
               TG.Env_extension.create
                 ~equations:(Name.Map.singleton (Name.var variable) said);
             when_block = TG.Env_extension.empty
           })
  in
  let join implementation ?known types =
    let env, parameter = join_env names implementation ?known Value types in
    print_joined_with_names names env parameter
  in
  let meet implementation t t' =
    match meet_as_model names implementation t t' with
    | None -> "Bottom"
    | Some (meet, types) -> print_with_own_variables names (meet :: types)
  in
  let compare_results name result =
    { name;
      compare =
        (fun { common; left; right } ->
          let once = to_compiler names common in
          let again = to_compiler names common in
          if once == again
          then Not_run "the common part built twice is one value"
          else
            let left = to_compiler names left in
            let right = to_compiler names right in
            let shared = result ~common:once ~common':once ~left ~right in
            let not_shared = result ~common:once ~common':again ~left ~right in
            if same_text shared not_shared
            then Agree
            else
              depends_on_sharing sharing
                (Format.asprintf
                   "@[<v>with the common part one value:@ %s@ with the common \
                    part built twice:@ %s@]"
                   shared not_shared))
    }
  in
  let of_blocks operation ~common ~common' ~left ~right =
    operation (block [common; left]) (block [common'; right])
  in
  let of_variants (implementation : implementation) ~common ~common' ~left:_
      ~right:_ =
    join implementation [variant [5; 6] common; variant [6; 7] common']
  in
  let of_what_is_known (implementation : implementation) ~common ~common'
      ~left:_ ~right:_ =
    let passed = TG.alias_type_of K.value (Simple.var variable) in
    join implementation
      ~known:(fun i -> [(Name.var variable, if i = 0 then common else common')])
      [passed; passed]
  in
  List.concat_map
    (fun (implementation : implementation) ->
      let name what =
        Printf.sprintf "join (%s) of %s" implementation.implementation what
      in
      [ compare_results
          (name "two blocks with a common field")
          (of_blocks (fun t t' -> join implementation [t; t']));
        compare_results
          (name "two variants whose immediate case says the same")
          (of_variants implementation);
        compare_results
          (name "a variable of which the two uses know the same")
          (of_what_is_known implementation) ])
    [binary; n_way]
  @ List.map
      (fun (implementation : implementation) ->
        compare_results
          (Printf.sprintf "meet (%s) of two blocks with a common field"
             implementation.implementation)
          (of_blocks (meet implementation)))
      [binary; n_way]

(* ======================================================================== *)
(* Chosen joins                                                             *)
(* ======================================================================== *)

(* Joins chosen by hand, where the two implementations are known or thought to
   part. For each: the types joined, what each implementation gives, and for a
   few values, each in a world where the variables named hold the values given,
   which of the types joined the value has and whether it has what each join
   gives. A value that has one of the types and not a join is a disagreement,
   unless it is recorded. *)
type use =
  { (* The variables that only this use binds, with their types. *)
    binds : (M.variable * MT.flambda_type) list;
    (* What this use knows of names that the source defines. *)
    learns : (MT.name * MT.flambda_type) list;
    (* The type of what the continuation is applied to. *)
    passes : MT.flambda_type
  }

type chosen_join =
  { title : string;
    kind : MK.flambda_kind;
    (* Variables that the source defines for types only. *)
    in_types : M.variable list;
    (* What every use knows of the names of the tests. *)
    known : (MT.name * MT.flambda_type) list;
    uses : use list;
    probes : ((M.variable * V.value) list * V.value) list;
    (* The entry that records that the n-way join is not above the types. *)
    recorded : string option
  }

(* A world where every variable of the tests holds the first value of its kind
   and every symbol is a block of tag 0 with no field. *)
let plain_world (names : names) : world =
  let pool = names.pool in
  let bind kind = List.map (fun x -> x, default_of_kind kind) in
  { statics =
      { static_code = [];
        static_values =
          List.map
            (fun symbol : (_ * V.statically_allocated_value) ->
              symbol, Static_block (N.z_of_int 0, []))
            pool.symbols
      };
    vars =
      bind Value pool.value_variables
      @ bind (Naked_number Kind_naked_immediate) pool.naked_immediate_variables
      @ bind (Naked_number Kind_naked_float) pool.naked_float_variables
      @ bind Region pool.region_variables
      @ bind Rec_info pool.rec_info_variables
  }

let print_lines ppf text =
  Format.pp_print_list ~pp_sep:Format.pp_print_cut Format.pp_print_string ppf
    (String.split_on_char '\n' text)

let chosen_joins (names : names) (cases : chosen_join list) =
  Format.printf "@.Chosen joins@.";
  let print_type ppf t = Model_type.print ppf (Model_type.normalise t) in
  let plain = plain_world names in
  List.iter
    (fun { title; kind; in_types; known; uses; probes; recorded } ->
      let lines = ref [] in
      let line print = lines := print :: !lines in
      List.iter
        (fun x ->
          line (fun ppf ->
              Format.fprintf ppf "the source defines %a for types only"
                Model_type.print_variable x))
        in_types;
      List.iter
        (fun { binds; learns; passes } ->
          line (fun ppf ->
              Format.fprintf ppf "@[<v 2>at one use:@ @[%a@]" print_type passes;
              List.iter
                (fun (x, t) ->
                  Format.fprintf ppf "@ where that use binds %a :@ @[%a@]"
                    Model_type.print_variable x print_type t)
                binds;
              List.iter
                (fun (name, t) ->
                  Format.fprintf ppf "@ where that use knows of %a:@ @[%a@]"
                    Model_type.print_name name print_type t)
                learns;
              Format.fprintf ppf "@]"))
        uses;
      List.iter
        (fun (name, t) ->
          line (fun ppf ->
              Format.fprintf ppf "@[<v 2>every use knows of %a:@ @[%a@]@]"
                Model_type.print_name name print_type t))
        known;
      let compiler_name = Converter.name_of_model names.numbering in
      let compiler_variable = Converter.variable_of_model names.numbering in
      let compiler_types =
        List.map (fun { passes; _ } -> to_compiler names passes) uses
      in
      let equations =
        List.map (fun (name, t) -> compiler_name name, to_compiler names t)
      in
      let compiler_known i =
        equations known @ equations (List.nth uses i).learns
      in
      let compiler_locals i =
        List.map
          (fun (x, t) -> compiler_variable x, to_compiler names t)
          (List.nth uses i).binds
      in
      (* The names of the source of which one use knows something that the
         others do not, or that are for types only: what each use and each join
         says of them is shown. *)
      let watched =
        List.sort_uniq Stdlib.compare
          (List.map (fun x -> MT.Name_var x) in_types
          @ List.concat_map (fun { learns; _ } -> List.map fst learns) uses)
      in
      let says_of env ppf (name : MT.name) =
        let compiler = compiler_name name in
        let simple = Simple.name compiler in
        Format.fprintf ppf "says of %a:@ @[%a@]" Model_type.print_name name
          print_type
          (to_model names (TE.find env compiler None));
        let canonical = TE.get_canonical_simple_ignoring_name_mode env simple in
        if not (Simple.equal canonical simple)
        then
          Format.fprintf ppf "@ which is %a" Model_type.print_simple
            (Converter.simple_to_model names.numbering canonical)
      in
      let joins =
        List.map
          (fun (implementation : implementation) ->
            let observe use_envs =
              if watched <> []
              then
                List.iteri
                  (fun i use_env ->
                    let text =
                      Format.asprintf "@[<v 2>use %d of the %s join%s%a@]"
                        (i + 1) implementation.implementation
                        (if TE.is_bottom use_env
                         then ", whose environment is bottom,"
                         else "")
                        (fun ppf ->
                          List.iter (fun name ->
                              Format.fprintf ppf " %a" (says_of use_env) name))
                        watched
                    in
                    line (fun ppf -> print_lines ppf text))
                  use_envs
            in
            let joined =
              or_fatal_error (fun () ->
                  let env, parameter =
                    join_env names implementation ~known:compiler_known
                      ~locals:compiler_locals
                      ~in_types:(List.map compiler_variable in_types)
                      ~observe kind compiler_types
                  in
                  ( joined_of_env names env parameter,
                    List.map
                      (fun name ->
                        Format.asprintf "@[<v 2>%a@]" (says_of env) name)
                      watched ))
            in
            let given =
              match joined with
              | Ok (joined, _) -> print_joined names joined
              | Error what ->
                "nothing: the compiler stops with the fatal error " ^ what
            in
            line (fun ppf ->
                Format.fprintf ppf "@[<v 2>the %s join gives@ %a@]"
                  implementation.implementation print_lines given);
            (match joined with
            | Ok (_, of_the_watched) ->
              List.iter
                (fun text ->
                  line (fun ppf ->
                      Format.fprintf ppf "@[<v 2>the %s join %a@]"
                        implementation.implementation print_lines text))
                of_the_watched
            | Error _ -> ());
            implementation, Option.map fst (Result.to_option joined))
          [binary; n_way]
      in
      List.iter
        (fun (assignments, v) ->
          let world = { plain with vars = assignments @ plain.vars } in
          (* A value has the type of a use for some values of the variables that
             the use binds. Where the use binds some and no values are found for
             them, it is not known whether the value has the type. *)
          let of_each_use =
            List.mapi
              (fun i { binds; passes; learns = _ } ->
                ( string_of_int (i + 1),
                  has_joined names world v
                    { joined = passes; own = binds; own_in_terms = [] } ))
              uses
          in
          let uses_that answer =
            List.filter_map
              (fun (use, answer') ->
                if Stdlib.( = ) answer answer' then Some use else None)
              of_each_use
          in
          let of_the_types = uses_that Has in
          let of_a_join ((implementation : implementation), joined) =
            Option.map
              (fun joined ->
                Printf.sprintf "the %s join: %s" implementation.implementation
                  (match has_joined names world v joined with
                  | Has -> "yes"
                  | Unresolved ->
                    "not for the values tried of its own variables"
                  | Has_not -> (
                    match of_the_types, recorded with
                    | [], _ -> "no"
                    | _ :: _, Some entry -> "no (recorded as " ^ entry ^ ")"
                    | _ :: _, None ->
                      incr failures;
                      "no: A DISAGREEMENT")))
              joined
          in
          let of_the_uses =
            (match of_the_types with
              | [] -> []
              | [use] -> ["use " ^ use]
              | _ :: _ :: _ -> ["uses " ^ String.concat " and " of_the_types])
            @ List.map
                (fun use ->
                  "use " ^ use
                  ^ " not for the values tried of the variables it binds")
                (uses_that Unresolved)
          in
          let answers =
            (match of_the_uses with
            | [] -> "no use"
            | _ :: _ -> String.concat ", " of_the_uses)
            :: List.filter_map of_a_join joins
          in
          line (fun ppf ->
              List.iter
                (fun (x, value) ->
                  Format.fprintf ppf "with %a = %a, " Model_type.print_variable
                    x print_value value)
                assignments;
              Format.fprintf ppf "%a: %s" print_value v
                (String.concat "; " answers)))
        probes;
      Format.printf "  @[<v 2>@[%a@]@ %a@]@." Format.pp_print_text title
        (Format.pp_print_list ~pp_sep:Format.pp_print_cut (fun ppf print ->
             print ppf))
        (List.rev !lines))
    cases

let the_chosen_joins (names : names) : chosen_join list =
  let pool = names.pool in
  let z = N.z_of_int in
  let x = List.hd pool.value_variables in
  let i = List.hd pool.naked_immediate_variables in
  let local = Converter.variable_to_model names.numbering names.local in
  let for_types_only =
    Converter.variable_to_model names.numbering names.for_types_only
  in
  let use ?(binds = []) ?(learns = []) passes = { binds; learns; passes } in
  let constant n = MT.this_tagged_immediate (z n) in
  let block fields =
    MT.immutable_block false (z 0) (Scannable Value_only) Heap fields
  in
  let block_value fields : V.value =
    Value_block (z 0, List.map tagged fields)
  in
  let no_blocks = MT.Or_unknown.Known MT.row_like_for_blocks_bottom in
  let variant_5_or_6 numbers =
    MT.create_variant false
      (Known (MT.these_naked_immediates [z 5; z 6]))
      no_blocks
      (Ext
         ( Env_extension
             [Name_var i, MT.these_naked_immediates (List.map z numbers)],
           MT.empty_env_extension ))
  in
  let is_int_of_x numbers : MT.flambda_type =
    Type_naked_immediate
      (Ok
         (No_alias
            { naked_immediates = Known (List.map z numbers);
              inverse_relations = [Is_int, Name_var x]
            }))
  in
  let slot =
    List.find
      (fun slot -> Stdlib.( = ) slot V.unnamed_function_slot)
      pool.function_slots
  in
  let closure function_types =
    MT.at_least_this_closure slot function_types [] [] MT.Alloc_mode.Heap
  in
  let code, other_code =
    match pool.code_ids with
    | code :: other_code :: _ -> code, other_code
    | [] | [_] -> assert false
  in
  [ { title =
        "Two blocks, (0, 0) and (1, 1), each field an alias of its constant";
      kind = Value;
      in_types = [];
      known = [];
      uses =
        (let zero = constant 0 and one = constant 1 in
         [use (block [zero; zero]); use (block [one; one])]);
      probes =
        [ [], block_value [0; 0];
          [], block_value [1; 1];
          [], block_value [0; 1];
          [], block_value [2; 2] ];
      recorded = None
    };
    { title =
        "The immediate 0, and a block whose field is a variable that only that \
         use binds, known to be 4 or 5";
      kind = Value;
      in_types = [];
      known = [];
      uses =
        [ use (constant 0);
          use
            ~binds:[local, MT.these_tagged_immediates [z 4; z 5]]
            (block [MT.alias_type_of Value (Var local)]) ];
      probes =
        [ [], tagged 0;
          [], block_value [4];
          [], block_value [5];
          [], block_value [6];
          [], tagged 1 ];
      recorded = None
    };
    { title =
        "The same, the variable known to be 4: its type is the alias of the \
         constant";
      kind = Value;
      in_types = [];
      known = [];
      uses =
        [ use (constant 0);
          use
            ~binds:[local, MT.these_tagged_immediates [z 4]]
            (block [MT.alias_type_of Value (Var local)]) ];
      probes = [[], tagged 0; [], block_value [4]; [], block_value [5]];
      recorded = None
    };
    { title =
        "The immediates 5 and 6 as a variant whose immediate case says that a \
         variable is 1, and that it is 2 (R1-15)";
      kind = Value;
      in_types = [];
      known = [];
      uses = [use (variant_5_or_6 [1]); use (variant_5_or_6 [2])];
      probes =
        [ [i, naked_immediate 1], tagged 5;
          [i, naked_immediate 2], tagged 5;
          [i, naked_immediate 3], tagged 5;
          [i, naked_immediate 1], tagged 7 ];
      recorded = None
    };
    { title =
        "A number that is 0 or 2, and one that is 2 or 4, each what is_int \
         answers on a variable that every use knows to be the immediate 3: no \
         number is either (R1-16)";
      kind = Naked_number Kind_naked_immediate;
      in_types = [];
      known = [Name_var x, constant 3];
      uses = [use (is_int_of_x [0; 2]); use (is_int_of_x [2; 4])];
      probes =
        [ [x, tagged 3], naked_immediate 0;
          [x, tagged 3], naked_immediate 1;
          [x, tagged 3], naked_immediate 2 ];
      recorded = None
    };
    { title =
        "The same two numbers as the immediates of two variants with no block \
         (R1-16)";
      kind = Value;
      in_types = [];
      known = [Name_var x, constant 3];
      uses =
        [ use
            (MT.create_variant false
               (Known (is_int_of_x [0; 2]))
               no_blocks No_extensions);
          use
            (MT.create_variant false
               (Known (is_int_of_x [2; 4]))
               no_blocks No_extensions) ];
      probes = [[x, tagged 3], tagged 0; [x, tagged 3], tagged 2];
      recorded = None
    };
    { title =
        "A variable of the source, for types only, that one use knows to be 0 \
         or 2 and what is_int answers on a variable known to be the immediate \
         3 (no number is that), and the other use knows to be 1";
      kind = Value;
      in_types = [for_types_only];
      known = [Name_var x, constant 3];
      uses =
        [ use
            ~learns:[Name_var for_types_only, is_int_of_x [0; 2]]
            (MT.this_tagged_immediate (z 0));
          use
            ~learns:[Name_var for_types_only, MT.this_naked_immediate (z 1)]
            (constant 0) ];
      probes = [];
      recorded = None
    };
    { title =
        "A closure whose own function has a known code, and one of which \
         nothing is said of the code (T1-4)";
      kind = Value;
      in_types = [];
      known = [];
      uses =
        [ use
            (closure
               [slot, MT.Or_unknown.Known { function_type_code_id = code }]);
          use (closure []) ];
      probes =
        [[], V.Value_closure (code, []); [], V.Value_closure (other_code, [])];
      recorded = None
    } ]

(* ======================================================================== *)
(* Examples of the join of types                                            *)
(* ======================================================================== *)

(* Small joins whose answers were written down from a transcription of the n-way
   join of types into the model, without running the compiler
   (middle_end/flambda2/types/rocq/FlambdaJoinTypesExamplesSpec.v). Each is run
   here: the types are the types of the argument at the uses of a continuation,
   and the answer is the type of the parameter in the joined environment, which
   is compared with the answer written down.

   Where the transcription makes a variable, the compiler makes one of its own
   and gives it a type in the joined environment. The join of environments then
   projects out a variable that is mentioned once and is not what [Is_int],
   [Get_tag] or [Is_null] answers: its type is put in its place
   ([Join_env.define_or_eliminate_variables_and_add_equations]). So: - where the
   variable is for [Is_int] or [Get_tag], the answer written down has a variable
   that is not of the tests there, the two are compared as text with those
   variables renamed, and what the compiler says of its variable is shown; -
   where it is another variable, mentioned once, the answer written here is not
   the statement's: it has in the place of the variable the type that the notes
   of the transcription say the variable has, the join of the types of what it
   stands for.

   Each example says where it is from: a statement of that file, by its name
   without [example_join_] and [_statement], with its inputs and its answer; a
   statement with its inputs and another answer, for the reason above; or not
   that file.

   A difference does not fail the test: it is shown, for the owner of the
   transcription to say which side is wrong. *)
type source =
  | Statement of string
  | Statement_with_another_answer of string
  | Not_from_the_file

type written_down =
  | Answer of MT.flambda_type
  | Thought_to_stop
      (** The transcription has no answer, where the compiler is thought to
          stop. *)
  | Nothing_to_compare of string
      (** What the compiler answers is shown, and why it is not compared. *)

type example_of_join =
  { example : string;
    source : source;
    (* What every use knows of variables of the tests. *)
    knowing : (M.variable * MT.flambda_type) list;
    inputs : MT.flambda_type list;
    answer : written_down
  }

let examples_of_joins (names : names) : example_of_join list =
  let z = N.z_of_int in
  let numbers = List.map z in
  let own i = N.positive_of_int (names.variables_with_a_name + i) in
  let x, y =
    match names.pool.value_variables with
    | x :: y :: _ -> x, y
    | [] | [_] -> assert false
  in
  let function_slot = List.hd names.pool.function_slots in
  let value_slot = List.hd names.pool.value_slots in
  let code, other_code =
    match names.pool.code_ids with
    | code :: other_code :: _ -> code, other_code
    | [] | [_] -> assert false
  in
  let naked_immediate : MK.flambda_kind = Naked_number Kind_naked_immediate in
  let naked_float : MK.flambda_kind = Naked_number Kind_naked_float in
  let tagged = MT.these_tagged_immediates in
  let constant i = MT.this_tagged_immediate (z i) in
  let alias variable = MT.alias_type_of Value (Var variable) in
  let floats numbers : MT.flambda_type =
    Type_naked_number (Kind_naked_float, Ok (No_alias numbers))
  in
  (* An alias of kind value to a naked immediate. *)
  let alias_to_a_naked_immediate =
    MT.alias_type_of Value (Const (Naked_immediate (z 1)))
  in
  (* A variant with the variables given for [Is_int] and [Get_tag], the
     immediates given, and for each tag listed the blocks on the heap of exactly
     the fields given, which are values. *)
  let variant is_int immediates get_tag blocks : MT.flambda_type =
    MT.non_null_value
      (Variant
         ( is_int,
           Known immediates,
           get_tag,
           Known
             (Row_like_for_blocks
                ( List.map
                    (fun (tag, fields) ->
                      ( z tag,
                        MT.Or_unknown.Known
                          ({ case_maps_to = fields;
                             case_index =
                               { index_domain =
                                   Known (N.nat_of_int (List.length fields));
                                 index_shape = Scannable Value_only
                               };
                             case_env_extension = MT.empty_env_extension
                           }
                            : MT.row_like_block_case) ))
                    blocks,
                  Bottom,
                  Heap )),
           No_extensions,
           false ))
  in
  let block tag fields =
    MT.immutable_block false (z tag) (Scannable Value_only) Heap fields
  in
  let function_types codes =
    List.map
      (fun code_id ->
        ( function_slot,
          MT.Or_unknown.Known
            ({ function_type_code_id = code_id } : MT.function_type) ))
      codes
  in
  (* The closure at the function slot of a set of that one function, with or
     without a function type for it, and one value slot. *)
  let closure codes value_slot_type =
    MT.exactly_this_closure function_slot (function_types codes) []
      [value_slot, value_slot_type]
      Heap
  in
  let statement ?(knowing = []) name example inputs answer =
    { example; source = Statement name; knowing; inputs; answer }
  in
  let with_another_answer ?(knowing = []) name example inputs answer =
    { example;
      source = Statement_with_another_answer name;
      knowing;
      inputs;
      answer = Answer answer
    }
  in
  let not_from_the_file ?(knowing = []) example inputs answer =
    { example;
      source = Not_from_the_file;
      knowing;
      inputs;
      answer = Answer answer
    }
  in
  [ statement "naked_immediates" "two sets of naked immediates"
      [ MT.these_naked_immediates (numbers [1; 2]);
        MT.these_naked_immediates (numbers [2; 3]) ]
      (Answer (MT.these_naked_immediates (numbers [1; 2; 3])));
    statement "tagged_immediates" "two sets of tagged immediates"
      [tagged (numbers [1; 2]); tagged (numbers [3; 4])]
      (Answer (tagged (numbers [3; 4; 1; 2])));
    statement "boxed_floats" "two boxed floats"
      [ MT.box_number Boxable_naked_float (floats (numbers [1; 2])) Heap;
        MT.box_number Boxable_naked_float (floats (numbers [3])) Heap ]
      (Answer
         (MT.box_number Boxable_naked_float (floats (numbers [1; 2; 3])) Heap));
    statement "strings" "two strings"
      [ MT.this_immutable_string (numbers [104; 105]);
        MT.this_immutable_string (numbers [111]) ]
      (Answer (MT.non_null_value (String [numbers [104; 105]; numbers [111]])));
    statement "one_constant" "one constant twice"
      [constant 5; constant 5]
      (Answer (constant 5));
    statement "two_constants" "two constants"
      [constant 5; constant 6]
      (Nothing_to_compare
         "the transcription makes a variable and answers an alias to it; here \
          the parameter is that variable, and the answer is its type");
    not_from_the_file
      "two constants in a field (a variable is made, mentioned once: its type \
       is in its place)"
      [block 0 [constant 5]; block 0 [constant 6]]
      (block 0 [tagged (numbers [5; 6])]);
    not_from_the_file
      "two constants in two fields (one variable is made, mentioned twice)"
      [block 0 [constant 5; constant 5]; block 0 [constant 6; constant 6]]
      (block 0 [alias (own 1); alias (own 1)]);
    statement "constant_and_set" "a constant and a set"
      [constant 5; tagged (numbers [1; 2])]
      (Answer (tagged (numbers [1; 2; 5])));
    statement "unknown" "a set and the unknown type"
      [MT.these_naked_immediates (numbers [1; 2]); MT.unknown naked_immediate]
      (Answer (MT.unknown naked_immediate));
    statement "bottom" "a set and bottom"
      [MT.these_naked_immediates (numbers [1; 2]); MT.bottom naked_immediate]
      (Answer (MT.these_naked_immediates (numbers [1; 2])));
    statement "all_bottom" "bottom twice"
      [MT.bottom Value; MT.bottom Value]
      (Answer (MT.bottom Value));
    statement "string_and_immediate" "a string and a tagged immediate"
      [MT.this_immutable_string (numbers [104; 105]); MT.any_tagged_immediate]
      (Answer MT.any_non_null_value);
    statement "null_and_immediate" "null and a tagged immediate"
      [MT.null; MT.any_tagged_immediate]
      (Answer
         (Type_value
            (Ok
               (No_alias
                  (Head_of_kind_value
                     ( Ok
                         (Variant
                            ( None,
                              Unknown,
                              None,
                              Known MT.row_like_for_blocks_bottom,
                              No_extensions,
                              false )),
                       Maybe_null None ))))));
    statement "mutable_blocks" "two mutable blocks, on the heap and local"
      [MT.mutable_block Heap; MT.mutable_block Local]
      (Answer (MT.mutable_block Heap_or_local));
    not_from_the_file "two mutable blocks, on the heap and on the heap or local"
      [MT.mutable_block Heap; MT.mutable_block Heap_or_local]
      (MT.mutable_block Heap_or_local);
    statement "fields" "blocks of one tag and one size"
      [block 0 [tagged (numbers [1; 2])]; block 0 [tagged (numbers [3; 4])]]
      (Answer (block 0 [tagged (numbers [1; 2; 3; 4])]));
    statement "same_fields" "blocks whose field is one variable"
      [block 0 [alias x]; block 0 [alias x]]
      (Answer (block 0 [alias x]));
    with_another_answer "fields_of_two_variables"
      "blocks whose fields are two variables of which nothing is known (a \
       variable is made, mentioned once: its type is in its place)"
      [block 0 [alias x]; block 0 [alias y]]
      (block 0 [MT.unknown Value]);
    not_from_the_file
      "blocks whose fields are two variables known to be numbers (the same)"
      ~knowing:[x, tagged (numbers [1; 2]); y, tagged (numbers [3; 4])]
      [block 0 [alias x]; block 0 [alias y]]
      (block 0 [tagged (numbers [1; 2; 3; 4])]);
    not_from_the_file
      "blocks with two fields that are two variables of which nothing is known \
       (one variable is made, mentioned twice)"
      [block 0 [alias x; alias x]; block 0 [alias y; alias y]]
      (block 0 [alias (own 1); alias (own 1)]);
    not_from_the_file
      "blocks with two fields that are two variables known to be numbers (the \
       same)"
      ~knowing:[x, tagged (numbers [1; 2]); y, tagged (numbers [3; 4])]
      [block 0 [alias x; alias x]; block 0 [alias y; alias y]]
      (block 0 [alias (own 1); alias (own 1)]);
    statement "two_sizes" "blocks of one tag and two sizes"
      [ block 0 [tagged (numbers [1; 2])];
        block 0 [tagged (numbers [3; 4]); MT.any_tagged_immediate] ]
      (Answer
         (MT.create_variant false
            (Known (MT.bottom naked_immediate))
            (Known
               (MT.row_like_for_blocks_create_at_least (z 0) (N.nat_of_int 1)
                  (Scannable Value_only)
                  [tagged (numbers [1; 2; 3; 4])]
                  Heap))
            No_extensions));
    statement "two_shapes"
      "blocks of one tag and two shapes (two values; a value and a naked float)"
      [ block 0 [MT.any_tagged_immediate; MT.any_tagged_immediate];
        MT.immutable_block false (z 0)
          (Scannable (Mixed_record (N.nat_of_int 1, [Kind_naked_float])))
          Heap
          [MT.any_tagged_immediate; MT.unknown naked_float] ]
      (Answer (MT.blocks_with_these_tags [z 0] Heap));
    statement "two_tags" "blocks of two tags (a variable is made for Get_tag)"
      [ block 0 [MT.any_tagged_immediate];
        block 1 [tagged (numbers [1; 2]); MT.any_tagged_immediate] ]
      (Answer
         (variant None
            (MT.bottom naked_immediate)
            (Some (own 1))
            [ 0, [MT.any_tagged_immediate];
              1, [tagged (numbers [1; 2]); MT.any_tagged_immediate] ]));
    statement "immediate_and_block"
      "an immediate and a block (a variable is made for Is_int)"
      [constant 0; block 0 [MT.any_tagged_immediate]]
      (Answer
         (variant
            (Some (own 1))
            (MT.this_naked_immediate (z 0))
            None
            [0, [MT.any_tagged_immediate]]));
    statement "variants" "two variants"
      [ variant None
          (MT.this_naked_immediate (z 0))
          None
          [ 0, [tagged (numbers [1; 2])];
            1, [tagged (numbers [3; 4]); MT.any_tagged_immediate] ];
        variant None
          (MT.these_naked_immediates (numbers [0; 1]))
          None
          [1, [tagged (numbers [5; 6]); MT.any_tagged_immediate]] ]
      (Answer
         (variant None
            (MT.these_naked_immediates (numbers [0; 1]))
            None
            [ 0, [tagged (numbers [1; 2])];
              1, [tagged (numbers [3; 4; 5; 6]); MT.any_tagged_immediate] ]));
    statement "closures" "two closures of one code"
      [ closure [code] (tagged (numbers [1; 2]));
        closure [code] (tagged (numbers [3; 4])) ]
      (Answer (closure [code] (tagged (numbers [3; 4; 1; 2]))));
    statement "closures_of_two_codes" "two closures of two codes"
      [ closure [code] (tagged (numbers [1; 2]));
        closure [other_code] (tagged (numbers [3; 4])) ]
      (Answer
         (MT.exactly_this_closure function_slot
            [function_slot, MT.Or_unknown.Unknown]
            []
            [value_slot, tagged (numbers [3; 4; 1; 2])]
            Heap));
    statement "closures_one_without_function_type"
      "a closure with a function type, and the closures of at least a value \
       slot"
      [ closure [code] (tagged (numbers [1; 2]));
        MT.at_least_this_closure function_slot [] []
          [value_slot, tagged (numbers [3; 4])]
          Heap ]
      (Answer
         (MT.at_least_this_closure function_slot [] []
            [value_slot, tagged (numbers [3; 4; 1; 2])]
            Heap));
    statement "alias_of_another_kind"
      "a tagged immediate and an alias of kind value to a naked immediate \
       (T5b-3)"
      [MT.any_tagged_immediate; alias_to_a_naked_immediate]
      Thought_to_stop;
    statement "closure_types_of_another_kind"
      "two closures whose closure types join to a type of another kind"
      [ MT.exactly_this_closure function_slot (function_types [code])
          [function_slot, alias_to_a_naked_immediate]
          [] Heap;
        MT.exactly_this_closure function_slot (function_types [code])
          [function_slot, MT.unknown Value]
          [] Heap ]
      Thought_to_stop ]

(* What the compiler does on the inputs of an example. *)
type the_compiler =
  | Answers of joined
  | Stops of string
  | Is_not_given of string  (** The inputs are not types of the compiler. *)
  | Is_not_read of string  (** The answer is not read: a failure of the test. *)

let run_examples_of_joins (names : names) =
  Format.printf
    "@.Examples of the join of types, written down from a transcription: the \
     n-way join of the compiler on the same types@.";
  let text t = print_with_own_variables names [t] in
  let examples = examples_of_joins names in
  let as_written = ref 0 in
  let as_written_with_variables = ref 0 in
  let stops_as_thought = ref 0 in
  let shown = ref 0 in
  let not_run = ref 0 in
  let different = ref 0 in
  List.iter
    (fun { example; source; knowing; inputs; answer } ->
      let example =
        match source with
        | Statement name -> Printf.sprintf "%s [%s]" example name
        | Statement_with_another_answer name ->
          Printf.sprintf "%s [the inputs of %s, another answer]" example name
        | Not_from_the_file -> Printf.sprintf "%s [not from the file]" example
      in
      (* What the compiler does: it answers, it stops, or the types are not the
         compiler's. *)
      let result =
        match
          ( List.map (to_compiler names) inputs,
            List.map
              (fun (variable, t) ->
                let variable =
                  Converter.variable_of_model names.numbering variable
                in
                Name.var variable, to_compiler names t)
              knowing )
        with
        | exception Converter.Not_in_the_compiler what -> Is_not_given what
        | types, known -> (
          let kind = MT.kind (List.hd inputs) in
          match
            or_fatal_error (fun () ->
                match join names n_way ~known:(fun _ -> known) kind types with
                | joined -> Answers joined
                | exception Assert_failure (file, _, _) ->
                  Stops ("an assertion of " ^ Filename.basename file ^ " fails")
                | exception Converter.Not_in_the_model what ->
                  Is_not_read ("the answer is not in the model: " ^ what)
                | exception Not_defined what ->
                  Is_not_read
                    (what
                   ^ " is in the answer and the environment does not define it"
                    ))
          with
          | Ok result -> result
          | Error line -> Stops ("a fatal error: " ^ general line))
      in
      match result, answer with
      | Is_not_read why, (Answer _ | Thought_to_stop | Nothing_to_compare _) ->
        incr different;
        Format.printf "  %s: DIFFERENT. %s@." example why
      | Is_not_given what, (Answer _ | Thought_to_stop | Nothing_to_compare _)
        ->
        incr not_run;
        Format.printf "  %s: not run, not in the compiler: %s@." example what
      | Stops why, Thought_to_stop ->
        incr stops_as_thought;
        Format.printf
          "  %s: the compiler stops, where the transcription has no answer: \
           %s@."
          example why
      | Stops why, (Answer _ | Nothing_to_compare _) ->
        incr different;
        Format.printf "  %s: DIFFERENT. The compiler stops: %s@." example why
      | Answers joined, Thought_to_stop ->
        incr different;
        Format.printf
          "  @[<v>%s: DIFFERENT. The compiler was thought to stop, and \
           answers:@ %s@]@."
          example
          (print_joined names joined)
      | Answers joined, Nothing_to_compare why ->
        incr shown;
        Format.printf
          "  @[<v>%s: not compared; the compiler answers@ %s@ (%s)@]@." example
          (print_joined names joined)
          why
      | Answers joined, Answer answer ->
        if
          Model_type.same joined.joined answer
          && match joined.own with [] -> true | _ :: _ -> false
        then (
          incr as_written;
          Format.printf "  %s: as written down@." example)
        else if same_text (text joined.joined) (text answer)
        then (
          incr as_written_with_variables;
          Format.printf
            "  @[<v>%s: as written down, with the compiler's variables:@ %s@]@."
            example
            (print_joined names joined))
        else (
          incr different;
          Format.printf
            "  @[<v>%s: DIFFERENT. Written down:@ %s@ the compiler answers:@ \
             %s@]@."
            example (text answer)
            (print_joined names joined)))
    examples;
  Format.printf
    "  Of %d: %d as written down, and %d more with the compiler's variables \
     for those written down; %d where the compiler stops and the transcription \
     has no answer; %d not compared; %d not run; %d different@."
    (List.length examples) !as_written !as_written_with_variables
    !stops_as_thought !shown !not_run !different

(* ======================================================================== *)
(* Examples of the meet                                                     *)
(* ======================================================================== *)

(* Meets whose answers were written down from a transcription of the meet into
   the model, without running the compiler: scenarios made by hand from the
   calls of the types library that Simplify makes for a match on a variant, a
   match on the tag of a block, a match on a value that may be null, two loads
   from a pair, the boxing and unboxing of a float, and two projections of value
   slots (FlambdaMeetMatchExamplesSpec.v, FlambdaMeetTagExamplesSpec.v,
   FlambdaMeetProjectionExamplesSpec.v and three statements of
   FlambdaMeetExamplesSpec.v, in middle_end/flambda2/types/rocq/). Each is run
   here, with each of the two meets of the compiler: the environment is built by
   the same calls, the meet is called on the two types of the statement, and
   what is compared with the statement is whether the meet is bottom, the type
   answered, the type that the environment answered has for the variables that
   the statement names ([Typing_env.find]), and their canonical elements.

   An example is named as its statement is, without [_statement]. The statements
   are about two meets of the model, the one that transcribes the compiler's and
   one that is to be proved, which answer alike but at one step: the two
   examples that are marked say what the statement says of the first. Where the
   meet of the model calls a join, the statement is with a join that forgets;
   what is compared here is what such a statement says of the type answered and
   of the variables.

   The variables of a scenario are numbered from 1 in the order given, as in the
   statements, and so are its two function slots and its two value slots; the
   shapes are made by the model's creation functions and converted. The
   relations of [Is_int], [Get_tag] and [Is_null] are added with the functions
   of the library that Simplify calls ([Flambda2_types.Typing_env]), which are
   of the interface that the library exports and take the meet from the flag of
   the compiler: the environment is built through that interface as far as the
   last relation, and read through the observer of typing environments from
   there.

   A difference does not fail the test: it is shown, for the owner of the
   transcription to say which side is wrong. *)
type step =
  | Define of int  (** The variable of that number is defined. *)
  | Relation of
      { relation : MT.Relation.t;
        result : int;
        scrutinee : int
      }
  | Equation of int * MT.flambda_type
  | Meet_of of MT.flambda_type * MT.flambda_type
      (** The environment that the meet answers is the one to go on in. *)

type stated =
  | Is_bottom
  | Answers_type of MT.flambda_type

type example_of_meet =
  { statement : string;
    (* The kinds of the variables 1, 2, ... *)
    variables : MK.flambda_kind list;
    steps : step list;
    (* The meet that the statement is about, in the environment of the steps;
       [None] where the statement is about the steps alone. *)
    meet : (MT.flambda_type * MT.flambda_type * stated) option;
    (* What the statement says of the environment answered. *)
    finds : (int * MK.flambda_kind * MT.flambda_type) list;
    canonicals : (int * M.simple) list
  }

let examples_of_meets : example_of_meet list =
  let v = N.positive_of_int in
  let z = N.z_of_int in
  let naked_immediate : MK.flambda_kind = Naked_number Kind_naked_immediate in
  let naked_float : MK.flambda_kind = Naked_number Kind_naked_float in
  let alias kind i = MT.alias_type_of kind (Var (v i)) in
  let number i = MT.this_naked_immediate (z i) in
  let constant i : M.simple = Const (Naked_immediate (z i)) in
  let no_blocks = MT.Or_unknown.Known MT.row_like_for_blocks_bottom in
  let no_immediates = MT.Or_unknown.Known (MT.bottom naked_immediate) in
  (* The blocks of tag 0 that have at least the fields given. *)
  let blocks fields : MT.row_like_for_blocks MT.Or_unknown.t =
    Known
      (Row_like_for_blocks
         ( [ ( z 0,
               Known
                 { case_maps_to = fields;
                   case_index =
                     { index_domain =
                         At_least (N.nat_of_int (List.length fields));
                       index_shape = Scannable Value_only
                     };
                   case_env_extension = MT.empty_env_extension
                 } ) ],
           Bottom,
           Heap_or_local ))
  in
  (* The blocks of tag 0, of which nothing more is known. *)
  let blocks_of_tag_0 : MT.row_like_for_blocks MT.Or_unknown.t =
    Known (Row_like_for_blocks ([z 0, Unknown], Bottom, Heap_or_local))
  in
  let value non_null is_null : MT.flambda_type =
    Type_value (Ok (No_alias (Head_of_kind_value (non_null, is_null))))
  in
  let variant ?is_int ?get_tag immediates blocks : MT.flambda_type =
    value
      (Ok (Variant (is_int, immediates, get_tag, blocks, No_extensions, false)))
      Not_null
  in
  (* The shape of a load of the field at [n - 1] of a block of tag 0 into a
     variable. *)
  let load_shape n result =
    match
      MT.immutable_block_with_size_at_least
        (Known (z 0))
        (N.nat_of_int n) (Scannable Value_only) (v result)
    with
    | Some shape -> shape
    | None -> MT.bottom Value
  in
  let example statement variables steps ?meet ?(finds = []) ?(canonicals = [])
      () =
    { statement; variables; steps; meet; finds; canonicals }
  in
  (* A scrutinee (1) and the result of a relation to it (2). *)
  let related relation =
    [Define 1; Define 2; Relation { relation; result = 2; scrutinee = 1 }]
  in
  let result = alias naked_immediate 2 in
  let x = alias Value 1 in
  (* The match: the parameter (1), the result of [Is_int] (2), the result of
     [Untag_immediate] (3) and the result of the load (4). *)
  let of_the_match = [MK.Value; naked_immediate; naked_immediate; MK.Value] in
  let match_variant = variant ~is_int:(v 2) in
  let start = related Is_int in
  let untagged = alias naked_immediate 3 in
  let in_the_immediates = start @ [Meet_of (result, number 1)] in
  let in_the_blocks = start @ [Meet_of (result, number 0)] in
  let untag = MT.tagged_immediate_alias_to (v 3) in
  let after_untag = in_the_immediates @ [Define 3; Meet_of (x, untag)] in
  let x_untagged = match_variant (Known untagged) no_blocks in
  (* The tag: the parameter (1), the result of [Get_tag] (2) and the result of
     the load (3). *)
  let of_the_tag = [MK.Value; naked_immediate; MK.Value] in
  let tags_variant = variant ~get_tag:(v 2) in
  (* Null: the parameter (1) and the result of [Is_null] (2). *)
  let of_null = [MK.Value; naked_immediate] in
  let maybe_null : MT.is_null = Maybe_null (Some (v 2)) in
  (* The pair: the parameter (1) and the results of the two loads (2, 3). *)
  let of_the_pair = [MK.Value; MK.Value; MK.Value] in
  let pair fields = variant no_immediates (blocks fields) in
  (* The float: the sum (1), its box (2), the result of the unboxing (3). *)
  let of_the_float = [naked_float; MK.Value; naked_float] in
  let box_type = MT.box_number Boxable_naked_float (alias naked_float 1) Heap in
  let boxed = [Define 1; Define 2; Equation (2, box_type)] in
  (* The closure (1) and the results of the two projections (2, 3). *)
  let of_the_closure = [MK.Value; MK.Value; MK.Value] in
  let slot_shape value_slot result =
    MT.closure_with_at_least_this_value_slot (v 1) (v value_slot) (v result)
      Value
  in
  (* A closure at the first function slot of a set that has at least the two, in
     which the closure at the second is a number. *)
  let closures_type n =
    MT.at_least_this_closure (v 1)
      [v 1, Unknown; v 2, Unknown]
      [v 2, MT.this_tagged_immediate (z n)]
      [] Heap
  in
  [ example "match_is_int" of_the_match start
      ~finds:
        [ 2, naked_immediate, MT.is_int_for_scrutinee (Name_var (v 1));
          1, Value, match_variant Unknown Unknown ]
      ();
    example "match_arm_immediate" of_the_match start
      ~meet:(result, number 1, Answers_type result)
      ~canonicals:[2, constant 1]
      ~finds:[1, Value, match_variant Unknown no_blocks]
      ();
    example "match_arm_block" of_the_match start
      ~meet:(result, number 0, Answers_type result)
      ~canonicals:[2, constant 0]
      ~finds:[1, Value, match_variant no_immediates Unknown]
      ();
    example "match_no_other_arm" of_the_match start
      ~meet:(result, number 2, Is_bottom)
      ();
    example "match_untag" of_the_match
      (in_the_immediates @ [Define 3])
      ~meet:(x, untag, Answers_type x)
      ~finds:
        [1, Value, x_untagged; 3, naked_immediate, MT.unknown naked_immediate]
      ();
    example "match_arm_constructor" of_the_match after_untag
      ~meet:(untagged, number 0, Answers_type untagged)
      ~canonicals:[3, constant 0]
      ~finds:[1, Value, x_untagged]
      ();
    example "match_inner_arm" of_the_match
      (after_untag @ [Meet_of (untagged, number 0)])
      ~meet:(untagged, number 1, Is_bottom)
      ();
    example "match_load" of_the_match
      (in_the_blocks @ [Define 4])
      ~meet:(x, load_shape 1 4, Answers_type x)
      ~finds:
        [ 1, Value, match_variant no_immediates (blocks [alias Value 4]);
          4, Value, MT.unknown Value ]
      ();
    example "match_load_of_immediate" of_the_match
      (in_the_immediates @ [Define 4])
      ~meet:(x, load_shape 1 4, Is_bottom)
      ();
    example "example_get_tag_env_made" of_the_tag (related Get_tag)
      ~finds:
        [ 2, naked_immediate, MT.get_tag_for_block (Name_var (v 1));
          1, Value, tags_variant Unknown Unknown ]
      ();
    example "tags_arm, of the meet that transcribes the compiler's" of_the_tag
      (related Get_tag)
      ~meet:(result, number 0, Answers_type result)
      ~finds:[1, Value, tags_variant no_immediates blocks_of_tag_0]
      ();
    example "tags_load, of the meet that transcribes the compiler's" of_the_tag
      (related Get_tag @ [Meet_of (result, number 0); Define 3])
      ~meet:(x, load_shape 1 3, Answers_type x)
      ~finds:[1, Value, tags_variant no_immediates (blocks [alias Value 3])]
      ();
    example "null_relation" of_null (related Is_null)
      ~finds:
        [ 2, naked_immediate, MT.is_null_for_scrutinee (Name_var (v 1));
          1, Value, value Unknown maybe_null ]
      ();
    example "null_arm_null" of_null (related Is_null)
      ~meet:(result, number 1, Answers_type result)
      ~canonicals:[2, constant 1]
      ~finds:[1, Value, value Bottom maybe_null]
      ();
    example "null_arm_value" of_null (related Is_null)
      ~meet:(result, number 0, Answers_type result)
      ~canonicals:[2, constant 0]
      ~finds:[1, Value, MT.any_non_null_value]
      ();
    example "meet_through_poison" [MK.Value]
      [Define 1; Equation (1, MT.null)]
      ~meet:(x, MT.any_non_null_value, Is_bottom)
      ();
    example "meet_closures_invalid_statics" [] []
      ~meet:(closures_type 0, closures_type 1, Is_bottom)
      ();
    example "pair_first_load" of_the_pair [Define 1; Define 2]
      ~meet:(x, load_shape 1 2, Answers_type x)
      ~finds:[1, Value, pair [alias Value 2]]
      ();
    example "pair_second_load" of_the_pair
      [Define 1; Define 2; Meet_of (x, load_shape 1 2); Define 3]
      ~meet:(x, load_shape 2 3, Answers_type x)
      ~finds:[1, Value, pair [alias Value 2; alias Value 3]]
      ();
    example "float_boxed" of_the_float boxed ~finds:[2, Value, box_type] ();
    example "float_unboxed" of_the_float (boxed @ [Define 3])
      ~meet:
        ( alias Value 2,
          MT.boxed_number_alias_to Boxable_naked_float (v 3) Heap_or_local,
          Answers_type (alias Value 2) )
      ~canonicals:[3, Var (v 1)]
      ~finds:[2, Value, box_type]
      ();
    example "closure_first_slot" of_the_closure [Define 1; Define 2]
      ~meet:(x, slot_shape 1 2, Answers_type x)
      ~finds:[1, Value, slot_shape 1 2]
      ();
    example "closure_second_slot" of_the_closure
      [Define 1; Define 2; Meet_of (x, slot_shape 1 2); Define 3]
      ~meet:(x, slot_shape 2 3, Answers_type x)
      ~finds:
        [ ( 1,
            Value,
            MT.closure_with_at_least_these_value_slots (v 1)
              [v 2, (v 3, Value); v 1, (v 2, Value)] ) ]
      () ]

(* The names of a scenario, and the environment that its steps make with one of
   the two meets. *)
type scenario =
  { numbering : Model_names.t;
    variable : int -> Variable.t;
    after_the_steps : (TE.t, string) result
  }

let scenario (implementation : implementation) (kinds : MK.flambda_kind list)
    (steps : step list) : scenario =
  let numbering = Model_names.create () in
  let unit = Current_unit.get_cu_exn () in
  let variables =
    List.map
      (fun kind ->
        let variable = Variable.create "v" (Converter.kind_of_model kind) in
        ignore (numbering.variables.number variable : N.positive);
        variable)
      kinds
  in
  List.iter
    (fun name ->
      ignore
        (numbering.function_slots.number
           (Function_slot.create unit ~name ~size:2)
          : N.positive))
    ["f"; "g"];
  List.iter
    (fun name ->
      ignore
        (numbering.value_slots.number
           (Value_slot.create unit ~name ~is_always_immediate:false K.value)
          : N.positive))
    ["a"; "b"];
  let variable i = List.nth variables (i - 1) in
  let bound i =
    Bound_name.create_var
      (Bound_var.create (variable i) Flambda_debug_uid.none Name_mode.normal)
  in
  let to_compiler = Converter.type_of_model numbering machine_width in
  let meet_expanded_head = implementation.meet_expanded_head in
  (* The steps as far as the last relation, through the interface that the
     library exports, with the meet of the implementation chosen by the flag
     that the library reads. *)
  let module Exported = Flambda2_types.Typing_env in
  let rec exported env steps =
    match steps with
    | Define i :: steps ->
      exported
        (Exported.add_definition env (bound i) (Variable.kind (variable i)))
        steps
    | Relation { relation; result; scrutinee } :: steps ->
      let add =
        match relation with
        | Is_int -> Exported.add_is_int_relation
        | Get_tag -> Exported.add_get_tag_relation
        | Is_null -> Exported.add_is_null_relation
      in
      exported
        (add env
           (Name.var (variable result))
           ~scrutinee:(Simple.var (variable scrutinee)))
        steps
    | (Equation _ | Meet_of _) :: _ | [] -> env, steps
  in
  let algorithm : Oxcaml_flags.join_algorithm =
    if String.equal implementation.implementation n_way.implementation
    then N_way
    else Binary
  in
  let before = !Oxcaml_flags.Flambda2.join_algorithm in
  Oxcaml_flags.Flambda2.join_algorithm := Oxcaml_flags.Set algorithm;
  let env, steps =
    Fun.protect
      ~finally:(fun () -> Oxcaml_flags.Flambda2.join_algorithm := before)
      (fun () ->
        exported
          (Exported.create ~machine_width ~resolver:(fun _ -> None))
          steps)
  in
  (* The same environment, as the modules of the library have it. *)
  let observed = ref None in
  TE.For_testing.set_observer
    (Some (fun env (_ : Continuation.t) -> observed := Some env));
  Exported.notify_test_observer env ~at_handler:(Continuation.create ());
  TE.For_testing.set_observer None;
  let env = match !observed with Some env -> env | None -> assert false in
  let rec go env steps : (TE.t, string) result =
    match steps with
    | [] -> Ok env
    | Define i :: steps ->
      go (TE.add_definition env (bound i) (Variable.kind (variable i))) steps
    | Equation (i, t) :: steps ->
      go
        (ME.use_meet_env ~meet_expanded_head env ~f:(fun env ->
             ME.add_equation env
               (Name.var (variable i))
               (to_compiler t) ~meet_expanded_head))
        steps
    | Meet_of (t1, t2) :: steps -> (
      match implementation.meet env (to_compiler t1) (to_compiler t2) with
      | Bottom -> Error "a meet on the way to the environment is bottom"
      | Ok ((_ : TG.t), env) -> go env steps)
    | Relation _ :: _ ->
      Error "a relation after a step that is not a definition"
  in
  { numbering; variable; after_the_steps = go env steps }

(* What differs from the statement when an example is run with one of the two
   meets; nothing if the list is empty. *)
let run_example_of_meet (implementation : implementation)
    (example : example_of_meet) : string list =
  let { numbering; variable; after_the_steps } =
    scenario implementation example.variables example.steps
  in
  let to_compiler = Converter.type_of_model numbering machine_width in
  let to_model = Converter.type_to_model numbering in
  let differences = ref [] in
  let differs fmt =
    Format.kasprintf (fun what -> differences := what :: !differences) fmt
  in
  let print ppf t = Model_type.print ppf (Model_type.normalise t) in
  let check env =
    List.iter
      (fun (i, kind, stated) ->
        let found =
          to_model
            (TE.find env
               (Name.var (variable i))
               (Some (Converter.kind_of_model kind)))
        in
        if not (Model_type.same found stated)
        then
          differs "@[<v>the type of v%d is@ %a@ and is stated to be@ %a@]" i
            print found print stated)
      example.finds;
    List.iter
      (fun (i, stated) ->
        match
          TE.get_canonical_simple_exn env ~min_name_mode:Name_mode.in_types
            (Simple.var (variable i))
        with
        | canonical ->
          let found = Converter.simple_to_model numbering canonical in
          if not (Stdlib.( = ) found stated)
          then
            differs "the canonical element of v%d is %a and is stated to be %a"
              i Model_type.print_simple found Model_type.print_simple stated
        | exception Not_found -> differs "v%d has no canonical element" i)
      example.canonicals
  in
  (match after_the_steps with
  | Error why -> differs "%s" why
  | Ok env -> (
    match example.meet with
    | None -> check env
    | Some (t1, t2, stated) -> (
      match
        implementation.meet env (to_compiler t1) (to_compiler t2), stated
      with
      | Bottom, Is_bottom -> ()
      | Bottom, Answers_type _ -> differs "the meet is bottom"
      | Ok (t, (_ : TE.t)), Is_bottom ->
        differs "@[<v>the meet is stated to be bottom, and answers@ %a@]" print
          (to_model t)
      | Ok (t, env), Answers_type stated ->
        let answered = to_model t in
        if not (Model_type.same answered stated)
        then
          differs "@[<v>the meet answers@ %a@ and is stated to answer@ %a@]"
            print answered print stated;
        check env)));
  List.rev !differences

(* What running an example with one of the two meets comes to. *)
type run_of_meet =
  | As_stated
  | Differs of string list
  | Stops_at of string
  | Is_not_run of string

let run_examples_of_meets () =
  Format.printf
    "@.Examples of the meet, written down from a transcription: the two meets \
     of the compiler on the same calls@.";
  let as_stated = ref 0 and different = ref 0 and not_run = ref 0 in
  let implementations = [binary; n_way] in
  List.iter
    (fun (example : example_of_meet) ->
      let runs =
        List.map
          (fun (implementation : implementation) ->
            let run =
              match
                or_fatal_error (fun () ->
                    match run_example_of_meet implementation example with
                    | [] -> As_stated
                    | _ :: _ as differences -> Differs differences
                    | exception Assert_failure (file, _, _) ->
                      Stops_at
                        ("an assertion of " ^ Filename.basename file ^ " fails")
                    | exception Converter.Not_in_the_compiler what ->
                      Is_not_run ("not in the compiler: " ^ what)
                    | exception Converter.Not_in_the_model what ->
                      Differs ["an answer is not in the model: " ^ what])
              with
              | Ok run -> run
              | Error line -> Stops_at ("a fatal error: " ^ general line)
            in
            (match run with
            | As_stated -> incr as_stated
            | Differs _ | Stops_at _ -> incr different
            | Is_not_run _ -> incr not_run);
            implementation.implementation, run)
          implementations
      in
      if
        List.for_all
          (fun (_, run) ->
            match run with
            | As_stated -> true
            | Differs _ | Stops_at _ | Is_not_run _ -> false)
          runs
      then
        Format.printf "  %s: as stated, with each of the two meets@."
          example.statement
      else
        List.iter
          (fun (implementation, run) ->
            let name =
              Printf.sprintf "%s (%s)" example.statement implementation
            in
            match run with
            | As_stated -> Format.printf "  %s: as stated@." name
            | Differs differences ->
              Format.printf "  @[<v>%s: DIFFERENT.%a@]@." name
                (fun ppf ->
                  List.iter (fun what ->
                      Format.fprintf ppf "@ %a" print_lines what))
                differences
            | Stops_at why ->
              Format.printf "  %s: DIFFERENT. The compiler stops: %s@." name why
            | Is_not_run why -> Format.printf "  %s: not run, %s@." name why)
          runs)
    examples_of_meets;
  Format.printf
    "  Of %d statements, each with the two meets: %d runs as stated, %d \
     different, %d not run@."
    (List.length examples_of_meets)
    !as_stated !different !not_run

(* ======================================================================== *)
(* Chosen meets                                                             *)
(* ======================================================================== *)

(* Two meets of types written by hand, each in an environment made as those of
   the examples above are, which answer what the meets of generated types above
   were not seen to answer. What each of the two meets of the compiler does is
   shown; nothing is compared, and the expected output is the record.

   - T7-2. The variable 1 is a value, the variable 3 is the tagging of the
   variable 2, and the variable 2 is [Get_tag] of the variable 1. The types met
   are the blocks of tag 0 or 1 whose one field is the variable 3, and the
   blocks of tag 0 whose field is the number 0 or of tag 1 whose field is the
   number 1. Neither has an extension. In each case of the answer the field is a
   number, so the variable 2 is, and the variable 1 is a block of that tag: the
   extension of the case says so. Given to the variable 1, the answer is then a
   type of a name that has an extension on that name, on which the compiler's
   [Equal_types_for_debug.equal_type] does not end; that function is not called
   here. - T4-9. The three variables are values of which nothing is known. The
   types met are blocks of one field: a variant whose blocks, of tag 0 or 1,
   have for their field the variable 1; and a variant whose blocks have for
   their field a pair, of the variable 2 twice for tag 0 and of the variable 3
   twice for tag 1. The answer of the n-way meet mentions a variable that the
   environment answered with it does not define. *)
type chosen_meet =
  { label : string;
    kinds : MK.flambda_kind list;
    before : step list;
    met : MT.flambda_type * MT.flambda_type;
    (* The variable that is then given the answer, by an equation, and whose
       type is read. *)
    given_to : int option
  }

let the_chosen_meets : chosen_meet list =
  let v = N.positive_of_int in
  let z = N.z_of_int in
  let naked_immediate : MK.flambda_kind = Naked_number Kind_naked_immediate in
  let alias i = MT.alias_type_of Value (Var (v i)) in
  let variant immediates cases : MT.flambda_type =
    Type_value
      (Ok
         (No_alias
            (Head_of_kind_value
               ( Ok
                   (Variant
                      ( None,
                        immediates,
                        None,
                        Known
                          (Row_like_for_blocks
                             ( List.map
                                 (fun (tag, fields) :
                                      (_
                                      * MT.row_like_block_case MT.Or_unknown.t)
                                    ->
                                   ( z tag,
                                     Known
                                       { case_maps_to = fields;
                                         case_index =
                                           { index_domain =
                                               Known
                                                 (N.nat_of_int
                                                    (List.length fields));
                                             index_shape = Scannable Value_only
                                           };
                                         case_env_extension =
                                           MT.empty_env_extension
                                       } ))
                                 cases,
                               Bottom,
                               Heap )),
                        No_extensions,
                        false )),
                 Not_null ))))
  in
  let blocks = variant (Known (MT.bottom naked_immediate)) in
  let immediates_or_blocks = variant Unknown in
  let number i = MT.this_tagged_immediate (z i) in
  [ { label = "T7-2";
      kinds = [Value; naked_immediate; Value];
      before =
        [ Define 1;
          Define 2;
          Define 3;
          Equation (3, MT.tagged_immediate_alias_to (v 2));
          Equation (2, MT.get_tag_for_block (Name_var (v 1))) ];
      met =
        ( blocks [0, [alias 3]; 1, [alias 3]],
          blocks [0, [number 0]; 1, [number 1]] );
      given_to = Some 1
    };
    { label = "T4-9";
      kinds = [Value; Value; Value];
      before = [Define 1; Define 2; Define 3];
      met =
        ( blocks [0, [immediates_or_blocks [0, [alias 1]; 1, [alias 1]]]],
          blocks
            [ ( 0,
                [ immediates_or_blocks
                    [ 0, [blocks [0, [alias 2; alias 2]]];
                      1, [blocks [0, [alias 3; alias 3]]] ] ] ) ] );
      given_to = None
    } ]

(* Whether a type has, in an extension, an equation on a name. *)
let rec has_an_extension_on (name : MT.name) (t : MT.flambda_type) : bool =
  let in_extension (Env_extension equations : MT.env_extension) =
    List.exists
      (fun (name', t) -> MT.name_eqb name name' || has_an_extension_on name t)
      equations
  in
  let in_block_case (case : MT.row_like_block_case) =
    in_extension case.case_env_extension
    || List.exists (has_an_extension_on name) case.case_maps_to
  in
  match t with
  | Type_value (Ok (No_alias (Head_of_kind_value (Ok head, _)))) -> (
    match head with
    | Variant (_, immediates, _, blocks, extensions, _) -> (
      (match immediates with
        | Known t -> has_an_extension_on name t
        | Unknown -> false)
      || (match blocks with
        | Known (Row_like_for_blocks (known, other, _)) -> (
          List.exists
            (fun ((_ : N.z), (case : _ MT.Or_unknown.t)) ->
              match case with
              | Known case -> in_block_case case
              | Unknown -> false)
            known
          || match other with Ok case -> in_block_case case | Bottom -> false)
        | Unknown -> false)
      ||
      match extensions with
      | No_extensions -> false
      | Ext (when_immediate, when_block) ->
        in_extension when_immediate || in_extension when_block)
    | Boxed_number (_, contents, _) -> has_an_extension_on name contents
    | Closures (Row_like_for_closures known, _) ->
      let in_case (case : MT.row_like_closures_case) =
        in_extension case.case_env_extension
        ||
        let (Closures_entry (_, closure_types, value_slot_types)) =
          case.case_maps_to
        in
        List.exists
          (fun ((_ : N.positive), t) -> has_an_extension_on name t)
          (closure_types @ value_slot_types)
      in
      List.exists (fun ((_ : N.positive), case) -> in_case case) known
    | Mutable_block _ | String _ -> false)
  | Type_value
      ( Unknown | Bottom
      | Ok (Equals _)
      | Ok (No_alias (Head_of_kind_value ((Unknown | Bottom), _))) )
  | Type_naked_immediate _ | Type_naked_number _ | Type_rec_info _
  | Type_region _ ->
    false

let chosen_meets () =
  Format.printf "@.Chosen meets@.";
  List.iter
    (fun { label; kinds; before; met = first, second; given_to } ->
      List.iter
        (fun (implementation : implementation) ->
          let name =
            Printf.sprintf "%s (%s)" label implementation.implementation
          in
          let observed =
            or_fatal_error (fun () ->
                let { numbering; variable; after_the_steps } =
                  scenario implementation kinds before
                in
                let to_compiler =
                  Converter.type_of_model numbering machine_width
                in
                let to_model = Converter.type_to_model numbering in
                let print_names ppf names =
                  Format.pp_print_list
                    ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
                    Model_type.print_name ppf names
                in
                match after_the_steps with
                | Error why -> ["not run: " ^ why]
                | Ok env -> (
                  match
                    implementation.meet env (to_compiler first)
                      (to_compiler second)
                  with
                  | Bottom -> ["the meet is bottom"]
                  | Ok (t, env) ->
                    let not_defined =
                      Name_occurrences.fold_names (TG.free_names t) ~init:[]
                        ~f:(fun not_defined name ->
                          if TE.mem env name
                          then not_defined
                          else
                            Converter.name_to_model numbering name
                            :: not_defined)
                    in
                    let answered = to_model t in
                    let name_of i : MT.name =
                      Name_var (numbering.variables.number (variable i))
                    in
                    let with_equations =
                      List.filter
                        (fun name -> has_an_extension_on name answered)
                        (List.mapi (fun i _ -> name_of (i + 1)) kinds)
                    in
                    let given =
                      match given_to with
                      | None -> []
                      | Some i ->
                        let x = variable i in
                        let meet_expanded_head =
                          implementation.meet_expanded_head
                        in
                        let env =
                          ME.use_meet_env ~meet_expanded_head env ~f:(fun env ->
                              ME.add_equation env (Name.var x) t
                                ~meet_expanded_head)
                        in
                        let of_x =
                          to_model
                            (TE.find env (Name.var x) (Some (Variable.kind x)))
                        in
                        [ Format.asprintf
                            "given the answer by an equation, %a has a type \
                             that has %s extension with an equation on %a"
                            Model_type.print_name (name_of i)
                            (if has_an_extension_on (name_of i) of_x
                             then "an"
                             else "no")
                            Model_type.print_name (name_of i) ]
                    in
                    [ (match with_equations with
                      | [] ->
                        "no extension of the answer has an equation on a \
                         variable of the environment"
                      | _ :: _ ->
                        Format.asprintf
                          "extensions of the answer have equations on %a"
                          print_names with_equations);
                      (match not_defined with
                      | [] ->
                        "the environment answered defines every name of the \
                         answer"
                      | _ :: _ ->
                        Format.asprintf
                          "the answer mentions %a, which the environment \
                           answered does not define"
                          print_names (List.rev not_defined));
                      Printf.sprintf "type_well_formed is %b of the answer"
                        (is_well_formed answered) ]
                    @ given))
          in
          match observed with
          | Ok observed ->
            Format.printf "  @[<v>%s:%a@]@." name
              (fun ppf ->
                List.iter (fun what -> Format.fprintf ppf "@ %s" what))
              observed
          | Error line ->
            Format.printf "  %s: the compiler stops: %s@." name (general line))
        [binary; n_way])
    the_chosen_meets

(* ======================================================================== *)
(* The comparison by text                                                   *)
(* ======================================================================== *)

(* An environment in which a variable of the tests is a block whose field is a
   variable that is not of the tests, which is one of two numbers, and in which
   the parameter is that variable of the tests. What the environment says of the
   variable that is not of the tests is reached from the type of the name only.
   Two such environments that differ in the numbers print differently when the
   names are among the roots, as for the shared parts; from the parameter alone
   they print alike, which is the limit of the comparisons of two joins that
   print the parameter only. *)
let reached_by_a_name_only (names : names) : (string * bool) list =
  let x =
    Converter.variable_of_model names.numbering
      (List.hd names.pool.value_variables)
  in
  let parameter = parameter names Value in
  let environment numbers =
    let e = Variable.create "e" K.value in
    let define env variable =
      TE.add_definition env
        (Bound_name.create_var
           (Bound_var.create variable Flambda_debug_uid.none Name_mode.normal))
        K.value
    in
    let meet_expanded_head = n_way.meet_expanded_head in
    let block_of_e =
      MTC.immutable_block ~machine_width ~is_unique:false
        (Converter.tag_of_model machine_width (N.z_of_int 0))
        ~shape:(Converter.block_shape_of_model (Scannable Value_only))
        (Converter.alloc_mode_of_model Heap)
        ~fields:[TG.alias_type_of K.value (Simple.var e)]
    in
    ME.use_meet_env ~meet_expanded_head
      (define (define names.env parameter) e)
      ~f:(fun env ->
        List.fold_left
          (fun env (variable, t) ->
            ME.add_equation env (Name.var variable) t ~meet_expanded_head)
          env
          [ ( e,
              to_compiler names
                (MT.these_tagged_immediates (List.map N.z_of_int numbers)) );
            x, block_of_e;
            parameter, TG.alias_type_of K.value (Simple.var x) ])
  in
  let with_names numbers =
    print_joined_with_names names (environment numbers) parameter
  in
  let parameter_only numbers =
    print_joined names (joined_of_env names (environment numbers) parameter)
  in
  [ ( "a variable that only a name of the tests reaches, of two numbers and of \
       two others, printed with the names",
      not (same_text (with_names [0; 1]) (with_names [2; 3])) );
    ( "the same, printed from the parameter alone (one text)",
      same_text (parameter_only [0; 1]) (parameter_only [2; 3]) ) ]

(* Where two answers of the compiler are compared as text, the variables that
   are not of the tests are renamed over the whole text. So two types that are
   aliases of one such variable print as two types that are aliases of another
   one do, and not as aliases of two different ones do: a renaming of each type
   on its own would print all three alike. *)
let comparison_by_text (names : names) =
  let own i = N.positive_of_int (names.variables_with_a_name + i) in
  let alias i = MT.alias_type_of Value (Var (own i)) in
  let text = print_with_own_variables names in
  let cases =
    [ ( "two aliases of one variable, and of another one",
        same_text (text [alias 1; alias 1]) (text [alias 2; alias 2]) );
      ( "two aliases of one variable, and aliases of two",
        let of_one = text [alias 1; alias 1] in
        let of_two = text [alias 2; alias 3] in
        not (same_text of_one of_two) );
      ( "what a join says of one variable of its own, and of two",
        not
          (same_text
             (print_joined names
                { joined = alias 1; own = [own 1, alias 1]; own_in_terms = [] })
             (print_joined names
                { joined = alias 2;
                  own = [own 2, alias 3; own 3, alias 3];
                  own_in_terms = []
                })) );
      ( "a type with a variable of its own, and with one whose number is \
         longer, so that the lines are broken elsewhere",
        let variant i =
          MT.create_variant false
            (Known (MT.this_naked_immediate (N.z_of_int 0)))
            (Known
               (MT.row_like_for_blocks_create_at_least (N.z_of_int 0)
                  (N.nat_of_int 1) (Scannable Value_only)
                  [alias i]
                  Heap))
            No_extensions
        in
        same_text (text [variant 1]) (text [variant 100000]) ) ]
    @ reached_by_a_name_only names
  in
  let wrong = List.filter (fun (_, as_expected) -> not as_expected) cases in
  Format.printf "@.The comparison by text (%d cases): %d as expected@."
    (List.length cases)
    (List.length cases - List.length wrong);
  List.iter (fun (what, _) -> Format.printf "  WRONG: %s@." what) wrong;
  failures := !failures + List.length wrong

(* ======================================================================== *)
(* What the model has not got of [Rec_info]                                 *)
(* ======================================================================== *)

(* The comparisons of one type leave out what the converter drops of [Rec_info]
   (the [rec_info] of a function type, the expression of a [Rec_info] head), and
   nothing else. These are cases made by hand, each with the outcome that a
   comparison is to have on it: - an alias to a variable of kind [Rec_info],
   which the model has, against a type of the model without it: the free
   variables differ, and that is a disagreement; - a function type whose
   [rec_info] mentions a variable: the free variables are not compared as they
   are, they agree once the variables of what was dropped are added, and the
   type comes back the same with the [rec_info] put back; - a [Rec_info] head,
   the successor of a variable: the same for the free variables, and the type
   does not come back; - two closures that differ in the last byte of a long
   string and in the [rec_info]: with the [rec_info] of the first put into the
   second, the compiler's two equalities tell the two apart, though they are
   printed alike (the printer of the compiler shows the start of a long string);
   - a type in which one code id has a [rec_info] in one function type and the
   unknown one in another: the [rec_info]s cannot be put back by code id, and
   the type is not compared. *)
let rec_info_cases (names : names) =
  let numbering = names.numbering in
  let depth_of_model = List.hd names.pool.rec_info_variables in
  let depth = Converter.variable_of_model numbering depth_of_model in
  let slot_of_model = List.hd names.pool.function_slots in
  let value_slot_of_model = List.hd names.pool.value_slots in
  let code_of_model = List.hd names.pool.code_ids in
  let code = Converter.code_id_of_model numbering code_of_model in
  let rec_info = TG.this_rec_info (Rec_info_expr.var depth) in
  (* A closure of the model whose value slot holds a string. *)
  let closure (bytes : string) : MT.flambda_type =
    MT.exactly_this_closure slot_of_model
      [ ( slot_of_model,
          MT.Or_unknown.Known
            ({ function_type_code_id = code_of_model } : MT.function_type) ) ]
      []
      [ ( value_slot_of_model,
          MT.this_immutable_string
            (List.map
               (fun c -> N.z_of_int (Char.code c))
               (List.of_seq (String.to_seq bytes))) ) ]
      Heap
  in
  let with_rec_info m =
    Converter.type_of_model_with_rec_infos numbering machine_width
      ~rec_infos:[code, rec_info]
      m
  in
  let comparisons =
    Type_comparisons.comparisons_of_one_type numbering
    @ comparisons_of_what_is_dropped numbering
    @ Type_comparisons.round_trip_from_the_compiler numbering names.env
  in
  let outcome name (both : both) =
    let comparison =
      List.find
        (fun { name = name'; compare = _ } -> String.equal name name')
        comparisons
    in
    match guarded comparison.compare both with
    | Agree -> "agree"
    | Not_run _ -> "not run"
    | Disagree _ -> "disagree"
    | Known_to_disagree _ -> "recorded"
    | Not_this_comparison -> "not this comparison"
  in
  let of_compiler compiler : both =
    { model = to_model names compiler; compiler }
  in
  let exact = "free_variables against free_names, without shadowed bindings" in
  let with_dropped =
    "free_variables, with the variables of what the converter drops, against \
     free_names"
  in
  let as_printed = "the round trip from the compiler, as printed" in
  let for_equal_types =
    "the round trip from the compiler, for the compiler's equality"
  in
  let for_equal = "the round trip from the compiler, for Type_grammar.equal" in
  let alias_without : both =
    { model = MT.unknown Rec_info;
      compiler = TG.alias_type_of K.rec_info (Simple.var depth)
    }
  in
  let function_type = of_compiler (with_rec_info (closure "abc")) in
  (* [this_rec_info] of a variable alone is an alias to it, which the model has:
     a head is an expression that is more than a variable. *)
  let head =
    of_compiler
      (TG.this_rec_info (Rec_info_expr.succ (Rec_info_expr.var depth)))
  in
  (* The second closure, with the [rec_info] of the first put into it. *)
  let first = with_rec_info (closure "aaaaaaaaaaaaX") in
  let second_with_the_rec_info_of_the_first =
    let (_ : MT.flambda_type), (dropped : Converter.dropped) =
      Converter.type_to_model_with_what_is_dropped numbering first
    in
    Converter.type_of_model_with_rec_infos numbering machine_width
      ~rec_infos:dropped.rec_infos (closure "aaaaaaaaaaaaY")
  in
  (* A closure whose function type has the [rec_info], and whose value slot
     holds a closure of the same code with the unknown one. *)
  let two_rec_infos_for_one_code =
    let slot = Converter.function_slot_of_model numbering slot_of_model in
    let value_slot =
      Converter.value_slot_of_model numbering value_slot_of_model
    in
    let closure rec_info value_slots =
      MTC.exactly_this_closure slot
        ~all_function_slots_in_set:
          (Function_slot.Map.singleton slot
             (Or_unknown.Known (TG.Function_type.create code ~rec_info)))
        ~all_closure_types_in_set:Function_slot.Map.empty
        ~all_value_slots_in_set:value_slots
        (Converter.alloc_mode_of_model Heap)
    in
    of_compiler
      (closure rec_info
         (Value_slot.Map.singleton value_slot
            (closure TG.any_rec_info Value_slot.Map.empty)))
  in
  let expect what expected actual = what, String.equal expected actual in
  let cases =
    [ expect "an alias to a variable that the model's type has not: exact"
        "disagree"
        (outcome exact alias_without);
      expect
        "an alias to a variable that the model's type has not: with what is \
         dropped"
        "disagree"
        (outcome with_dropped alias_without);
      expect "a function type with a rec_info of a variable: exact" "not run"
        (outcome exact function_type);
      expect
        "a function type with a rec_info of a variable: with what is dropped"
        "agree"
        (outcome with_dropped function_type);
      expect "a function type with a rec_info of a variable: as printed" "agree"
        (outcome as_printed function_type);
      expect
        "a function type with a rec_info of a variable: the compiler's equality"
        "agree"
        (outcome for_equal_types function_type);
      expect "a function type with a rec_info of a variable: Type_grammar.equal"
        "agree"
        (outcome for_equal function_type);
      expect "a Rec_info head that mentions a variable: exact" "not run"
        (outcome exact head);
      expect "a Rec_info head that mentions a variable: with what is dropped"
        "agree"
        (outcome with_dropped head);
      expect "a Rec_info head that mentions a variable: as printed" "not run"
        (outcome as_printed head);
      ( "two closures that differ in the end of a long string: printed alike",
        String.equal
          (print_compiler_type first)
          (print_compiler_type second_with_the_rec_info_of_the_first) );
      ( "two closures that differ in the end of a long string: not the same \
         for Type_grammar.equal",
        not (TG.equal first second_with_the_rec_info_of_the_first) );
      ( "two closures that differ in the end of a long string: not the same \
         for the compiler's equality",
        not
          (Equal.equal_type
             ~config:(Equal.create_config ~ignore_alloc_mode:false ())
             ~meet_expanded_head:binary.meet_expanded_head names.env first
             second_with_the_rec_info_of_the_first) );
      expect "one code id with a rec_info and with the unknown one: as printed"
        "not run"
        (outcome as_printed two_rec_infos_for_one_code);
      expect
        "one code id with a rec_info and with the unknown one: \
         Type_grammar.equal"
        "not run"
        (outcome for_equal two_rec_infos_for_one_code) ]
  in
  let wrong = List.filter (fun (_, as_expected) -> not as_expected) cases in
  Format.printf
    "@.What the model has not got of Rec_info (%d cases): %d as expected@."
    (List.length cases)
    (List.length cases - List.length wrong);
  List.iter (fun (what, _) -> Format.printf "  WRONG: %s@." what) wrong;
  failures := !failures + List.length wrong

(* ======================================================================== *)
(* The ranges of numbers                                                    *)
(* ======================================================================== *)

(* Numbers of the model at the ends of the range of each kind, and the numbers
   next to them outside. An integer of n bits has four (the greatest, the least,
   and the one beyond each), and so has a bit pattern of n bits, which is read
   as such an integer. Of each, [const_in_range] of the model
   (FlambdaPrimitiveSpec.v) says whether it is in range; the converter takes one
   that is to the compiler and back unchanged, and refuses one that is not. The
   numbers are made with the arithmetic of the model, not with the functions of
   model_numbers.ml that are under test.

   Then constants made in the compiler whose top bit is set (the floats that are
   minus zero, patterns of ones): the converter gives for each a constant that
   is in the range of the model, and takes it back to the same constant of the
   compiler. *)
let ranges_of_numbers () =
  let z = N.z_of_int in
  let ends (const : N.z -> M.const) ~bits =
    let limit = Z.pow (z 2) (z (bits - 1)) in
    [ const (Z.sub limit (z 1)), true;
      const limit, false;
      const (Z.opp limit), true;
      const (Z.sub (Z.opp limit) (z 1)), false ]
  in
  let cases : (M.const * bool) list =
    ends (fun i -> Naked_immediate i) ~bits:63
    @ ends (fun i -> Tagged_immediate i) ~bits:63
    @ ends (fun i -> Naked_int8 i) ~bits:8
    @ ends (fun i -> Naked_int16 i) ~bits:16
    @ ends (fun i -> Naked_int32 i) ~bits:32
    @ ends (fun i -> Naked_int64 i) ~bits:64
    @ ends (fun i -> Naked_nativeint i) ~bits:64
    @ ends (fun f -> Naked_float32 f) ~bits:32
    @ ends (fun f -> Naked_float f) ~bits:64
    @ ends (fun m -> Naked_mask m) ~bits:64
    @ ends (fun v -> Naked_vec128 v) ~bits:128
    @ ends (fun v -> Naked_vec256 v) ~bits:256
    @ ends (fun v -> Naked_vec512 v) ~bits:512
  in
  let wrong =
    List.filter
      (fun (const, in_range) ->
        (not (Bool.equal (Primitive_spec.const_in_range const) in_range))
        ||
        match Converter.const_of_model machine_width const with
        | converted ->
          let back = Converter.const_to_model converted in
          not (in_range && Stdlib.( = ) back const)
        | exception Converter.Not_in_the_compiler _ -> in_range)
      cases
  in
  let ones = -1L and top = Int64.min_int in
  let module Float32 = Numeric_types.Float32_by_bit_pattern in
  let module Float = Numeric_types.Float_by_bit_pattern in
  let module Vec128 = Vector_types.Vec128.Bit_pattern in
  let module Vec256 = Vector_types.Vec256.Bit_pattern in
  let module Vec512 = Vector_types.Vec512.Bit_pattern in
  let module Mask = Vector_types.Mask.Bit_pattern in
  let module RWC = Reg_width_const in
  (* A vector whose most significant word is [high], the others [low]. *)
  let vec128 ~low ~high =
    RWC.naked_vec128 (Vec128.of_bits { word0 = low; word1 = high })
  in
  let vec256 ~low ~high =
    RWC.naked_vec256
      (Vec256.of_bits { word0 = low; word1 = low; word2 = low; word3 = high })
  in
  let vec512 ~low ~high =
    RWC.naked_vec512
      (Vec512.of_bits
         { word0 = low;
           word1 = low;
           word2 = low;
           word3 = low;
           word4 = low;
           word5 = low;
           word6 = low;
           word7 = high
         })
  in
  let from_the_compiler : (string * RWC.t) list =
    [ ( "the float32 that is minus zero",
        RWC.naked_float32 (Float32.of_bits Int32.min_int) );
      "a float32 of ones", RWC.naked_float32 (Float32.of_bits (-1l));
      "the float that is minus zero", RWC.naked_float (Float.of_bits top);
      "a float of ones", RWC.naked_float (Float.of_bits ones);
      ( "a mask with its top bit only",
        RWC.naked_mask (Mask.of_bits { word0 = top }) );
      "a mask of ones", RWC.naked_mask (Mask.of_bits { word0 = ones });
      "a vec128 with its top bit only", vec128 ~low:0L ~high:top;
      "a vec128 of ones", vec128 ~low:ones ~high:ones;
      "a vec256 with its top bit only", vec256 ~low:0L ~high:top;
      "a vec256 of ones", vec256 ~low:ones ~high:ones;
      "a vec512 with its top bit only", vec512 ~low:0L ~high:top;
      "a vec512 of ones", vec512 ~low:ones ~high:ones ]
  in
  let wrong_from_the_compiler =
    List.filter
      (fun ((_ : string), const) ->
        let converted = Converter.const_to_model const in
        not
          (Primitive_spec.const_in_range converted
          &&
          match Converter.const_of_model machine_width converted with
          | back -> RWC.equal back const
          | exception Converter.Not_in_the_compiler _ -> false))
      from_the_compiler
  in
  Format.printf "@.The ranges of numbers (%d constants): %d as expected@."
    (List.length cases)
    (List.length cases - List.length wrong);
  List.iter
    (fun (const, in_range) ->
      Format.printf "  WRONG: %a is %s@." Model_type.print_const const
        (if in_range
         then
           "refused, changed or not in the range of the model, and is in range"
         else "accepted, or in the range of the model, and is out of range"))
    wrong;
  Format.printf
    "Constants of the compiler with the top bit set (%d): %d in the range of \
     the model and unchanged by the round trip@."
    (List.length from_the_compiler)
    (List.length from_the_compiler - List.length wrong_from_the_compiler);
  List.iter
    (fun (what, _) -> Format.printf "  WRONG: %s@." what)
    wrong_from_the_compiler;
  failures
    := !failures + List.length wrong + List.length wrong_from_the_compiler

(* ======================================================================== *)
(* The tests                                                                *)
(* ======================================================================== *)

let () =
  let comp_unit = Compilation_unit.of_string "Types_difftest" in
  Env.set_current_unit
    (Unit_info.make_dummy ~input_name:"types_difftest" comp_unit);
  let names = create_names () in
  let structural = Oxcaml_flags.Set Oxcaml_flags.Structural in
  Oxcaml_flags.Flambda2.join_sharing := structural;
  Format.printf
    "The types of the compiler against the Rocq model.@.Stack allocation: \
     %s.@.Joins: with -flambda2-join-sharing structural, but where the \
     compiler's default is named.@."
    (if Flambda2_ui.Flambda_features.stack_allocation_enabled ()
     then "enabled"
     else "disabled");
  ranges_of_numbers ();
  comparison_by_text names;
  rec_info_cases names;
  run ~title:"Raw types of the model" ~seed:1000 ~count:3000
    ~generate:(fun r ->
      G.flambda_type { well_formed = false; depth = 3 } r names.pool)
    ~prepare:(both names) ~shrink:G.shrink ~print:Model_type.print
    (comparisons_of_one_type names);
  run ~title:"Types of the model that the compiler's functions make" ~seed:5000
    ~count:3000
    ~generate:(fun r ->
      G.flambda_type { well_formed = true; depth = 3 } r names.pool)
    ~prepare:(both names) ~shrink:G.shrink ~print:Model_type.print
    (comparisons_of_one_type names
    @ round_trip_from_the_compiler names
    @ well_formed_types names);
  let pairs_for_equality ~title ~seed (config : G.config) =
    run ~title ~seed ~count:1500
      ~generate:(generate_pair_for_equality names config)
      ~prepare:(fun (m1, m2) ->
        ignore (to_compiler names m1 : TG.t);
        ignore (to_compiler names m2 : TG.t);
        m1, m2)
      ~shrink:(fun (m1, m2) ->
        List.map (fun m1 -> m1, m2) (G.shrink m1)
        @ List.map (fun m2 -> m1, m2) (G.shrink m2))
      ~print:(fun ppf (m1, m2) ->
        Format.fprintf ppf "@[<v>%a@ and@ %a@]" Model_type.print m1
          Model_type.print m2)
      (equality_of_types names)
  in
  pairs_for_equality
    ~title:
      "Two types of the model that the compiler's functions make, for the \
       equality of types"
    ~seed:12000
    { well_formed = true; depth = 3 };
  pairs_for_equality
    ~title:"Two raw types of the model, for the equality of types" ~seed:14000
    { well_formed = false; depth = 2 };
  run ~title:"The creation functions" ~seed:20000 ~count:10000
    ~generate:(generate_call names)
    ~prepare:(fun call -> call)
    ~shrink:(fun _ -> [])
    ~print:print_call (creation_functions names);
  run ~title:"A relation and a constant" ~seed:30000 ~count:600
    ~generate:(fun r ->
      let config : G.config = { well_formed = true; depth = 0 } in
      let kind = G.pick r G.all_kinds in
      ( G.relation r,
        match G.const_of_kind config r kind with
        | Some const -> const
        | None -> M.Poison kind ))
    ~prepare:(fun input -> input)
    ~shrink:(fun _ -> [])
    ~print:(fun ppf (relation, const) ->
      Format.fprintf ppf "%a of %a" Model_type.print_relation relation
        Model_type.print_const const)
    (relation_of_const names);
  run ~title:"Raw row-like structures of blocks" ~seed:31000 ~count:1000
    ~generate:(fun r ->
      G.row_like_for_blocks { well_formed = false; depth = 1 } r names.pool)
    ~prepare:(fun blocks ->
      ignore
        (Converter.row_like_for_blocks_of_model names.numbering machine_width
           blocks
          : TG.row_like_for_blocks);
      blocks)
    ~shrink:G.shrink_row_like_for_blocks
    ~print:(fun ppf blocks ->
      Model_type.print ppf (blocks_as_type_of_model blocks))
    (row_like_bottom names);
  run ~title:"Two types of kind value, for the two meets and the two joins"
    ~seed:9000 ~count:1000
    ~generate:(fun r ->
      let config : G.config = { well_formed = true; depth = 2 } in
      ( G.type_of_kind config r names.pool Value,
        G.type_of_kind config r names.pool Value ))
    ~prepare:(fun (m1, m2) ->
      ignore (to_compiler names m1 : TG.t);
      ignore (to_compiler names m2 : TG.t);
      m1, m2)
    ~shrink:(fun (m1, m2) ->
      List.map (fun m1 -> m1, m2) (G.shrink m1)
      @ List.map (fun m2 -> m1, m2) (G.shrink m2))
    ~print:(fun ppf (m1, m2) ->
      Format.fprintf ppf "@[<v>%a@ and@ %a@]" Model_type.print m1
        Model_type.print m2)
    (two_implementations names);
  let semantic_pairs ~title ~seed ~count kind =
    run ~title ~seed ~count
      ~generate:(fun r ->
        let config : G.config = { well_formed = true; depth = 2 } in
        let first = G.type_of_kind config r names.pool kind in
        let second = G.type_of_kind config r names.pool kind in
        { world_seed = Random.int r; first; second })
      ~prepare:(fun case ->
        ignore (to_compiler names case.first : TG.t);
        ignore (to_compiler names case.second : TG.t);
        case)
      ~shrink:shrink_semantic_case ~print:print_semantic_case
  in
  semantic_pairs
    ~title:
      "Two types of kind value and a world, for the meaning of meet and join"
    ~seed:40000 ~count:1500 MK.Value
    (semantic_comparisons names);
  semantic_pairs
    ~title:
      "Two types of naked immediates and a world, for the meaning of meet and \
       join"
    ~seed:50000 ~count:1500 (MK.Naked_number Kind_naked_immediate)
    (semantic_comparisons names);
  let other_kinds =
    List.filter
      (fun (kind : MK.flambda_kind) ->
        match kind with
        | Value | Naked_number Kind_naked_immediate -> false
        | Naked_number
            ( Kind_naked_float32 | Kind_naked_float | Kind_naked_int8
            | Kind_naked_int16 | Kind_naked_int32 | Kind_naked_int64
            | Kind_naked_nativeint | Kind_naked_vec128 | Kind_naked_vec256
            | Kind_naked_vec512 | Kind_naked_mask )
        | Region | Rec_info ->
          true)
      G.all_kinds
  in
  run
    ~title:
      "Two types of one of the other kinds and a world, for the meaning of \
       meet and join"
    ~seed:55000 ~count:600
    ~generate:(fun r ->
      let config : G.config = { well_formed = true; depth = 2 } in
      let kind = G.pick r other_kinds in
      let first = G.type_of_kind config r names.pool kind in
      let second = G.type_of_kind config r names.pool kind in
      { world_seed = Random.int r; first; second })
    ~prepare:(fun case ->
      ignore (to_compiler names case.first : TG.t);
      ignore (to_compiler names case.second : TG.t);
      case)
    ~shrink:shrink_semantic_case ~print:print_semantic_case
    (semantic_comparisons names);
  (* Chosen pairs, each in a few worlds. The first is T1-4: a closure whose own
     function has a known code, and a closure of which nothing is said of the
     code. *)
  let chosen =
    let slot =
      List.find
        (fun slot -> Stdlib.( = ) slot V.unnamed_function_slot)
        names.pool.function_slots
    in
    let closure function_types =
      MT.at_least_this_closure slot function_types [] [] MT.Alloc_mode.Heap
    in
    let code : MT.function_type =
      { function_type_code_id = List.hd names.pool.code_ids }
    in
    [closure [slot, MT.Or_unknown.Known code], closure []]
  in
  let next = ref 0 in
  run ~title:"Chosen pairs of types, for the meaning of meet and join"
    ~seed:60000
    ~count:(3 * List.length chosen)
    ~generate:(fun r ->
      let first, second = List.nth chosen (!next / 3) in
      incr next;
      { world_seed = Random.int r; first; second })
    ~prepare:(fun case -> case)
    ~shrink:(fun _ -> [])
    ~print:print_semantic_case
    (semantic_comparisons names);
  chosen_joins names (the_chosen_joins names);
  run_examples_of_joins names;
  run_examples_of_meets ();
  chosen_meets ();
  let with_itself ~title sharing =
    run ~title ~seed:70000 ~count:1500
      ~generate:(fun r ->
        G.type_of_kind { well_formed = true; depth = 3 } r names.pool MK.Value)
      ~prepare:(fun m ->
        ignore (to_compiler names m : TG.t);
        m)
      ~shrink:G.shrink ~print:Model_type.print
      (shared_and_not names sharing)
  in
  let with_a_common_part ~title sharing =
    run ~title ~seed:80000 ~count:1000
      ~generate:(fun r ->
        let part () =
          G.type_of_kind { well_formed = true; depth = 2 } r names.pool MK.Value
        in
        let common = part () in
        let left = part () in
        let right = part () in
        { common; left; right })
      ~prepare:(fun ({ common; left; right } as parts) ->
        ignore (to_compiler names common : TG.t);
        ignore (to_compiler names left : TG.t);
        ignore (to_compiler names right : TG.t);
        parts)
      ~shrink:(fun ({ common; left; right } as parts) ->
        List.map (fun common -> { parts with common }) (G.shrink common)
        @ List.map (fun left -> { parts with left }) (G.shrink left)
        @ List.map (fun right -> { parts with right }) (G.shrink right))
      ~print:(fun ppf { common; left; right } ->
        Format.fprintf ppf
          "@[<v>the common part@ %a@ the other part of the first@ %a@ the \
           other part of the second@ %a@]"
          Model_type.print common Model_type.print left Model_type.print right)
      (shared_parts names sharing)
  in
  with_itself ~title:"A type of kind value with itself, shared and not"
    Structural_sharing;
  with_a_common_part
    ~title:"Two types of kind value with a common part, shared and not"
    Structural_sharing;
  with_join_sharing Oxcaml_flags.Physical (fun () ->
      with_itself
        ~title:
          "A type of kind value with itself, shared and not, with the \
           compiler's default for the sharing of joins"
        Default_sharing;
      with_a_common_part
        ~title:
          "Two types of kind value with a common part, shared and not, with \
           the compiler's default for the sharing of joins"
        Default_sharing);
  Format.printf "@.%s@."
    (if !failures = 0
     then "No disagreement."
     else Printf.sprintf "%d DISAGREEMENTS." !failures);
  if !failures > 0 then exit 1
