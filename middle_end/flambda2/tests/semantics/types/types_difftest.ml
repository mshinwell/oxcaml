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
module K = Flambda_kind
module TG = Flambda2_types__Type_grammar
module TE = Flambda2_types__Typing_env
module Equal = Flambda2_types__Equal_types_for_debug
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
module Converter = Flambda2_rocq_types_converter.Type_converter
module Model_names = Flambda2_rocq_types_converter.Model_names
module Model_type = Flambda2_rocq_types_converter.Model_type
module N = Flambda2_rocq_types_converter.Model_numbers
module G = Type_generator
module Random = Minicheck.Splittable_random

let machine_width = Target_system.Machine_width.Sixty_four

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
    (* A parameter of a continuation, for the joins. It is not in the pool: no
       generated type mentions it. *)
    parameter : Variable.t;
    (* The variables of the tests are numbered from 1 to this. *)
    variables_of_the_tests : int
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
  let parameter = Variable.create "p" K.value in
  let value_variables = number numbering.variables value_variables in
  let naked_immediate_variables =
    number numbering.variables naked_immediate_variables
  in
  let naked_float_variables =
    number numbering.variables naked_float_variables
  in
  let region_variables = number numbering.variables region_variables in
  let rec_info_variables = number numbering.variables rec_info_variables in
  (* The parameter is numbered after the variables of the pool. *)
  let (_ : N.positive) = numbering.variables.number parameter in
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
    parameter;
    variables_of_the_tests = List.length all_variables + 1
  }

(* ======================================================================== *)
(* Running a comparison                                                     *)
(* ======================================================================== *)

type outcome =
  | Not_this_comparison
      (** The input is for another comparison of the list: not counted. *)
  | Agree
  | Not_run of string  (** The comparison does not apply, and why. *)
  | Disagree of string
  | Known_to_disagree of string * string
      (** A disagreement that is recorded: the entry of the record of
          discrepancies with what it is about, and what the disagreement is. It
          is expected, and one case of each is shown; it is not a failure of the
          test. *)

type 'input comparison =
  { name : string;
    compare : 'input -> outcome
  }

(* A failure of the compiler itself on an input is not an answer to compare: it
   is counted with the cases that could not be run. *)
let guarded compare input =
  match compare input with
  | outcome -> outcome
  | exception Misc.Fatal_error -> Not_run "a fatal error of the compiler"
  | exception Converter.Not_in_the_model what ->
    Not_run ("not in the model: " ^ what)
  | exception Converter.Not_in_the_compiler what ->
    Not_run ("not in the compiler: " ^ what)

(* A reason without what is particular to one case (numbers, names), so that
   reasons can be counted. *)
let general reason =
  let digit c = c >= '0' && c <= '9' in
  let zeros = String.map (fun c -> if digit c then '0' else c) reason in
  String.concat "N"
    (List.filter
       (fun part -> not (String.equal part ""))
       (String.split_on_char '0' zeros))

let failures = ref 0

(* Runs each comparison on [count] inputs. Case [i] is generated from the seed
   [seed + i] alone, so a case can be run again on its own. [prepare] is what
   every comparison needs of an input (its conversion): an input that it refuses
   goes to no comparison, and the refusals are counted once. An input on which a
   comparison disagrees is shrunk as long as the comparison still disagrees on
   it. *)
let count_reasons reasons =
  let counts = Hashtbl.create 8 in
  List.iter
    (fun reason ->
      let reason = general reason in
      Hashtbl.replace counts reason
        (1 + Option.value (Hashtbl.find_opt counts reason) ~default:0))
    reasons;
  List.sort Stdlib.compare (List.of_seq (Hashtbl.to_seq counts))

let run ~title ~seed ~count ~generate ~prepare ~shrink ~print
    (comparisons : _ comparison list) =
  Format.printf "@.%s (%d cases, seeds %d to %d)@." title count seed
    (seed + count - 1);
  let prepared input =
    guarded
      (fun input ->
        ignore (prepare input);
        Agree)
      input
  in
  let inputs =
    List.init count (fun i -> seed + i, generate (Random.of_int (seed + i)))
  in
  let refused, inputs =
    List.partition_map
      (fun (case_seed, input) ->
        match prepared input with
        | Agree | Not_this_comparison -> Right (case_seed, input)
        | Not_run reason | Disagree reason | Known_to_disagree (_, reason) ->
          Left reason)
      inputs
  in
  List.iter
    (fun (reason, n) -> Format.printf "  %d not converted: %s@." n reason)
    (count_reasons refused);
  Format.printf "  %d converted@." (List.length inputs);
  List.iter
    (fun { name; compare } ->
      let compare input =
        guarded (fun input -> compare (prepare input)) input
      in
      let agreed = ref 0 in
      let not_run = ref [] in
      let disagreed = ref [] in
      let known = ref [] in
      List.iter
        (fun (case_seed, input) ->
          match compare input with
          | Not_this_comparison -> ()
          | Agree -> incr agreed
          | Not_run reason -> not_run := reason :: !not_run
          | Known_to_disagree (entry, what) ->
            (* Shrunk like any other, as long as it is the same entry. *)
            let rec smallest steps input what =
              let still candidate =
                match compare candidate with
                | Known_to_disagree (entry', what)
                  when String.equal entry entry' ->
                  Some (candidate, what)
                | Not_this_comparison | Agree | Not_run _ | Disagree _
                | Known_to_disagree _ ->
                  None
              in
              match
                if steps = 0 then None else List.find_map still (shrink input)
              with
              | Some (input, what) -> smallest (steps - 1) input what
              | None -> input, what
            in
            let input, what = smallest 200 input what in
            known := (entry, case_seed, input, what) :: !known
          | Disagree what ->
            let rec smallest steps input what =
              let disagrees candidate =
                match compare candidate with
                | Disagree what -> Some (candidate, what)
                | Not_this_comparison | Agree | Not_run _ | Known_to_disagree _
                  ->
                  None
              in
              match
                if steps = 0
                then None
                else List.find_map disagrees (shrink input)
              with
              | Some (input, what) -> smallest (steps - 1) input what
              | None -> input, what
            in
            let input, what = smallest 200 input what in
            disagreed := (case_seed, input, what) :: !disagreed)
        inputs;
      let disagreed = List.rev !disagreed in
      Format.printf "  %s: %d agree" name !agreed;
      if disagreed <> []
      then Format.printf ", %d DISAGREE" (List.length disagreed);
      let known = List.rev !known in
      if known <> []
      then Format.printf ", %d disagree as recorded" (List.length known);
      Format.printf "@.";
      List.iter
        (fun (reason, n) -> Format.printf "    %d not run: %s@." n reason)
        (count_reasons !not_run);
      (* One case of each recorded disagreement is shown. *)
      List.iter
        (fun (entry, case_seed, input, what) ->
          Format.printf
            "    @[<v>recorded as %s (seed %d): %s@ on the shrunk input:@ \
             @[%a@]@]@."
            entry case_seed what print input)
        (List.sort_uniq
           (fun (entry, _, _, _) (entry', _, _, _) ->
             String.compare entry entry')
           known);
      (* The first few disagreements are shown in full. *)
      List.iteri
        (fun i (case_seed, input, what) ->
          if i < 3
          then
            Format.printf
              "    @[<v>DISAGREEMENT (seed %d): %s@ on the shrunk input:@ \
               @[%a@]@]@."
              case_seed what print input)
        disagreed;
      failures := !failures + List.length disagreed)
    comparisons

(* ======================================================================== *)
(* The comparisons of one type                                              *)
(* ======================================================================== *)

let print_compiler_type t = Format.asprintf "%a" TG.print t

let to_compiler (names : names) (t : MT.flambda_type) : TG.t =
  Converter.type_of_model names.numbering machine_width t

let to_model (names : names) (t : TG.t) : MT.flambda_type =
  Converter.type_to_model names.numbering t

let agree_if condition what = if condition then Agree else Disagree what

(* The variables of [Type_grammar.free_names], as numbers. *)
let free_variables_of_compiler (names : names) (t : TG.t) : M.variable list =
  Name_occurrences.fold_variables (TG.free_names t) ~init:[]
    ~f:(fun variables var ->
      Converter.variable_to_model names.numbering var :: variables)

(* A type of the model with the type of the compiler made from it. *)
type both =
  { model : MT.flambda_type;
    compiler : TG.t
  }

let both (names : names) (m : MT.flambda_type) : both =
  { model = m; compiler = to_compiler names m }

(* Each function of one type that the model has, against the compiler's. *)
let comparisons_of_one_type (names : names) : both comparison list =
  let on_both name answer_of_model answer_of_compiler same print =
    { name;
      compare =
        (fun { model; compiler } ->
          let of_model = answer_of_model model in
          let of_compiler = answer_of_compiler compiler in
          agree_if
            (same of_model of_compiler)
            (Format.asprintf "the model answers %a, the compiler %a" print
               of_model print of_compiler))
    }
  in
  let print_simple_option ppf simple =
    match simple with
    | None -> Format.pp_print_string ppf "None"
    | Some simple -> Model_type.print_simple ppf simple
  in
  let print_variables ppf variables =
    Model_type.print_list Model_type.print_variable ppf
      (Model_type.set N.compare_positive variables)
  in
  [ { name = "the round trip from the model (to the compiler and back)";
      compare =
        (fun { model; compiler } ->
          let back = to_model names compiler in
          agree_if
            (Model_type.same model back)
            (Format.asprintf "the type comes back as %a" Model_type.print back))
    };
    on_both "kind" MT.kind
      (fun t -> Converter.kind_to_model (TG.kind t))
      Stdlib.( = ) Model_type.print_kind;
    on_both "get_alias_opt" MT.get_alias_opt
      (fun t ->
        Option.map
          (Converter.simple_to_model names.numbering)
          (TG.get_alias_opt t))
      Stdlib.( = ) print_simple_option;
    on_both "is_obviously_bottom" MT.is_obviously_bottom TG.is_obviously_bottom
      Bool.equal Format.pp_print_bool;
    on_both "is_obviously_unknown" MT.is_obviously_unknown
      TG.is_obviously_unknown Bool.equal Format.pp_print_bool;
    (* The model lists the variables of the bindings of a map that an earlier
       binding shadows (FlambdaTypeGrammar.v says so), and a map of the compiler
       has no such binding. So the two are compared on the type with its maps
       written in one way, and on the type as it is the model's answer has to
       include the compiler's. *)
    on_both "free_variables against free_names, without shadowed bindings"
      (fun m -> MT.free_variables (Model_type.normalise m))
      (free_variables_of_compiler names)
      Model_type.same_variables print_variables;
    on_both "free_variables includes free_names, with shadowed bindings"
      MT.free_variables
      (free_variables_of_compiler names)
      (fun of_model of_compiler ->
        List.for_all (fun x -> List.mem x of_model) of_compiler)
      print_variables ]

(* The round trip from the compiler: a type of the compiler, to the model and
   back, is the same type for the compiler's own equality
   ([Equal_types_for_debug], allocation modes included) and is printed the same.
   The types of the compiler are those made from generated types of the model,
   so this is what the converter keeps of a type and not what it drops: that is
   the cases at the end of this file. *)
let round_trip_from_the_compiler (names : names) : both comparison list =
  let back t = to_compiler names (to_model names t) in
  [ { name = "the round trip from the compiler, as printed";
      compare =
        (fun { model = _; compiler } ->
          let back = back compiler in
          agree_if
            (String.equal
               (print_compiler_type compiler)
               (print_compiler_type back))
            ("the type comes back as " ^ print_compiler_type back))
    };
    { name = "the round trip from the compiler, for the compiler's equality";
      compare =
        (fun { model; compiler } ->
          let back = back compiler in
          (* On a type with an extension within an extension the compiler's
             equality may overflow the stack (T7-2: an extension that gives a
             name a type with an extension on that name). The compiler built
             here raises that as an asynchronous exception, which only
             [Sys.with_async_exns] catches, and the compiler that builds this
             file first has no such function: so the equality is not asked of
             such a type. *)
          if Model_type.extension_depth model >= 2
          then
            Known_to_disagree
              ( "T7-2",
                "the compiler's equality is not asked: it may overflow the \
                 stack on a type with an extension within an extension" )
          else
            let equal =
              Equal.equal_type
                ~config:(Equal.create_config ~ignore_alloc_mode:false ())
                ~meet_expanded_head:Binary.meet_expanded_head names.env compiler
                back
            in
            let back = print_compiler_type back in
            agree_if equal ("the type comes back as " ^ back))
    } ]

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
    "at_least_this_closure" ]

(* A row-like structure of blocks as a type, to compare it as one. *)
let blocks_as_type_of_model (blocks : MT.row_like_for_blocks) =
  MT.create_variant false MT.Or_unknown.Unknown (MT.Or_unknown.Known blocks)
    MT.No_extensions

let blocks_as_type_of_compiler (blocks : TG.row_like_for_blocks) =
  TG.create_variant ~is_unique:false ~immediates:Unknown ~blocks:(Known blocks)
    ~extensions:No_extensions

let call_in_the_model (call : call) : MT.flambda_type =
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
      (fun () -> At_least_this_closure (slots_and_types ())) ]
  in
  (G.pick r generators) ()

(* A call is shown by the type that the model makes of it. *)
let print_call ppf (call : call) =
  Format.fprintf ppf "@[<v>a call of %s, which in the model gives@ %a@]"
    (name_of_call call) Model_type.print (call_in_the_model call)

let creation_functions (names : names) : call comparison list =
  List.map
    (fun name ->
      { name;
        compare =
          (fun call ->
            if not (String.equal (name_of_call call) name)
            then Not_this_comparison
            else
              match call_in_the_compiler names call with
              | exception No_such_function why -> Not_run why
              | of_compiler ->
                let of_compiler = to_model names of_compiler in
                agree_if
                  (Model_type.same (call_in_the_model call) of_compiler)
                  (Format.asprintf "the compiler gives %a" Model_type.print
                     of_compiler))
      })
    names_of_calls
  @ [ { name = "a creation function that is not in the list above";
        compare =
          (fun call ->
            if List.mem (name_of_call call) names_of_calls
            then Not_this_comparison
            else Disagree "it is compared with nothing")
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

(* The type of the parameter of a continuation that is applied to a value of
   each of the types given, one at each use. *)
let join_as_model (names : names) (implementation : implementation)
    (types : TG.t list) : MT.flambda_type =
  let parameter = Name.var names.parameter in
  let env =
    TE.add_definition names.env
      (Bound_name.create_var
         (Bound_var.create names.parameter Flambda_debug_uid.none
            Name_mode.normal))
      K.value
  in
  let use_envs =
    List.map
      (fun t ->
        ME.use_meet_env ~meet_expanded_head:implementation.meet_expanded_head
          (TE.increment_scope env) ~f:(fun env ->
            ME.add_equation env parameter t
              ~meet_expanded_head:implementation.meet_expanded_head))
      types
  in
  let joined =
    implementation.join env use_envs
      ~params:
        (Bound_parameters.create
           [ Bound_parameter.create names.parameter K.With_subkind.any_value
               Flambda_debug_uid.none ])
      ~cut_after:(TE.current_scope env)
  in
  to_model names (TE.find joined parameter (Some K.value))

(* A type as printed, written in one way, with the variables that are not those
   of the tests named [e0], [e1], ... in the order they come. *)
let print_with_own_variables (names : names) (m : MT.flambda_type) : string =
  let printed =
    Format.asprintf "%a" Model_type.print (Model_type.normalise m)
  in
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
        if number <= names.variables_of_the_tests
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

let two_implementations (names : names) :
    (MT.flambda_type * MT.flambda_type) comparison list =
  let print_meet ppf result =
    match result with
    | None -> Format.pp_print_string ppf "Bottom"
    | Some (t, types) ->
      Format.fprintf ppf "@[<v>%a@ and for the names %a@]" Model_type.print t
        print_types types
  in
  [ { name = "meet: the binary and the n-way implementation";
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
          let of_binary = join_as_model names binary types in
          let of_n_way = join_as_model names n_way types in
          (* A join may make variables of its own, which are not the same
             variables in the two: the two types are compared as they are
             printed, with those variables named in the order they come. *)
          let printed m = print_with_own_variables names m in
          if String.equal (printed of_binary) (printed of_n_way)
          then Agree
          else
            (* The two may differ in how much they keep: that is recorded and
               not a failure. Whether each is above the types joined is for the
               comparison with the meaning of types. *)
            Known_to_disagree
              ( (match
                   ( MT.is_obviously_unknown of_binary,
                     MT.is_obviously_unknown of_n_way )
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
  | 8 ->
    Value_closure
      ( G.pick r pool.code_ids,
        Model_type.map N.compare_positive Fun.id
          (G.list r ~max:2 (fun () ->
               G.pick r pool.value_slots, generate_value names r (depth - 1)))
      )
  | _ -> Value_symbol (G.pick r pool.symbols)

let generate_world (names : names) r : world =
  let pool = names.pool in
  let bind variables value = List.map (fun x -> x, value ()) variables in
  { statics =
      { static_code = [];
        static_values =
          List.map
            (fun symbol : (_ * V.statically_allocated_value) ->
              ( symbol,
                match G.below r 4 with
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
            | Value_block _ | Value_boxed_number _ ->
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
        | Value_block _ | Value_boxed_number _ ->
          None)
      (values_for names world contents)
  | Closures (Row_like_for_closures cases, _) ->
    (* A closure of each code, with the value slots of the index of each
       case. *)
    List.concat_map
      (fun (_, (case : (_, _, _, _) MT.row_like_case)) ->
        let (Closures_entry (_, _, value_slot_types) : MT.closures_entry) =
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
        List.map
          (fun code : V.value -> Value_closure (code, value_slots))
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
  | Value_const _ | Value_symbol _ | Value_boxed_number _ -> []
  | Value_block (_, fields) -> List.concat_map parts_of_value fields
  | Value_closure (_, value_slots) | Value_closure_of_set (_, _, value_slots) ->
    List.concat_map (fun (_, v) -> parts_of_value v) value_slots)

(* A join may make variables of its own, which stand for some value. A value has
   such a type if it has it for some values of those variables; the values tried
   are small numbers and the parts of the value. This asks less than the type
   means (it ignores what the joined environment says of those variables), so a
   value that fails it does not have the type. *)
let has_for_some_own_variables (world : world) (v : V.value)
    (t : MT.flambda_type) : bool option =
  let own =
    List.filter
      (fun x -> not (List.mem_assoc x world.vars))
      (Model_type.set N.compare_positive (MT.free_variables t))
  in
  let values = List.init 3 naked_immediate @ parts_of_value v in
  let rec for_some vars (own : M.variable list) =
    match own with
    | [] -> Meaning.type_satisfied_b world.statics vars v t
    | x :: own ->
      List.exists (fun value -> for_some ((x, value) :: vars) own) values
  in
  if List.compare_length_with own 3 > 0
  then None
  else Some (for_some world.vars own)

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
          if not (K.equal (TG.kind t1) K.value && K.equal (TG.kind t2) K.value)
          then Not_run "the parameter of the joins is of kind value"
          else
            let join = join_as_model names implementation [t1; t2] in
            let of_an_input =
              List.filter
                (fun v -> has world v first || has world v second)
                values
            in
            let outside =
              List.find_opt
                (fun v ->
                  match has_for_some_own_variables world v join with
                  | Some has -> not has
                  | None -> false)
                of_an_input
            in
            match outside, of_an_input with
            | Some v, _ ->
              let what =
                Format.asprintf
                  "@[<v>the value %a has one of the types and not their join,@ \
                   %a@]"
                  print_value v Model_type.print join
              in
              (* A function type that only one of the types has, kept by the
                 join: T1-4. *)
              let function_types_of (t : MT.flambda_type) =
                let of_head (head : MT.head_of_kind_value_non_null) =
                  match head with
                  | Closures (Row_like_for_closures cases, _) ->
                    List.concat_map
                      (fun (_, (case : (_, _, _, _) MT.row_like_case)) ->
                        let (Closures_entry (function_types, _, _)
                              : MT.closures_entry) =
                          case.case_maps_to
                        in
                        List.map fst function_types)
                      cases
                  | Variant _ | Mutable_block _ | Boxed_number _ | String _ ->
                    []
                in
                match t with
                | Type_value (Ok (No_alias (Head_of_kind_value (non_null, _))))
                  -> (
                  match non_null with
                  | Ok head -> of_head head
                  | Unknown | Bottom -> [])
                | Type_value (Unknown | Bottom | Ok (Equals _))
                | Type_naked_immediate _ | Type_naked_number _ | Type_rec_info _
                | Type_region _ ->
                  []
              in
              let kept =
                List.filter
                  (fun slot ->
                    not
                      (List.mem slot (function_types_of first)
                      && List.mem slot (function_types_of second)))
                  (function_types_of join)
              in
              if kept <> []
              then Known_to_disagree ("T1-4", what)
              else Disagree what
            | None, [] -> Not_run "no value tried has either type"
            | None, _ :: _ -> Agree)
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
            | [] -> Agree)
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
              (* What [reduce_inverse_relations] deduces from [Get_tag]. *)
              let about_get_tag (t : MT.flambda_type) =
                match t with
                | Type_naked_immediate (Ok (No_alias head)) ->
                  List.exists
                    (fun ((relation : MT.Relation.t), _) ->
                      match relation with
                      | Get_tag -> true
                      | Is_int | Is_null -> false)
                    head.inverse_relations
                | Type_naked_immediate (Unknown | Bottom | Ok (Equals _))
                | Type_value _ | Type_naked_number _ | Type_rec_info _
                | Type_region _ ->
                  false
              in
              if about_get_tag first || about_get_tag second
              then Known_to_disagree ("T1-1", what)
              else Disagree what
            | None, (Some _ | None) -> Agree))
    }
  in
  (* The other way, which is about how much a meet keeps and not about whether
     it is right: where what the meet teaches of the names is true, a value of
     the meet has both types. Where it has not, the meet is larger than the two
     types together. *)
  let contains ~part whole =
    let length = String.length part in
    let rec at i =
      i + length <= String.length whole
      && (String.equal (String.sub whole i length) part || at (i + 1))
    in
    at 0
  in
  let meet_is_no_larger (implementation : implementation) =
    { name =
        Printf.sprintf "meet (%s): a value of the meet has both types"
          implementation.implementation;
      compare =
        (fun ({ world_seed = _; first; second } as case) ->
          let world, values, t1, t2 = setting case in
          match implementation.meet names.env t1 t2 with
          | Bottom -> Agree
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
              | None -> Agree
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
let shared_and_not (names : names) : MT.flambda_type comparison list =
  let compare_results name of_types =
    { name;
      compare =
        (fun m ->
          let t = to_compiler names m in
          let again = to_compiler names m in
          let shared = of_types t t in
          let not_shared = of_types t again in
          if String.equal shared not_shared
          then Agree
          else
            Known_to_disagree
              ( "T7-7, a result that depends on sharing",
                Format.asprintf
                  "@[<v>with the two arguments one value:@ %s@ with the type \
                   built twice:@ %s@]"
                  shared not_shared ))
    }
  in
  let join implementation t t' =
    print_with_own_variables names (join_as_model names implementation [t; t'])
  in
  let meet implementation t t' =
    match meet_as_model names implementation t t' with
    | None -> "Bottom"
    | Some (meet, types) ->
      String.concat " "
        (List.map (print_with_own_variables names) (meet :: types))
  in
  [ compare_results "join (binary) of a type with itself" (join binary);
    compare_results "join (n-way) of a type with itself" (join n_way);
    compare_results "meet (binary) of a type with itself" (meet binary);
    compare_results "meet (n-way) of a type with itself" (meet n_way) ]

(* ======================================================================== *)
(* The tests                                                                *)
(* ======================================================================== *)

let () =
  let comp_unit = Compilation_unit.of_string "Types_difftest" in
  Env.set_current_unit
    (Unit_info.make_dummy ~input_name:"types_difftest" comp_unit);
  let names = create_names () in
  Format.printf
    "The types of the compiler against the Rocq model.@.Stack allocation: %s.@."
    (if Flambda2_ui.Flambda_features.stack_allocation_enabled ()
     then "enabled"
     else "disabled");
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
    (comparisons_of_one_type names @ round_trip_from_the_compiler names);
  run ~title:"The creation functions" ~seed:20000 ~count:6000
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
    ~title:"Two types of naked immediates and a world, for the meaning of meet"
    ~seed:50000 ~count:1500 (MK.Naked_number Kind_naked_immediate)
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
  run
    ~title:
      "A type of kind value with itself, shared and not (until the compiler \
       has a flag for it, results may depend on sharing)"
    ~seed:70000 ~count:1500
    ~generate:(fun r ->
      G.type_of_kind { well_formed = true; depth = 3 } r names.pool MK.Value)
    ~prepare:(fun m ->
      ignore (to_compiler names m : TG.t);
      m)
    ~shrink:G.shrink ~print:Model_type.print (shared_and_not names);
  Format.printf "@.%s@."
    (if !failures = 0
     then "No disagreement."
     else Printf.sprintf "%d DISAGREEMENTS." !failures);
  if !failures > 0 then exit 1
