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

(* The types that Simplify computes, against the Rocq model of types.

   The tests of types_difftest.ml run the model beside the compiler on types
   that a generator makes. Here the types are the compiler's own: a unit is read
   from a .fl file and simplified, and every typing environment that Simplify
   reports to the observer of the types library (at the start of each
   continuation handler that it simplifies, and at the end of the unit) is gone
   through, each name that it knows with its type. Each such type, unless it is
   one already seen for the name (for [Type_grammar.equal], the compiler's
   structural equality), is taken to the model by the converter, and the
   comparisons of one type are run on it (type_comparisons.ml): each function
   that the model has of a type against the compiler's, the type there and back,
   and whether the type is well formed ([type_well_formed] of
   FlambdaTypeWellFormedSpec.v, which is meant to be true of every type that the
   compiler builds).

   What is printed for a file is a line: the environments, the names, the
   different types and those that the model has; and at the end, for all the
   files, the types that the model has not got and why, and for each comparison
   how many types agree and how many are not run and why. A disagreement is
   shown in full under its file and makes the tool fail.

   With [-cmx] the argument is a directory, and the types are those that the
   compiler kept of a unit in its .cmx file when it compiled it, for every .cmx
   file of the directory: the type of every symbol and of every variable of the
   unit that the file has, read as Simplify reads them when it compiles a unit
   that uses that one. What is printed for a unit is a line: its symbols, its
   variables, and the types that the model has; and at the end, with the counts
   of the comparisons, how many of the types are what at their top. A file that
   has no types is a unit that is not read, and is counted so.

   A run on one input that stops, by a fatal error or an exception, is a line
   for that input and is counted; the tool then fails, with another status than
   for a disagreement.

   With [-tops], a control of what is counted at the top of a type. *)

open Flambda2_identifiers
open Flambda2_kinds
open Flambda2_parser
open Flambda2_term_basics
open Flambda2_terms
open Type_comparisons
module K = Flambda_kind
module TG = Flambda2_types__Type_grammar
module TE = Flambda2_types__Typing_env
module TEL = Flambda2_types__Typing_env_level
module MT = Flambda2_rocq_semantics.FlambdaTypeGrammar
module Converter = Flambda2_rocq_types_converter.Type_converter
module Model_names = Flambda2_rocq_types_converter.Model_names
module N = Flambda2_rocq_types_converter.Model_numbers
module Model_type = Flambda2_rocq_types_converter.Model_type

(* ======================================================================== *)
(* What an environment knows                                                *)
(* ======================================================================== *)

(* The names that an environment knows, with their kinds: the variables that its
   levels define and the symbols that it defines. *)
let names_of (env : TE.t) : (Name.t * K.t) list =
  let level = TE.cut env ~cut_after:Scope.initial in
  List.map
    (fun (variable, kind) -> Name.var variable, kind)
    (Variable.Map.bindings (TEL.defined_variables_with_kinds level))
  @ List.map
      (fun symbol -> Name.symbol symbol, K.value)
      (Symbol.Set.elements (TE.defined_symbols env))

(* ======================================================================== *)
(* An extension within an extension                                         *)
(* ======================================================================== *)

(* The environment extensions of a type that are not inside another one: those
   of its variants and of the cases of its row-like structures, in the fields,
   the contents and the slots too. *)
let rec extensions (t : MT.flambda_type) : MT.env_extension list =
  let of_block_case (case : MT.row_like_block_case) =
    case.case_env_extension :: List.concat_map extensions case.case_maps_to
  in
  let of_head (head : MT.head_of_kind_value_non_null) =
    match head with
    | Variant (_, immediates, _, blocks, variant_extensions, _) -> (
      (match immediates with Known t -> extensions t | Unknown -> [])
      @ (match blocks with
        | Unknown -> []
        | Known (Row_like_for_blocks (known_tags, other_tags, _)) ->
          (match other_tags with Ok case -> of_block_case case | Bottom -> [])
          @ List.concat_map
              (fun (_, (case : _ MT.Or_unknown.t)) ->
                match case with
                | Known case -> of_block_case case
                | Unknown -> [])
              known_tags)
      @
      match variant_extensions with
      | No_extensions -> []
      | Ext (when_immediate, when_block) -> [when_immediate; when_block])
    | Mutable_block _ | String _ -> []
    | Boxed_number (_, contents, _) -> extensions contents
    | Closures (Row_like_for_closures cases, _) ->
      List.concat_map
        (fun (_, (case : (_, _, _, _) MT.row_like_case)) ->
          let (Closures_entry (_, closure_types, value_slot_types)
                : MT.closures_entry) =
            case.case_maps_to
          in
          case.case_env_extension
          :: List.concat_map
               (fun (_, t) -> extensions t)
               (closure_types @ value_slot_types))
        cases
  in
  match t with
  | Type_value (Ok (No_alias (Head_of_kind_value (non_null, _)))) -> (
    match non_null with Ok head -> of_head head | Unknown | Bottom -> [])
  | Type_value (Unknown | Bottom | Ok (Equals _))
  | Type_naked_immediate _ | Type_naked_number _ | Type_rec_info _
  | Type_region _ ->
    []

(* Whether some extension of a type gives a name a type that has, at any depth,
   an extension on that same name: the shape on which the compiler's equality of
   types does not terminate (T7-2). *)
let rec extension_on_a_name_within_one_on_it (t : MT.flambda_type) : bool =
  let rec has_extension_on name (t : MT.flambda_type) =
    List.exists
      (fun (Env_extension equations : MT.env_extension) ->
        List.mem_assoc name equations
        || List.exists (fun (_, t) -> has_extension_on name t) equations)
      (extensions t)
  in
  List.exists
    (fun (Env_extension equations : MT.env_extension) ->
      List.exists
        (fun (name, t) ->
          has_extension_on name t || extension_on_a_name_within_one_on_it t)
        equations)
    (extensions t)

(* ======================================================================== *)
(* The counts                                                               *)
(* ======================================================================== *)

(* Counts by what is counted, shown in the order in which each was first
   counted. *)
type counts =
  { mutable order : string list;
    table : (string, int) Hashtbl.t
  }

let create_counts () = { order = []; table = Hashtbl.create 16 }

let count counts what =
  match Hashtbl.find_opt counts.table what with
  | Some n -> Hashtbl.replace counts.table what (n + 1)
  | None ->
    counts.order <- what :: counts.order;
    Hashtbl.replace counts.table what 1

let print_counts counts =
  List.iter
    (fun what ->
      Format.printf "  %d %s@." (Hashtbl.find counts.table what) what)
    (List.rev counts.order)

(* ======================================================================== *)
(* One unit                                                                 *)
(* ======================================================================== *)

let observations : (TE.t * Continuation.t) list ref = ref []

(* The observer only keeps what it is given. *)
let observe env continuation =
  observations := (env, continuation) :: !observations

(* The unit of a file, simplified, or why there is none. Simplify may stop on a
   unit, with a fatal error or at an assertion: some of the units of the
   semantics tests are there to show it. *)
let simplify filename : (Flambda_unit.t, string) result =
  match Parse_flambda.parse_fexpr filename with
  | Error _ -> Error "not read: the parser refuses it"
  | Ok fexpr -> (
    let unit_info = Parse_flambda.make_unit_info ~filename in
    Env.set_current_unit unit_info;
    let converted = Fexpr_to_flambda.conv (Unit_info.modname unit_info) fexpr in
    let null_formatter =
      Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
    in
    TE.For_testing.set_observer (Some observe);
    let result =
      or_fatal_error (fun () ->
          match
            Flambda2.flambda_to_flambda ~ppf_dump:null_formatter
              ~prefixname:(Filename.chop_extension filename)
              ~machine_width ~code_slot_offsets:converted.code_slot_offsets
              converted.unit
          with
          | result -> Ok result.flambda
          | exception Assert_failure (file, _, _) ->
            Error
              ("not simplified: an assertion of " ^ Filename.basename file
             ^ " fails"))
    in
    TE.For_testing.set_observer None;
    match result with
    | Ok result -> result
    | Error line -> Error ("not simplified: a fatal error: " ^ general line))

(* The counts of one file are written to a file, a count and what is counted on
   each line, for the run that goes through all the files. *)
let write_counts counts path =
  let channel = open_out path in
  List.iter
    (fun what ->
      Printf.fprintf channel "%d %s\n" (Hashtbl.find counts.table what) what)
    (List.rev counts.order);
  close_out channel

let add_counts totals path =
  let channel = open_in path in
  let rec read () =
    match input_line channel with
    | line ->
      (match String.index_opt line ' ' with
      | Some i ->
        let n = int_of_string (String.sub line 0 i) in
        let what = String.sub line (i + 1) (String.length line - i - 1) in
        for _ = 1 to n do
          count totals what
        done
      | None -> ());
      read ()
    | exception End_of_file -> close_in channel
  in
  read ()

(* What a type is at its top, for the counts. A head that may be null has a
   variable for whether it is, which holds a relation, or has none: the two are
   counted apart. *)
let top_of_a_type (t : MT.flambda_type) : string =
  match t with
  | Type_value Unknown -> "unknown"
  | Type_value Bottom -> "bottom"
  | Type_value (Ok (Equals (Symbol _))) -> "an alias of a symbol"
  | Type_value (Ok (Equals (Var _))) -> "an alias of a variable"
  | Type_value (Ok (Equals (Const _))) -> "a constant"
  | Type_value (Ok (No_alias (Head_of_kind_value (non_null, is_null)))) -> (
    let or_null what =
      match is_null with
      | Not_null -> what
      | Maybe_null None -> what ^ ", or null"
      | Maybe_null (Some _) ->
        what ^ ", or null, with a variable for whether it is null"
    in
    match non_null with
    | Unknown -> or_null "any value that is not null"
    | Bottom -> (
      match is_null with
      | Not_null -> "no value"
      | Maybe_null None -> "null"
      | Maybe_null (Some _) -> "null, with a variable for whether it is null")
    | Ok (Variant _) -> or_null "a variant"
    | Ok (Mutable_block _) -> or_null "a mutable block"
    | Ok (Boxed_number _) -> or_null "a boxed number"
    | Ok (Closures _) -> or_null "closures"
    | Ok (String _) -> or_null "a string")
  | Type_naked_immediate _ -> "a naked immediate"
  | Type_naked_number _ -> "a naked number"
  | Type_rec_info _ -> "a rec_info"
  | Type_region _ -> "a region"

(* A control of what is counted at the top of a type, on the four types that say
   least of a value: the unknown type, and the heads of which the part that is
   not null is unknown, which is not null, may be null, or may be null with a
   variable for whether it is. The four are to be counted apart. *)
let control_of_the_tops () =
  let head is_null : MT.flambda_type =
    Type_value (Ok (No_alias (Head_of_kind_value (Unknown, is_null))))
  in
  let types : (string * MT.flambda_type) list =
    [ "the unknown type", Type_value Unknown;
      "a head that is not null, of which no more is known", head Not_null;
      ( "a head that may be null, with no variable for whether it is",
        head (Maybe_null None) );
      ( "a head that may be null, with a variable for whether it is",
        head (Maybe_null (Some (N.positive_of_int 1))) ) ]
  in
  Format.printf
    "A control: what is counted at the top of the types that say least of a \
     value@.";
  List.iter
    (fun (what, t) -> Format.printf "  %s: %s@." what (top_of_a_type t))
    types;
  let tops = List.map (fun ((_ : string), t) -> top_of_a_type t) types in
  let apart =
    List.length (List.sort_uniq String.compare tops) = List.length tops
  in
  Format.printf "  the four are counted apart: %s@.@."
    (if apart then "yes" else "NO");
  if not apart then exit 1

(* A disagreement: the comparison, what it says, and the type. *)
type disagreement = string * string * MT.flambda_type

(* The environments of a unit, each with the names that are asked of it: each
   type of a name that was not seen before is compared. The disagreements are
   returned, in the order in which they were found. What the types are at their
   top is counted where [tops] says so. *)
let check_environments ~(tops : bool) (counts : counts)
    (environments : (TE.t * (Name.t * K.t) list) list) : disagreement list =
  let count = count counts in
  let numbering = Model_names.create () in
  (* The types of each name that were compared already. Two types are the same
     one for the compiler's structural equality, and not for how they are
     printed, which leaves things out. *)
  let seen : TG.t list Name.Map.t ref = ref Name.Map.empty in
  let seen_already name t =
    let types = Option.value (Name.Map.find_opt name !seen) ~default:[] in
    List.exists (TG.equal t) types
    ||
    (seen := Name.Map.add name (t :: types) !seen;
     false)
  in
  let found = ref [] in
  List.iter
    (fun (env, names) ->
      let comparisons =
        comparisons_of_one_type numbering
        @ comparisons_of_what_is_dropped numbering
        @ round_trip_from_the_compiler numbering env
        @ [ { name = "type_well_formed";
              compare = (fun { model; compiler = _ } -> well_formed [model])
            } ]
      in
      List.iter
        (fun (name, kind) ->
          count "names in the environments";
          let t = TE.find env name (Some kind) in
          if not (seen_already name t)
          then (
            count "different types of a name";
            match Converter.type_to_model_with_what_is_dropped numbering t with
            | exception Converter.Not_in_the_model what ->
              count ("not in the model: " ^ general what)
            | model, (dropped : Converter.dropped) ->
              count "in the model";
              if tops then count ("at its top, " ^ top_of_a_type model);
              if
                List.exists
                  (fun ((_ : Code_id.t), rec_info) ->
                    not (TG.is_obviously_unknown rec_info))
                  dropped.rec_infos
              then
                count
                  "with a function type that has a rec_info, which is put back \
                   for the round trip from the compiler";
              (match Model_type.extension_depth model with
              | 0 -> ()
              | 1 -> count "with an extension"
              | _ ->
                count "with an extension within an extension";
                if extension_on_a_name_within_one_on_it model
                then count "with an extension on a name inside one on it");
              List.iter
                (fun { name = comparison; compare } ->
                  match guarded compare { model; compiler = t } with
                  | Not_this_comparison -> ()
                  | Agree -> count (comparison ^ ": agree")
                  | Not_run reason ->
                    count (comparison ^ ": not run, " ^ general reason)
                  | Known_to_disagree (label, _) ->
                    count (comparison ^ ": as recorded, " ^ label)
                  | Disagree what ->
                    count (comparison ^ ": DISAGREE");
                    found := (comparison, what, model) :: !found)
                comparisons))
        names)
    environments;
  List.rev !found

let number (counts : counts) what =
  Option.value (Hashtbl.find_opt counts.table what) ~default:0

(* The disagreements of a unit, shown in full under its line. Their number is
   returned. *)
let print_disagreements (disagreements : disagreement list) : int =
  List.iter
    (fun (comparison, what, model) ->
      Format.printf "  @[<v>DISAGREEMENT, %s: %s@ on the type@ %a@]@."
        comparison what Model_type.print model)
    disagreements;
  List.length disagreements

(* One file: its counts are returned with the number of its disagreements. *)
let check_file filename : counts * int =
  let shown = Filename.basename filename in
  let counts = create_counts () in
  let count = count counts in
  observations := [];
  match simplify filename with
  | Error why ->
    count "units not simplified";
    Format.printf "%s: %s@." shown why;
    counts, 0
  | Ok unit ->
    count "units simplified";
    let return_continuation = Flambda_unit.return_continuation unit in
    let at_end, at_handlers =
      List.partition
        (fun (_, continuation) ->
          Continuation.equal continuation return_continuation)
        (List.rev !observations)
    in
    List.iter
      (fun _ -> count "environments at the start of a handler")
      at_handlers;
    List.iter (fun _ -> count "environments at the end of a unit") at_end;
    let environments = at_handlers @ at_end in
    let disagreements =
      check_environments ~tops:false counts
        (List.map
           (fun (env, (_ : Continuation.t)) -> env, names_of env)
           environments)
    in
    Format.printf
      "%s: %d environments, %d names, %d different types of a name, %d in the \
       model@."
      shown (List.length environments)
      (number counts "names in the environments")
      (number counts "different types of a name")
      (number counts "in the model");
    counts, print_disagreements disagreements

(* ======================================================================== *)
(* One unit of the standard library                                         *)
(* ======================================================================== *)

(* What the compiler kept of a unit in its .cmx file, as an environment: the one
   that Simplify starts from when it compiles another unit, in which a name of
   the unit is looked up in what its file has. With it, the symbols and the
   variables of the unit that the file says it has, each with its kind: a symbol
   is of kind value. The load path and the current unit, which is another one,
   are set by the caller. *)
let environment_of_cmx (unit_name : string) :
    (TE.t * (Name.t * K.t) list * (Name.t * K.t) list, string) result =
  let unit = Compilation_unit.of_string unit_name in
  let loader =
    Flambda2_cmx.Flambda_cmx.create_loader
      ~get_module_info:Flambda2.get_module_info
  in
  let resolver = Flambda2_cmx.Flambda_cmx.load_cmx_file_contents loader in
  match resolver unit with
  | None -> Error "not read: no .cmx file, or one that has no types"
  | Some serializable -> (
    let module Exported = Flambda2_types.Typing_env in
    let ids = Exported.Serializable.ids_for_export serializable in
    observations := [];
    TE.For_testing.set_observer (Some observe);
    Exported.notify_test_observer
      (Exported.create ~machine_width ~resolver)
      ~at_handler:(Continuation.create ());
    TE.For_testing.set_observer None;
    match !observations with
    | [(env, (_ : Continuation.t))] ->
      let of_the_unit compilation_unit =
        Compilation_unit.equal compilation_unit unit
      in
      Ok
        ( env,
          List.filter_map
            (fun symbol ->
              if of_the_unit (Symbol.compilation_unit symbol)
              then Some (Name.symbol symbol, K.value)
              else None)
            (Symbol.Set.elements ids.symbols),
          List.filter_map
            (fun variable ->
              if of_the_unit (Variable.compilation_unit variable)
              then Some (Name.var variable, Variable.kind variable)
              else None)
            (Variable.Set.elements ids.variables) )
    | [] | _ :: _ :: _ -> Error "not read: the observer was not called once")

let check_cmx unit_name : counts * int =
  let counts = create_counts () in
  let count = count counts in
  match environment_of_cmx unit_name with
  | Error why ->
    count "units not read";
    Format.printf "%s: %s@." unit_name why;
    counts, 0
  | Ok (env, symbols, variables) ->
    count "units read";
    List.iter (fun _ -> count "symbols of a unit in its .cmx file") symbols;
    List.iter (fun _ -> count "variables of a unit in its .cmx file") variables;
    let disagreements =
      check_environments ~tops:true counts [env, symbols @ variables]
    in
    Format.printf "%s: %d symbols, %d variables, %d in the model@." unit_name
      (List.length symbols) (List.length variables)
      (number counts "in the model");
    counts, print_disagreements disagreements

(* The compiler keeps what it knows of a unit when it goes on to another one in
   the same run, and then fails on units that it simplifies when they come
   first. So each file, or each unit of a directory, is gone through in a run of
   its own: this program runs itself on each, and adds up the counts that each
   run writes. A run that stops is a line for its input, and is counted: the
   tool then ends with status 3, where no input has a disagreement, so that a
   rule which expects no such run fails. *)
let each_in_a_run_of_its_own ~(one : string list) ~(shown : string -> string)
    ~(they : string) (inputs : string list) =
  let totals = create_counts () in
  let with_disagreements = ref 0 in
  List.iter
    (fun input ->
      let counts_file = Filename.temp_file "types_of_compilations" ".counts" in
      match
        Sys.command
          (Filename.quote_command Sys.executable_name
             (one @ [counts_file; input]))
      with
      | (0 | 1) as status ->
        if status = 1 then incr with_disagreements;
        add_counts totals counts_file;
        Sys.remove counts_file
      | status ->
        count totals "units on which this tool stopped";
        Format.printf "%s: this tool stopped with status %d@." (shown input)
          status)
    inputs;
  Format.printf "@.In all:@.";
  print_counts totals;
  let stopped = number totals "units on which this tool stopped" in
  Format.printf "@.%s@."
    (if !with_disagreements > 0
     then Printf.sprintf "DISAGREEMENTS in %d %s." !with_disagreements they
     else if stopped > 0
     then
       Printf.sprintf
         "No disagreement in the %s gone through; this tool stopped on %d." they
         stopped
     else "No disagreement.");
  if !with_disagreements > 0 then exit 1;
  if stopped > 0 then exit 3

let () =
  match Array.to_list Sys.argv with
  | [_; "-one"; counts_file; filename] ->
    Clflags.set_target Clflags.Target.Native;
    (* So that the parameter of a handler with several uses is given the join of
       its arguments, and not the unknown type. *)
    Oxcaml_flags.Flambda2.join_points := Oxcaml_flags.Set true;
    (* The model has no physical equality: the joins are those of the structural
       setting of the flag for sharing, as in types_difftest.ml. *)
    Oxcaml_flags.Flambda2.join_sharing
      := Oxcaml_flags.Set Oxcaml_flags.Structural;
    let counts, disagreements = check_file filename in
    write_counts counts counts_file;
    if disagreements > 0 then exit 1
  | [_; "-one-cmx"; directory; counts_file; unit_name] ->
    Clflags.set_target Clflags.Target.Native;
    Load_path.init ~auto_include:Load_path.no_auto_include ~visible:[]
      ~hidden:[directory];
    Env.set_current_unit
      (Unit_info.make_dummy ~input_name:"types_of_compilations"
         (Compilation_unit.of_string "Types_of_compilations"));
    let counts, disagreements = check_cmx unit_name in
    write_counts counts counts_file;
    if disagreements > 0 then exit 1
  | [_; "-tops"] -> control_of_the_tops ()
  | [] | [_] | [_; "-cmx"] ->
    prerr_endline
      "usage: types_of_compilations FILE.fl ..., or types_of_compilations -cmx \
       DIRECTORY, or types_of_compilations -tops";
    exit 2
  | [_; "-cmx"; directory] ->
    (* The units of the .cmx files of the directory, in the order of their
       names. *)
    let units =
      Sys.readdir directory |> Array.to_list
      |> List.filter_map (fun file ->
          if Filename.check_suffix file ".cmx"
          then Some (String.capitalize_ascii (Filename.chop_suffix file ".cmx"))
          else None)
      |> List.sort String.compare
    in
    Format.printf
      "The types that the compiler kept of the units of a directory in their \
       .cmx files, against the Rocq model.@.@.";
    each_in_a_run_of_its_own ~one:["-one-cmx"; directory] ~shown:Fun.id
      ~they:"units" units
  | _ :: filenames ->
    Format.printf
      "The types that Simplify computes for the units of the semantics tests, \
       against the Rocq model.@.@.";
    each_in_a_run_of_its_own ~one:["-one"] ~shown:Filename.basename
      ~they:"files" filenames
