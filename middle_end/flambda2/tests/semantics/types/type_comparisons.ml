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

(* What the tests of types share: how a comparison is run and reported, and the
   comparisons of one type, each function that the model has of a type against
   the compiler's.

   A comparison is given an input and says whether the two sides agree. [run]
   runs each comparison of a list on inputs generated from seeds, counts the
   outcomes, and shows every disagreement with the seed of its case and a shrunk
   input; a tool that has its own inputs (the types that Simplify computes)
   calls the comparisons itself. *)

open Flambda2_identifiers
open Flambda2_kinds
open Flambda2_nominal
module TG = Flambda2_types__Type_grammar
module TE = Flambda2_types__Typing_env
module Equal = Flambda2_types__Equal_types_for_debug
module Binary = Flambda2_types__Meet_and_join
module M = Flambda2_rocq_semantics.FlambdaModel
module MT = Flambda2_rocq_semantics.FlambdaTypeGrammar
module Well_formed = Flambda2_rocq_semantics.FlambdaTypeWellFormedSpec
module Converter = Flambda2_rocq_types_converter.Type_converter
module Model_names = Flambda2_rocq_types_converter.Model_names
module Model_type = Flambda2_rocq_types_converter.Model_type
module N = Flambda2_rocq_types_converter.Model_numbers
module Random = Minicheck.Splittable_random

let machine_width = Target_system.Machine_width.Sixty_four

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

(* A result that differs when arguments are shared and when they are not: with
   the compiler's default it is recorded (T7-7); with the structural setting
   nothing is to depend on sharing, and it is a failure. *)
type sharing =
  | Default_sharing
  | Structural_sharing

let depends_on_sharing (sharing : sharing) what : outcome =
  match sharing with
  | Default_sharing ->
    Known_to_disagree ("T7-7, a result that depends on sharing", what)
  | Structural_sharing -> Disagree what

(* A variable that a type given by the compiler mentions and the environment
   given with it does not define. *)
exception Not_defined of string

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
  | exception Not_defined what ->
    Disagree (what ^ " is in a type and the environment does not define it")

(* A reason without what is particular to one case (numbers, names), so that
   reasons can be counted. *)
let general reason =
  let digit c = c >= '0' && c <= '9' in
  let zeros = String.map (fun c -> if digit c then '0' else c) reason in
  String.concat "N"
    (List.filter
       (fun part -> not (String.equal part ""))
       (String.split_on_char '0' zeros))

(* What the compiler does where it may stop with a fatal error. It writes what
   the error is about on the standard error before it raises: that is taken from
   there, and kept out of the log. *)
let or_fatal_error f : (_, string) result =
  let out = Format.pp_get_formatter_out_functions Format.err_formatter () in
  let written = Buffer.create 80 in
  Format.pp_print_flush Format.err_formatter ();
  Format.pp_set_formatter_out_functions Format.err_formatter
    { out with
      out_string = Buffer.add_substring written;
      out_newline = (fun () -> Buffer.add_char written '\n');
      out_spaces = (fun n -> Buffer.add_string written (String.make n ' '));
      out_indent = ignore
    };
  let restore () =
    Format.pp_print_flush Format.err_formatter ();
    Format.pp_set_formatter_out_functions Format.err_formatter out
  in
  match f () with
  | result ->
    restore ();
    Ok result
  | exception Misc.Fatal_error ->
    restore ();
    (* The first line is the error; the context of the compiler may follow. *)
    let first_line =
      match String.split_on_char '\n' (Buffer.contents written) with
      | line :: _ -> String.trim line
      | [] -> ""
    in
    let prefix = ">> Fatal error: " in
    let length = String.length prefix in
    Error
      (if
         String.length first_line >= length
         && String.equal (String.sub first_line 0 length) prefix
       then String.sub first_line length (String.length first_line - length)
       else first_line)

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

let agree_if condition what = if condition then Agree else Disagree what

(* The variables of [Type_grammar.free_names], as numbers. *)
let free_variables_of_compiler (numbering : Model_names.t) (t : TG.t) :
    M.variable list =
  Name_occurrences.fold_variables (TG.free_names t) ~init:[]
    ~f:(fun variables var ->
      Converter.variable_to_model numbering var :: variables)

(* Those of kind [Rec_info]. The model has not got the expression of a
   [Rec_info] head nor the [rec_info] of a function type, so a variable of that
   kind that the compiler's type mentions there is not in the model's type. *)
let free_depth_variables_of_compiler (numbering : Model_names.t) (t : TG.t) :
    M.variable list =
  Name_occurrences.fold_variables (TG.free_names t) ~init:[]
    ~f:(fun variables var ->
      if Flambda_kind.equal (Variable.kind var) Flambda_kind.rec_info
      then Converter.variable_to_model numbering var :: variables
      else variables)

(* A printed type of the compiler without the [rec_info] of its function types,
   which the model has not got: each is shown as [(rec_info _)]. *)
let without_rec_info (printed : string) : string =
  let opening = "(rec_info " in
  let length = String.length printed in
  let buffer = Buffer.create length in
  let starts_at i =
    i + String.length opening <= length
    && String.equal (String.sub printed i (String.length opening)) opening
  in
  (* The position after the bracket that closes the one opened at [i]. *)
  let rec closing i depth =
    if i >= length
    then length
    else
      match printed.[i] with
      | '(' -> closing (i + 1) (depth + 1)
      | ')' -> if depth = 1 then i + 1 else closing (i + 1) (depth - 1)
      | _ -> closing (i + 1) depth
  in
  let rec copy i =
    if i < length
    then
      if starts_at i
      then (
        Buffer.add_string buffer "(rec_info _)";
        copy (closing i 0))
      else (
        Buffer.add_char buffer printed.[i];
        copy (i + 1))
  in
  copy 0;
  Buffer.contents buffer

(* A type of the model with the type of the compiler made from it. *)
type both =
  { model : MT.flambda_type;
    compiler : TG.t
  }

(* Each function of one type that the model has, against the compiler's. *)
let comparisons_of_one_type (numbering : Model_names.t) : both comparison list =
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
  (* The variables of the model's type against those of the compiler's: the same
     ones, or if not [exact] at least those of the compiler's. A variable of
     kind [Rec_info] that only the compiler's type has is in what the model has
     not got: the case is then not run, and counted so. *)
  let free_variables name of_model ~exact =
    { name;
      compare =
        (fun { model; compiler } ->
          let of_model = of_model model in
          let of_compiler = free_variables_of_compiler numbering compiler in
          let only_of_compiler =
            List.filter (fun x -> not (List.mem x of_model)) of_compiler
          in
          let only_of_model =
            List.filter (fun x -> not (List.mem x of_compiler)) of_model
          in
          let depth_variables =
            free_depth_variables_of_compiler numbering compiler
          in
          match only_of_compiler, only_of_model with
          | [], [] -> Agree
          | [], _ :: _ when not exact -> Agree
          | _ :: _, ([] | _ :: _)
            when List.for_all
                   (fun x -> List.mem x depth_variables)
                   only_of_compiler
                 && ((not exact)
                    || match only_of_model with [] -> true | _ :: _ -> false) ->
            Not_run
              "the compiler's type mentions a variable of kind Rec_info where \
               the model has not got the expression"
          | ([] | _ :: _), ([] | _ :: _) ->
            Disagree
              (Format.asprintf "the model answers %a, the compiler %a"
                 print_variables of_model print_variables of_compiler))
    }
  in
  [ { name = "the round trip from the model (to the compiler and back)";
      compare =
        (fun { model; compiler } ->
          let back = Converter.type_to_model numbering compiler in
          agree_if
            (Model_type.same model back)
            (Format.asprintf "the type comes back as %a" Model_type.print back))
    };
    on_both "kind" MT.kind
      (fun t -> Converter.kind_to_model (TG.kind t))
      Stdlib.( = ) Model_type.print_kind;
    on_both "get_alias_opt" MT.get_alias_opt
      (fun t ->
        Option.map (Converter.simple_to_model numbering) (TG.get_alias_opt t))
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
    free_variables
      "free_variables against free_names, without shadowed bindings"
      (fun m -> MT.free_variables (Model_type.normalise m))
      ~exact:true;
    free_variables "free_variables includes free_names, with shadowed bindings"
      MT.free_variables ~exact:false ]

(* [type_well_formed] of FlambdaTypeWellFormedSpec.v is meant to be true of
   every type that the compiler builds, whatever the program. Whether it is true
   of a type of the compiler is asked of the type that the converter gives for
   it.

   The generator is not held to it: it makes types that a creation function of
   the compiler would not (a case of blocks of an exact size with fewer types, a
   set of closures with no function type for one of its closures), which the
   functions that the converter builds with accept. So what is asked is that the
   predicate is kept: by the conversion, and by a meet or a join of types of
   which it is true. *)
let is_well_formed = Well_formed.type_well_formed

(* [Agree] if the predicate is true of every type given. *)
let well_formed (types : MT.flambda_type list) : outcome =
  match List.find_opt (fun t -> not (is_well_formed t)) types with
  | None -> Agree
  | Some t ->
    Disagree
      (Format.asprintf "type_well_formed is false of@ %a" Model_type.print t)

(* The predicate is the same of a type and of what the compiler makes of it. A
   map of the compiler binds a key once, so the type of the model is taken with
   its maps written in one way. *)
let well_formed_types (numbering : Model_names.t) : both comparison list =
  [ { name = "type_well_formed of a type, and of what the compiler makes of it";
      compare =
        (fun { model; compiler } ->
          let of_model = is_well_formed (Model_type.normalise model) in
          let back = Converter.type_to_model numbering compiler in
          let of_compiler = is_well_formed back in
          agree_if
            (Bool.equal of_model of_compiler)
            (Format.asprintf
               "it is %b of the type and %b of what the compiler makes of it:@ \
                %a"
               of_model of_compiler Model_type.print back))
    };
    { name = "the types of which type_well_formed is true";
      compare =
        (fun { model; compiler = _ } ->
          if is_well_formed (Model_type.normalise model)
          then Agree
          else Not_run "it is false of the type")
    } ]

(* The round trip from the compiler: a type of the compiler, to the model and
   back, is the same type for the compiler's own equality
   ([Equal_types_for_debug], allocation modes included) and is printed the same.
   Where the two differ only in the [rec_info] of a function type, which the
   converter drops and makes unknown on the way back, the case is not run, and
   counted so: a type made from a type of the model never has one, and a type
   that Simplify computes may. *)
let round_trip_from_the_compiler (numbering : Model_names.t) (env : TE.t) :
    both comparison list =
  let back t =
    Converter.type_of_model numbering machine_width
      (Converter.type_to_model numbering t)
  in
  let differ_in_rec_info_only t t' =
    let printed = print_compiler_type t and printed' = print_compiler_type t' in
    (not (String.equal printed printed'))
    && String.equal (without_rec_info printed) (without_rec_info printed')
  in
  let differs_in_rec_info =
    "the type has a function type with a rec_info, which the model has not got"
  in
  [ { name = "the round trip from the compiler, as printed";
      compare =
        (fun { model = _; compiler } ->
          let back = back compiler in
          if
            String.equal
              (print_compiler_type compiler)
              (print_compiler_type back)
          then Agree
          else if differ_in_rec_info_only compiler back
          then Not_run differs_in_rec_info
          else Disagree ("the type comes back as " ^ print_compiler_type back))
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
                ~meet_expanded_head:Binary.meet_expanded_head env compiler back
            in
            if equal
            then Agree
            else if differ_in_rec_info_only compiler back
            then Not_run differs_in_rec_info
            else
              let back = print_compiler_type back in
              Disagree ("the type comes back as " ^ back))
    } ]
