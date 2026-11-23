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

(* A control of what a program that links flsemantics.ml may ask of it and its
   command line may not: [set] of the numbering of names, the reference
   [poison_missing_callee], and the refusal of the checks while that reference
   is set. Nothing else in this tree asks them. What this prints, on its two
   outputs, is compared with ../semantics/linking_program/control.expected.

   The numbering is asked of an instance of the functor made here, on names that
   are strings, and of the instance of the value slots. The conversion and the
   checks are asked of units read from the texts of that directory, which are
   given as arguments, each read once: the compiler keeps the symbols of a unit
   from one unit to the next. Two of the texts, of a call of a C function and of
   a call of a method with no callee, are of calls that the compiler does not
   make ([Apply_expr.invariant]): what is shown of them is that the reader is
   refused. A fatal error of flsemantics.ml writes its words on the error output
   before it is raised: they are in the stored file, each above the line that
   says what was refused. *)

(* The matches below name the constructors that the control is about and take
   the others together. *)
[@@@ocaml.warning "-4"]

open Import
module Model = Flambda2_rocq_semantics.FlambdaModel
module Numbers = Flambda2_rocq_library.BinNums
module S = Flsemantics

let say fmt = Format.printf (fmt ^^ "@.")

(* Whether what is asked is refused by a fatal error. Another exception is not
   caught. *)
let refuses (ask : unit -> unit) =
  match ask () with exception Misc.Fatal_error -> true | () -> false

let yes_or_no b = if b then "yes" else "NO"

(* ---- The numbering ----------------------------------------------------- *)

module Names = S.Numbering (String)

let shown (number : Numbers.positive) =
  match S.number_of_positive number with
  | None -> "greater than the numbers of names"
  | Some n ->
    if n = S.last_number
    then "the last number"
    else if n = S.last_number - 1
    then "the last number but one"
    else string_of_int n

let name_shown number =
  match Names.name_of number with None -> "none" | Some name -> name

let names () =
  String.concat ", "
    (List.map
       (fun (name, number) -> name ^ " " ^ shown number)
       (Names.bindings ()))

let of_int = S.positive_of_int

(* The positive that is one more than two to the power of the size of an [int]:
   [int_of_positive] makes 1 of it, which is the number of the name "first"
   below. *)
let too_great : Numbers.positive =
  let rec double times (p : Numbers.positive) : Numbers.positive =
    if times = 0 then p else double (times - 1) (Numbers.Coq_xO p)
  in
  Numbers.Coq_xI (double (Sys.int_size - 1) Numbers.Coq_xH)

let numbering () =
  say "THE NUMBERING OF NAMES";
  Names.reset ();
  let first = Names.find "first" in
  Names.set "a" (of_int 40);
  let a = Names.find "a" in
  let made = Names.fresh () in
  let b = Names.find "b" in
  say
    "find first = %s; set a 40: find a = %s; then fresh = %s; then find b = %s"
    (shown first) (shown a) (shown made) (shown b);
  Names.set "c" (of_int 5);
  let c = Names.find "c" in
  let made = Names.fresh () in
  say "set c 5, a number below: find c = %s; then fresh = %s" (shown c)
    (shown made);
  Names.set "b" (of_int 7);
  say "set b 7, where b had 42: find b = %s" (shown (Names.find "b"));
  Names.set "d" (of_int 40);
  let d = Names.find "d" in
  let a = Names.find "a" in
  say "set d 40, the number of a: find d = %s; find a = %s" (shown d) (shown a);
  let e = Names.find "e" in
  Names.set "f" e;
  say "find e = %s; set f to it: find f = %s; the name of that number: %s"
    (shown e)
    (shown (Names.find "f"))
    (name_shown e);
  Names.set "e" (of_int 9);
  say "set e 9: find e = %s; the name of 44: %s; the name of 9: %s"
    (shown (Names.find "e"))
    (name_shown (of_int 44))
    (name_shown (of_int 9));
  say
    "the name of 40, which set alone gave: %s; of 41, which fresh made: %s; of \
     42, which find gave to b: %s"
    (name_shown (of_int 40))
    (name_shown (of_int 41))
    (name_shown (of_int 42));
  say "the names: %s" (names ());
  (* Numbers that are refused, and what is left as it was. *)
  let before = names () in
  let refused = refuses (fun () -> Names.set "g" (of_int max_int)) in
  let same = String.equal before (names ()) in
  let made = Names.fresh () in
  say
    "set g to the greatest int: refused: %s; the names as they were: %s; then \
     fresh = %s"
    (yes_or_no refused) (yes_or_no same) (shown made);
  say "a positive of which int_of_positive makes %d: it is %s; its name: %s"
    (S.int_of_positive too_great)
    (shown too_great) (name_shown too_great);
  let refused = refuses (fun () -> Names.set "g" too_great) in
  let same = String.equal before (names ()) in
  let made = Names.fresh () in
  say "set g to it: refused: %s; the names as they were: %s; then fresh = %s"
    (yes_or_no refused) (yes_or_no same) (shown made);
  (* The last numbers. *)
  Names.set "y" (of_int (S.last_number - 1));
  let y = Names.find "y" in
  let made = Names.fresh () in
  say "set y to the last number but one: find y = %s; then fresh = %s" (shown y)
    (shown made);
  let before = names () in
  let no_fresh =
    refuses (fun () -> ignore (Names.fresh () : Numbers.positive))
  in
  let no_find =
    refuses (fun () -> ignore (Names.find "z" : Numbers.positive))
  in
  let no_alias = refuses (fun () -> Names.alias "w" ~same_as:"z") in
  let same = String.equal before (names ()) in
  say
    "then fresh: refused: %s; find of a new name: refused: %s; alias to a new \
     name: refused: %s; the names as they were: %s"
    (yes_or_no no_fresh) (yes_or_no no_find) (yes_or_no no_alias)
    (yes_or_no same);
  Names.set "x" (of_int S.last_number);
  say "set x to the last number: find x = %s; find a = %s"
    (shown (Names.find "x"))
    (shown (Names.find "a"));
  Names.reset ();
  let none = String.equal "" (names ()) in
  let a = Names.find "a" in
  say "reset: no name is left: %s; find a = %s; the name of 40: %s"
    (yes_or_no none) (shown a)
    (name_shown (of_int 40))

let unit_of_the_slot =
  Compilation_unit.create Compilation_unit.Prefix.empty
    (Compilation_unit.Name.of_string "Linking_program")

(* The instance of the value slots, which the conversion numbers. *)
let numbering_of_slots () =
  say "THE NUMBERING OF VALUE SLOTS";
  S.reset_conversion ();
  let slot name =
    Value_slot.create unit_of_the_slot ~name ~is_always_immediate:false
      Flambda2_kinds.Flambda_kind.value
  in
  let first = slot "first" and second = slot "second" in
  S.Value_slots.set first (of_int 12);
  let number = S.Value_slots.find first in
  let next = S.Value_slots.find second in
  say
    "set the first slot 12: find of it = %s; find of a second = %s; the name \
     of 12: %s; the name of 13: %s"
    (shown number) (shown next)
    (match S.Value_slots.name_of (of_int 12) with
    | None -> "none"
    | Some slot -> Value_slot.name slot)
    (match S.Value_slots.name_of (of_int 13) with
    | None -> "none"
    | Some slot -> Value_slot.name slot);
  S.reset_conversion ();
  say "reset_conversion: value slots numbered: %d"
    (List.length (S.Value_slots.bindings ()))

(* ---- The conversion ---------------------------------------------------- *)

let unit_of_text filename : Flambda_unit.t =
  match Parse_flambda.parse_fexpr filename with
  | Error e ->
    Test_utils.dump_error e;
    exit 2
  | Ok text -> (
    let unit_info = Parse_flambda.make_unit_info ~filename in
    Compilenv.reset unit_info;
    let read = Fexpr_to_flambda.conv (Unit_info.modname unit_info) text in
    match S.as_read_from_text read.unit with
    | Ok unit -> unit
    | Error why ->
      say "%s: %s" (Filename.basename filename) why;
      exit 2)

(* What is asked, with the reference set; the reference is unset afterwards,
   whatever is raised. *)
let with_the_reference_set ask =
  S.poison_missing_callee := true;
  Fun.protect ~finally:(fun () -> S.poison_missing_callee := false) ask

(* What the conversion makes of a unit: its term, or the words of its refusal.
   The refusal of a call for its kind prints the call after its first words,
   with the names that the compiler gave: the first words alone are shown. *)
let conversion unit : (S.converted, string) result =
  S.reset_conversion ();
  match S.convert_unit unit with
  | exception S.Unsupported what ->
    let words = Format.asprintf "%t" what in
    let first = "the call " in
    Error
      (if String.starts_with ~prefix:first words
       then first ^ "(the call is printed here)"
       else words)
  | converted -> Ok converted

let conversion_shown unit =
  match conversion unit with
  | Error words -> "refused, \"" ^ words ^ "\""
  | Ok _ -> "converted"

(* The calls of a term that are not in code. *)
let rec calls (e : Model.expr) : Model.apply_expr list =
  let in_handler (Model.Handler (_, _, handler)) = calls handler in
  match e with
  | Let (_, _, _, body) | Let_static (_, body) -> calls body
  | Let_cont_non_recursive (_, handler, body) -> in_handler handler @ calls body
  | Let_cont_recursive (handlers, body) ->
    List.concat_map (fun (_, handler) -> in_handler handler) handlers
    @ calls body
  | Apply apply -> [apply]
  | Apply_cont _ | Switch _ | Invalid -> []

let the_call (converted : S.converted) : Model.apply_expr =
  match calls converted.body with
  | [apply] -> apply
  | [] | _ :: _ :: _ ->
    say "NOT ONE CALL outside code";
    exit 2

let callee_shown (apply : Model.apply_expr) =
  match apply.ap_callee with
  | Const (Poison Value) -> "the poison constant of the kind of values"
  | Const _ -> "another constant"
  | Var _ -> "a variable"
  | Symbol _ -> "a symbol"

let run_shown (converted : S.converted) =
  let outcome, _ = S.run ~statics:(S.Imports.imports_statics []) converted in
  Format.asprintf "%a" S.print_outcome outcome

(* What is asked, with what it writes on the error formatter kept from the error
   output and given back, and whether it is refused by a fatal error. That is
   for a fatal error of the compiler whose words print a call as the compiler
   prints it. *)
let with_error_output_kept ask =
  let kept = Buffer.create 256 in
  let ppf = Format.err_formatter in
  Format.pp_print_flush ppf ();
  let functions = Format.pp_get_formatter_out_functions ppf () in
  Format.pp_set_formatter_out_functions ppf
    { functions with
      out_string = Buffer.add_substring kept;
      out_flush = (fun () -> ())
    };
  let refused =
    Fun.protect
      ~finally:(fun () ->
        Format.pp_print_flush ppf ();
        Format.pp_set_formatter_out_functions ppf functions)
      (fun () -> refuses ask)
  in
  refused, Buffer.contents kept

(* A text of a call that the compiler has not: the reader makes the call, and
   the compiler refuses to make it ([Apply_expr.invariant]). The first words of
   its fatal error are shown: the call is printed after them. *)
let no_such_call filename =
  let refused, words =
    with_error_output_kept (fun () ->
        ignore (unit_of_text filename : Flambda_unit.t))
  in
  let first_words =
    let before = ">> Fatal error: " in
    if String.starts_with ~prefix:before words
    then
      let from = String.length before in
      match String.index_from_opt words from ':' with
      | Some colon -> String.sub words from (colon - from)
      | None -> "(no colon)"
    else "(not the words of a fatal error)"
  in
  say "%s: read: refused by a fatal error: %s; its first words: %s"
    (Filename.basename filename)
    (yes_or_no refused) first_words

(* A call that the conversion refuses with the reference set as it does
   without. *)
let still_refused filename =
  let unit = unit_of_text filename in
  let unset = conversion_shown unit in
  let set = with_the_reference_set (fun () -> conversion_shown unit) in
  say "%s: with the reference unset: %s; set: %s"
    (Filename.basename filename)
    unset set

(* ---- The checks -------------------------------------------------------- *)

(* The names that the conversion has numbered. *)
let numbered () =
  List.length (S.Variables.bindings ())
  + List.length (S.Continuations.bindings ())
  + List.length (S.Symbols.bindings ())
  + List.length (S.Code_ids.bindings ())

(* The three checks of a unit against itself, with the reference unset: each
   reaches its work. *)
let checks_made ~filename unit =
  let units = S.units_read () in
  say "check:";
  (match S.check ~filename ~units unit unit with
  | Compared _ -> say "check: the two runs were made and compared"
  | Failed -> say "check: FAILED"
  | Not_checked -> say "check: not checked");
  say "check_or_raise:";
  (match S.check_or_raise ~filename ~units unit unit with
  | Some _ -> say "check_or_raise: a validation was asked"
  | None -> say "check_or_raise: not checked"
  | exception S.Check_failed -> say "check_or_raise: FAILED");
  S.reset_conversion ();
  S.check_regions ~units unit unit;
  say "check_regions: names that the conversion has numbered after it: %s"
    (if numbered () > 0 then "some" else "NONE")

(* The three checks of a unit against itself, with the reference set: each
   refuses before it does anything. *)
let checks_refused ~filename unit (converted : S.converted) =
  let units = S.units_read () in
  with_the_reference_set (fun () ->
      S.reset_conversion ();
      S.terms_compared := Some (converted, converted);
      S.regions_met := true;
      let refused =
        refuses (fun () ->
            ignore (S.check ~filename ~units unit unit : S.checked))
      in
      say "check: refused: %s" (yes_or_no refused);
      let refused =
        refuses (fun () ->
            ignore
              (S.check_or_raise ~filename ~units unit unit
                : S.Validate.validation option))
      in
      say "check_or_raise: refused: %s" (yes_or_no refused);
      let refused = refuses (fun () -> S.check_regions ~units unit unit) in
      say "check_regions: refused: %s" (yes_or_no refused);
      say
        "after the three: names that the conversion has numbered: %d; the \
         terms of the last comparison are still there: %s; the mark that \
         regions were met is still there: %s; regions are kept: %s"
        (numbered ())
        (yes_or_no (Option.is_some !S.terms_compared))
        (yes_or_no !S.regions_met)
        (if !S.keep_regions then "YES" else "no"));
  S.terms_compared := None;
  S.regions_met := false

let () =
  (* As the test tool does before it reads a text ([Flsemantics.main]). *)
  Misc.Style.setup (Some Misc.Color.Never);
  Clflags.set_target Clflags.Target.Native;
  S.init_load_path ();
  match Array.to_list Sys.argv with
  | [_; c_call; method_call; effect_call; probe; given; missing] ->
    numbering ();
    numbering_of_slots ();
    say "CALLS WITH NO CALLEE THAT THE COMPILER DOES NOT MAKE";
    List.iter no_such_call [c_call; method_call];
    say "CALLS THAT ARE REFUSED WITH THE REFERENCE SET AS WITHOUT IT";
    List.iter still_refused [effect_call; probe];
    say "A CALL THAT HAS A CALLEE";
    let unit = unit_of_text given in
    let given_name = Filename.basename given in
    let unset = conversion unit in
    let set = with_the_reference_set (fun () -> conversion unit) in
    let given_call =
      match unset, set with
      | Ok unset, Ok set ->
        say
          "%s: converted; with the reference set, to the same term: %s; its \
           callee: %s; its run: %s"
          given_name
          (yes_or_no (unset = set))
          (callee_shown (the_call unset))
          (run_shown unset);
        the_call unset
      | Error words, _ | _, Error words ->
        say "%s: REFUSED, \"%s\"" given_name words;
        exit 2
    in
    say "the checks of %s against itself, with the reference unset:" given_name;
    checks_made ~filename:given_name unit;
    say "A CALL OF A FUNCTION THAT HAS NO CALLEE";
    let unit = unit_of_text missing in
    let missing_name = Filename.basename missing in
    say "%s: with the reference unset: %s" missing_name (conversion_shown unit);
    let converted =
      with_the_reference_set (fun () ->
          S.reset_conversion ();
          say
            "with the reference set, after reset_conversion: the reference is \
             still set: %s"
            (yes_or_no !S.poison_missing_callee);
          match conversion unit with
          | Ok converted -> converted
          | Error words ->
            say "%s: with the reference set: REFUSED, \"%s\"" missing_name words;
            exit 2)
    in
    let call = the_call converted in
    say "%s: with the reference set: converted; its callee: %s" missing_name
      (callee_shown call);
    let same what yes =
      say "  %s as of the call of %s: %s" what given_name (yes_or_no yes)
    in
    same "the kind of the call" (call.ap_call_kind = given_call.ap_call_kind);
    same "the arguments" (call.ap_args = given_call.ap_args);
    same "the two arities"
      (call.ap_args_arity = given_call.ap_args_arity
      && call.ap_return_arity = given_call.ap_return_arity);
    same "the two continuations and the extra arguments"
      (call.ap_continuation = given_call.ap_continuation
      && call.ap_exn_continuation = given_call.ap_exn_continuation
      && call.ap_exn_extra_args = given_call.ap_exn_extra_args);
    say "the reference is unset again: %s"
      (yes_or_no (not !S.poison_missing_callee));
    say "the run of that term, by run, which is not guarded: %s"
      (run_shown converted);
    say "the checks of %s against itself, with the reference unset:"
      missing_name;
    checks_made ~filename:missing_name unit;
    say "the checks of %s against itself, with the reference set:" missing_name;
    checks_refused ~filename:missing_name unit converted;
    let raised =
      match with_the_reference_set (fun () -> raise Exit) with
      | exception Exit -> true
      | () -> false
    in
    say
      "what is asked with the reference set raises: %s; the reference is unset \
       again: %s"
      (yes_or_no raised)
      (yes_or_no (not !S.poison_missing_callee))
  | _ ->
    prerr_endline
      "linking_program_control: the six texts, in the order of the rule";
    exit 2
