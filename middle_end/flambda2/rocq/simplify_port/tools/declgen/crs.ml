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

(* THE QUESTIONS FOR A HUMAN that stand at the head of files of decl/. This file
   follows no file of the compiler.

   A row is a file of decl/, who is asked, the words, and what the words say of
   the file (below). The generator writes a row as ONE comment: the word CR, who
   is asked, a colon, the words. The comment stands under the header of the file
   (or under the words that stand in the place of a header) and before the
   comment GENERATED, with a blank line before it and after it. The generator
   fills the lines itself: the words are one string, and a break of line in it
   means nothing.

   THIS LIST IS THE ONLY PLACE WHERE THE WORDS ARE. To change a question, to add
   one or to take one away: change the list, then run tools/declgen/run.sh,
   which writes decl/ again.

   THE WORDS ARE WRITTEN BY HAND, and they name things of the file: the file
   whose notice it carries, what it declares. So that a question does not go on
   saying a thing that is no longer so, a row says the same things once more as
   data, and the generator compares them with what it is about to write: -
   [notice_of]: the file whose header the file of decl/ carries (the interface
   that it follows; for a file FILE__local, the file of Simplify); -
   [has_notice]: whether that file has a header; - [about]: what the file of
   decl/ declares. Names are those of OCaml, as the first column of
   decl/INDEX.tsv has them, and a name stands for itself and for all that is
   inside it (a module for its members). [All names]: every declaration of the
   file is one of these, and each of these is declared. [Of_library pairs]: the
   same, of the declarations whose place is a file of the standard library
   ([stdlib/] in the last column of decl/INDEX.tsv), each name with that file.
   If one of the three is not so, the words are to be read again and the row
   mended.

   The generator stops with an error, and writes no file, if two rows name one
   file, if a row names a file that it does not write, if what a row says of its
   file is not so, or if the words or the name have a comment mark or a double
   quote (in a comment of Rocq the first ends or opens a comment, the second
   opens a string). In a run on some of the files of Simplify
   (tools/declgen/run.sh with units) no question is written and no row is
   checked: such a run does not make the decl/ of the tree.

   Three tools read the files of decl/ line by line and would take a line of
   words for a sentence: tools/aliases.py, tools/declgen/check_realisations.py
   and tools/declgen/compile_all.py. Each leaves out such a comment, from the
   line that begins with the mark of a comment and then [CR] to the line that
   ends it. *)

type about =
  | All of string list
  | Of_library of (string * string) list

type row =
  { file : string;
    who : string;
    words : string;
    notice_of : string;
    has_notice : bool;
    about : about
  }

let rows =
  [ { file = "Dwarf_flags";
      who = "mshinwell";
      words =
        "The declaration of gdwarf_may_alter_codegen follows \
         backend/debug/dwarf/dwarf_flags/dwarf_flags.mli, which has no leading \
         notice; the donor-header rule supplies none. What notice should this \
         generated file carry?";
      notice_of = "backend/debug/dwarf/dwarf_flags/dwarf_flags.mli";
      has_notice = false;
      about = All ["Dwarf_flags.gdwarf_may_alter_codegen"]
    };
    { file = "Target_system";
      who = "mshinwell";
      words =
        "The is_32_bit and Machine_width declarations follow \
         utils/target_system.mli, which has no leading notice; the \
         donor-header rule supplies none. What notice should this generated \
         file carry?";
      notice_of = "utils/target_system.mli";
      has_notice = false;
      about = All ["Target_system.is_32_bit"; "Target_system.Machine_width"]
    };
    { file = "Numeric_types";
      who = "mshinwell";
      words =
        "The inherited Int32/Int64 declarations use the building OCaml's \
         standard-library names and types (stdlib/int32.mli and \
         stdlib/int64.mli counterparts). The donor rule keeps the notice of \
         middle_end/flambda2/numbers/numeric_types.mli. Are additional \
         standard-library credits needed for this portion?";
      notice_of = "middle_end/flambda2/numbers/numeric_types.mli";
      has_notice = true;
      about =
        Of_library
          [ "Numeric_types.Int32", "stdlib/int32.mli";
            "Numeric_types.Int64", "stdlib/int64.mli" ]
    };
    { file = "Rebuilt_expr__local";
      who = "mshinwell";
      words =
        "HV.key, t, create, find and replace use the building OCaml's \
         Hashtbl.S names and types (stdlib/hashtbl.mli counterpart). The donor \
         rule keeps the notice of \
         middle_end/flambda2/simplify/rebuilt_expr.ml. Are additional \
         standard-library credits needed for this portion?";
      notice_of = "middle_end/flambda2/simplify/rebuilt_expr.ml";
      has_notice = true;
      about =
        Of_library
          [ "HV.key", "stdlib/hashtbl.mli";
            "HV.t", "stdlib/hashtbl.mli";
            "HV.create", "stdlib/hashtbl.mli";
            "HV.find", "stdlib/hashtbl.mli";
            "HV.replace", "stdlib/hashtbl.mli" ]
    } ]

(* The width of a line of the comment. *)
let width = 80

(* What the generator is about to write for a file of decl/: the file whose
   header it carries, whether that file has a header, and what is declared, each
   with its name in OCaml and its place without the number of a line. *)
type known =
  { source : string option;
    header : bool;
    declared : (string * string) list
  }

let has_sub s sub =
  let n = String.length s and k = String.length sub in
  let rec at i = i + k <= n && (String.sub s i k = sub || at (i + 1)) in
  at 0

let begins s prefix =
  String.length s >= String.length prefix
  && String.sub s 0 (String.length prefix) = prefix

(* What is wrong with the words of a row, if anything. *)
let wrong s =
  if has_sub s "(*" || has_sub s "*)"
  then Some "a comment mark"
  else if String.contains s '"'
  then Some "a double quote"
  else None

(* Whether a declaration of the name [n] is the thing [item] or inside it. *)
let under n item = n = item || begins n (item ^ ".")

(* The first thing that a row says of its file and that is not so. *)
let not_so row known =
  let first l =
    match List.filter_map (fun x -> x) l with [] -> None | x :: _ -> Some x
  in
  if known.source <> Some row.notice_of
  then
    Some
      (Printf.sprintf "the file carries the header of %s, not of %s"
         (Option.value ~default:"no file" known.source)
         row.notice_of)
  else if known.header <> row.has_notice
  then
    Some
      (Printf.sprintf "%s has %s" row.notice_of
         (if known.header then "a header" else "no header"))
  else
    match row.about with
    | All names ->
      first
        (List.map
           (fun (n, _) ->
             if List.exists (under n) names
             then None
             else Some (Printf.sprintf "the file declares %s too" n))
           known.declared
        @ List.map
            (fun item ->
              if List.exists (fun (n, _) -> under n item) known.declared
              then None
              else Some (Printf.sprintf "the file does not declare %s" item))
            names)
    | Of_library pairs ->
      let of_library =
        List.filter (fun (_, place) -> begins place "stdlib/") known.declared
      in
      first
        (List.map
           (fun (n, place) ->
             if List.exists (fun (item, p) -> under n item && p = place) pairs
             then None
             else
               Some
                 (Printf.sprintf
                    "the file has %s of %s of the standard library too" n place))
           of_library
        @ List.map
            (fun (item, p) ->
              if
                List.exists
                  (fun (n, place) -> under n item && p = place)
                  of_library
              then None
              else
                Some
                  (Printf.sprintf "the file has nothing of %s from %s" item p))
            pairs)

(* The comment of a row, as lines: the words filled to [width], the first line
   after the mark of the comment, the others after three blanks. The mark that
   ends the comment stays on the line of the last word. *)
let comment row =
  let all =
    List.filter
      (fun w -> w <> "")
      (String.split_on_char ' '
         (String.map
            (fun c -> match c with '\n' | '\t' | '\r' -> ' ' | c -> c)
            (Printf.sprintf "CR %s: %s" row.who row.words)))
  in
  let rec close = function
    | [] -> []
    | [w] -> [w ^ " *)"]
    | w :: rest -> w :: close rest
  in
  let rec fill line lines = function
    | [] -> List.rev (line :: lines)
    | w :: rest ->
      if String.length line + 1 + String.length w <= width
      then fill (line ^ " " ^ w) lines rest
      else fill ("   " ^ w) (line :: lines) rest
  in
  match close all with [] -> [] | w :: rest -> fill ("(* " ^ w) [] rest

(* The rows, checked: for each file its comment. [known] says what the generator
   is about to write for a file; None if it does not write it. *)
let checked ~known =
  let seen = Hashtbl.create 7 in
  List.map
    (fun row ->
      let stop fmt =
        Printf.ksprintf
          (fun s ->
            failwith
              (Printf.sprintf "crs.ml: the row for decl/%s.v: %s" row.file s))
          fmt
      in
      if Hashtbl.mem seen row.file then stop "a second row for this file";
      Hashtbl.replace seen row.file ();
      (match wrong row.who, wrong row.words with
      | Some w, _ | None, Some w -> stop "its words have %s" w
      | None, None -> ());
      if
        row.who = ""
        || String.contains row.who ' '
        || String.trim row.words = ""
      then stop "no words, or no one name of who is asked";
      (match known row.file with
      | None -> stop "the file is not written"
      | Some k -> (
        match not_so row k with
        | Some what ->
          stop
            "what it says of the file is no longer so (%s): read the words \
             again"
            what
        | None -> ()));
      row.file, comment row)
    rows
