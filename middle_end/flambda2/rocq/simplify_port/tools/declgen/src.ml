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

(* The text of the compiler's interfaces: the header of a file, and the
   words of one declaration, for the comment that stands before what is
   generated from it. This file follows no file of the compiler. *)

open Common

let file_cache : (string, string array option) Hashtbl.t = Hashtbl.create 97

(* The interfaces of the standard library that the build read are those of
   the compiler that built it; their text here is the repository's own
   [stdlib/] file of the same name. *)
let source_path (fname : string) =
  let direct = Filename.concat !source_root fname in
  if Sys.file_exists direct
  then Some (fname, true)
  else
    let in_stdlib = Filename.concat "stdlib" (Filename.basename fname) in
    if Sys.file_exists (Filename.concat !source_root in_stdlib)
    then Some (in_stdlib, false)
    else None

let lines_of rel =
  match Hashtbl.find_opt file_cache rel with
  | Some l -> l
  | None ->
    let l =
      try
        let ic = open_in_bin (Filename.concat !source_root rel) in
        let n = in_channel_length ic in
        let s = really_input_string ic n in
        close_in ic;
        Some (Array.of_list (String.split_on_char '\n' s))
      with Sys_error _ -> None
    in
    Hashtbl.replace file_cache rel l;
    l

(* The header of a file: its first lines, as long as each is a comment on
   one line (the box of the licence). *)
let header rel =
  match lines_of rel with
  | None -> []
  | Some lines ->
    let is_box l =
      let n = String.length l in
      n >= 4 && String.sub l 0 2 = "(*" && String.sub l (n - 2) 2 = "*)"
    in
    let rec go i acc =
      if i < Array.length lines && is_box lines.(i)
      then go (i + 1) (lines.(i) :: acc)
      else List.rev acc
    in
    go 0 []

(* Text that is safe inside a comment of Rocq, on one line. *)
let one_line s =
  let b = Buffer.create (String.length s) in
  let last_space = ref true in
  String.iter
    (fun c ->
      match c with
      | ' ' | '\n' | '\t' | '\r' ->
        if not !last_space then Buffer.add_char b ' ';
        last_space := true
      | '"' ->
        Buffer.add_char b '\'';
        last_space := false
      | c ->
        Buffer.add_char b c;
        last_space := false)
    s;
  let s = String.trim (Buffer.contents b) in
  let s = Str.global_replace (Str.regexp_string "(*") "( *" s in
  let s = Str.global_replace (Str.regexp_string "*)") "* )" s in
  if String.length s > 400 then String.sub s 0 397 ^ "..." else s

(* Where a declaration is, and its words: [(variable.mli:23, "val ...")].
   For the standard library the place is the repository's file and no line
   (the lines are those of another copy), and no words. *)
let place_and_text (loc : Location.t) =
  let fname = loc.loc_start.pos_fname in
  match source_path fname with
  | None -> Filename.basename fname, None
  | Some (rel, false) -> rel, None
  | Some (rel, true) -> (
    let place =
      Printf.sprintf "%s:%d" (Filename.basename rel) loc.loc_start.pos_lnum
    in
    match lines_of rel with
    | None -> place, None
    | Some lines ->
      let first = loc.loc_start.pos_lnum - 1 in
      let last = loc.loc_end.pos_lnum - 1 in
      if first < 0 || last >= Array.length lines || last < first
      then place, None
      else
        let text =
          String.concat " " (Array.to_list (Array.sub lines first (last - first + 1)))
        in
        place, Some (one_line text))
