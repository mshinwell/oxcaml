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

(* The text of the compiler's interfaces: the header of a file, and the words of
   one declaration, for the comment that stands before what is generated from
   it. This file follows no file of the compiler. *)

open Common

let file_cache : (string, string array option) Hashtbl.t = Hashtbl.create 97

(* The interfaces of the standard library that the build read are those of the
   compiler that built it; their text here is the repository's own [stdlib/]
   file of the same name. *)
let source_path (fname : string) =
  let direct = Filename.concat !source_root fname in
  if Sys.file_exists direct
  then Some (fname, true)
  else
    let in_stdlib = Filename.concat "stdlib" (Filename.basename fname) in
    if Sys.file_exists (Filename.concat !source_root in_stdlib)
    then Some (in_stdlib, false)
    else None

let read_file path =
  try Some (In_channel.with_open_bin path In_channel.input_all)
  with Sys_error _ -> None

(* The name that Git gives the text of a file of the tree ([Blob]). *)
let blob rel =
  Option.map Blob.of_text (read_file (Filename.concat !source_root rel))

(* Whether a compiled file is a file of the build that is read; if not, it is of
   the library of the OCaml that made the build. *)
let of_the_build path =
  starts_with ~prefix:(Filename.concat !build_root "") path

(* How the text from which the build compiled a file stands to the tree. A typed
   tree keeps the name of the text that the compiler read and the MD5 digest of
   that text. *)
type compiled_from =
  | Tree of string
      (** the text of this file of the tree: the file itself, or a copy that the
          build made of it, which is the line [# 1 "FILE"] and then the file *)
  | Another_text of string
      (** another text of this file than the tree has (or than the build root
          has now, if the text is the build's own) *)
  | Of_the_build of string
      (** a text that the build wrote and the tree does not have *)
  | No_text of string  (** neither the tree nor the build root has this file *)
  | Not_named  (** the typed tree does not name its source *)

let compiled_from (cmt : Cmt_format.cmt_infos) =
  match cmt.cmt_sourcefile, cmt.cmt_source_digest with
  | Some s, Some d -> (
    match read_file (Filename.concat !source_root s) with
    | Some text ->
      if String.equal (Digest.string text) d then Tree s else Another_text s
    | None -> (
      match read_file (Filename.concat !build_root s) with
      | None -> No_text s
      | Some text when not (String.equal (Digest.string text) d) ->
        Another_text s
      | Some text -> (
        let copy_of =
          match String.index_opt text '\n' with
          | None -> None
          | Some i ->
            Option.map
              (fun rel ->
                rel, String.sub text (i + 1) (String.length text - i - 1))
              (Scanf.sscanf_opt (String.sub text 0 i) "# 1 %S%!" (fun r -> r))
        in
        match copy_of with
        | None -> Of_the_build s
        | Some (rel, rest) -> (
          match read_file (Filename.concat !source_root rel) with
          | Some t when String.equal t rest -> Tree rel
          | Some _ -> Another_text rel
          | None -> Of_the_build s))))
  | _ -> Not_named

(* The first line of a text that dune wrote. *)
let line_of_dune = "(* generated by dune *)\n"

(* A LIST OF THE MODULES OF A LIBRARY is the one text that the build writes, and
   the tree does not have, from which a file may be compiled that is read. It is
   known by all of these, and by nothing less. The name of its text ends with
   [.ml-gen]. That text, which the build root has ([text]: the text whose digest
   the typed tree keeps), begins with the line of dune. The typed tree is that
   of an implementation and has an item. Each item is [module A = LIB__A], where
   [LIB__A] is a compilation unit and [LIB] is the name of the unit of the list
   (without the [__] that may end it); or it is the empty module of the unit's
   own name ([module LIB__ = struct end]). *)
let list_of_modules ~text (cmt : Cmt_format.cmt_infos) =
  let unit_name = cmt.cmt_modname in
  let lib =
    if String.ends_with ~suffix:"__" unit_name
    then String.sub unit_name 0 (String.length unit_name - 2)
    else unit_name
  in
  let item (i : Typedtree.structure_item) =
    match i.str_desc with
    | Tstr_module
        { mb_name = { txt = Some a; _ };
          mb_expr = { mod_desc = Tmod_ident (Pident id, _); _ };
          _
        } ->
      Ident.persistent id && String.equal (Ident.name id) (lib ^ "__" ^ a)
    | Tstr_module
        { mb_name = { txt = Some a; _ };
          mb_expr = { mod_desc = Tmod_structure { str_items = []; _ }; _ };
          _
        } ->
      String.equal a unit_name
    | _ -> false
  in
  match cmt.cmt_sourcefile, cmt.cmt_annots with
  | Some s, Implementation str ->
    String.ends_with ~suffix:".ml-gen" s
    && String.starts_with ~prefix:line_of_dune text
    && str.str_items <> []
    && List.for_all item str.str_items
  | _ -> false

(* What the generator makes of a typed tree that it has read. *)
type standing =
  | Follows of string
      (** it was compiled from the text that the tree has of this file *)
  | List_of_modules of string
      (** it is a list of the modules of a library, compiled from this text of
          the build *)
  | Refused of string
      (** the text from which it was compiled is another than the tree's, or
          cannot be compared with the tree: the reason, one sentence *)

(* [file] is the compiled file that [cmt] was read from. If it is a file of the
   build and is refused, the reason is kept in [stale]: the generator then
   writes nothing. *)
let standing ~file (cmt : Cmt_format.cmt_infos) =
  let standing =
    match compiled_from cmt with
    | Tree rel -> Follows rel
    | Another_text s ->
      Refused (Printf.sprintf "the build compiled another text of %s" s)
    | Of_the_build s -> (
      match read_file (Filename.concat !build_root s) with
      | Some text when list_of_modules ~text cmt -> List_of_modules s
      | _ ->
        Refused
          (Printf.sprintf
             "%s is in the build root and the tree does not have it, and it is \
              not a list of the modules of a library: it cannot be compared \
              with the tree"
             s))
    | No_text s ->
      Refused
        (Printf.sprintf
           "%s, the text from which the build compiled %s, is neither in the \
            tree nor in the build root: it cannot be compared with the tree"
           s (Filename.basename file))
    | Not_named ->
      Refused
        (Printf.sprintf
           "the typed tree %s does not name the text from which it was \
            compiled: it cannot be compared with the tree"
           (Filename.basename file))
  in
  (match standing with
  | Refused why when of_the_build file -> stale := why :: !stale
  | Follows _ | List_of_modules _ | Refused _ -> ());
  standing

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

(* The header of a file: its first lines, as long as each is a comment on one
   line (the box of the licence); or its first comment, when that is a box of
   several lines (it begins with a line of stars and ends a line). *)
let header rel =
  match lines_of rel with
  | None -> []
  | Some lines ->
    let n = Array.length lines in
    let ends l =
      let k = String.length l in
      k >= 2 && String.sub l (k - 2) 2 = "*)"
    in
    let is_box l = String.length l >= 4 && String.sub l 0 2 = "(*" && ends l in
    let is_stars l =
      let k = String.length l in
      k >= 12
      && l.[0] = '('
      && String.for_all (fun c -> c = '*') (String.sub l 1 (k - 1))
    in
    let rec several i acc =
      if i >= n
      then []
      else if ends lines.(i)
      then List.rev (lines.(i) :: acc)
      else several (i + 1) (lines.(i) :: acc)
    in
    let rec go i acc =
      if i < n && is_box lines.(i)
      then go (i + 1) (lines.(i) :: acc)
      else List.rev acc
    in
    if n > 0 && is_stars lines.(0) then several 1 [lines.(0)] else go 0 []

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

(* Where a declaration is, and its words: [(variable.mli:23, "val ...")]. For
   the standard library the place is the repository's file and no line (the
   lines are those of another copy), and no words. *)
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
          String.concat " "
            (Array.to_list (Array.sub lines first (last - first + 1)))
        in
        place, Some (one_line text))
