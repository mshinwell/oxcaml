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

(* Two tables about the files of Simplify that the ported files follow (the
   donors), for tools/given.py: the rows of UPDATES.tsv and of
   DONOR-TOKENS.tsv. This file follows no file of the compiler.

   UPDATES.tsv: one row for each record update [{ e with f1 = v1; .. }] of
   the typed tree of a donor: the file, the line where the update begins,
   the line where it ends, the type of the record as the typed tree names
   it, the place of that type (the file and the line where its first field
   is declared, as the typed tree has them), the fields that the update
   gives in the order of the text, and all the fields of the type in the
   order of the type. Two types of one name in one file have two places. A
   row has names and numbers from the typed tree, and no text of a source.
   A donor whose typed tree was not made from the text of the tree
   ([Arities.tree_source]) has one row that says so, with [-] for the lines.

   DONOR-TOKENS.tsv: one row for each donor: the file, the number of tokens
   that the compiler's own lexer reads in it (comments left out), and the
   MD5 digest of the characters of those tokens, one after the other,
   without white space (a string may hold some). tools/given.py reads the
   donors with a lexer of its own; it wants the characters of its tokens to
   have this digest, so that it leaves out the same comments and loses no
   character. The two lexers do not cut the characters into the same
   tokens (a label [~f:] is one token here). *)

let line (l : Location.t) = l.loc_start.pos_lnum

let last_line (l : Location.t) = l.loc_end.pos_lnum

let rec type_name (t : Types.type_expr) =
  match Types.get_desc t with
  | Tconstr (p, _, _) -> Path.name p
  | Tpoly (t, _) -> type_name t
  | _ -> "?"

(* The rows of the record updates of one structure. *)
let updates_of source (str : Typedtree.structure) =
  let rows = ref [] in
  let expr (it : Tast_iterator.iterator) (e : Typedtree.expression) =
    (match e.exp_desc with
    | Texp_record { fields; extended_expression = Some _; _ } ->
      let all =
        Array.to_list fields
        |> List.map (fun ((ld : Data_types.label_description), _) -> ld.lbl_name)
      in
      let given =
        Array.to_list fields
        |> List.filter_map (fun ((ld : Data_types.label_description), d) ->
               match (d : Typedtree.record_label_definition) with
               | Kept _ -> None
               | Overridden (lid, _) -> Some (lid.loc.loc_start.pos_cnum, ld.lbl_name))
        |> List.sort compare |> List.map snd
      in
      let place =
        if Array.length fields = 0
        then "?"
        else
          let (ld : Data_types.label_description), _ = fields.(0) in
          Printf.sprintf "%s:%d" ld.lbl_loc.loc_start.pos_fname (line ld.lbl_loc)
      in
      rows
        := Printf.sprintf "%s\t%d\t%d\t%s\t%s\t%s\t%s" source (line e.exp_loc)
             (last_line e.exp_loc) (type_name e.exp_type) place
             (String.concat " " given) (String.concat " " all)
           :: !rows
    | _ -> ());
    Tast_iterator.default_iterator.expr it e
  in
  let it = { Tast_iterator.default_iterator with expr } in
  it.structure it str;
  List.rev !rows

let not_read source why = Printf.sprintf "%s\t-\t-\t%s\t-\t\t" source why

(* The source of a typed tree in the tree, and the rows of its record
   updates; or the one row that says why it was not read. *)
let read cmt_file : string option * string list =
  match Cmt_format.read_cmt cmt_file with
  | exception _ ->
    None, [not_read (Filename.basename cmt_file) "not read: the typed tree could not be read"]
  | cmt -> (
    let named = Option.value ~default:(Filename.basename cmt_file) cmt.cmt_sourcefile in
    match cmt.cmt_annots with
    | Implementation str -> (
      match Arities.tree_source cmt str with
      | Ok source -> Some source, updates_of source str
      | Error why -> None, [not_read named why])
    | _ -> None, [not_read named "not read: no typed tree of an implementation"])

let is_white c = c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\012'

(* The number of tokens of a text and the digest of their characters. *)
let tokens_of_text name text =
  let lexbuf = Lexing.from_string text in
  Lexing.set_filename lexbuf name;
  Lexer.init ();
  let b = Buffer.create (String.length text) in
  let rec loop n =
    match Lexer.token lexbuf with
    | Parser.EOF -> n
    | Parser.COMMENT _ | Parser.DOCSTRING _ -> loop n
    | _ ->
      for i = lexbuf.lex_start_p.pos_cnum to lexbuf.lex_curr_p.pos_cnum - 1 do
        if not (is_white text.[i]) then Buffer.add_char b text.[i]
      done;
      loop (n + 1)
  in
  match loop 0 with
  | n -> Ok (n, Digest.to_hex (Digest.string (Buffer.contents b)))
  | exception _ -> Error "not read: the compiler's lexer refuses the text"

(* The row of DONOR-TOKENS.tsv of a file of the tree; none if the tree does
   not have the file (a list of modules that the build writes). *)
let tokens source =
  match Arities.read_file (Filename.concat !Common.source_root source) with
  | None -> None
  | Some text -> (
    match tokens_of_text source text with
    | Ok (n, digest) -> Some (Printf.sprintf "%s\t%d\t%s" source n digest)
    | Error why -> Some (Printf.sprintf "%s\t-\t%s" source why))

(* For a test ([declgen --updates FILE.cmt]): the rows of one typed tree,
   whatever its source is. *)
let print_updates cmt_file =
  let cmt = Cmt_format.read_cmt cmt_file in
  match cmt.cmt_annots with
  | Implementation str ->
    List.iter print_endline
      (updates_of (Option.value ~default:"?" cmt.cmt_sourcefile) str)
  | _ -> print_endline (not_read cmt_file "not read: no typed tree of an implementation")

(* For a test ([declgen --tokens FILE.ml]): the row of one file. *)
let print_tokens file =
  match Arities.read_file file with
  | None -> Printf.printf "%s\t-\tnot read: no such file\n" file
  | Some text -> (
    match tokens_of_text file text with
    | Ok (n, digest) -> Printf.printf "%s\t%d\t%s\n" file n digest
    | Error why -> Printf.printf "%s\t-\t%s\n" file why)
