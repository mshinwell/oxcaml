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

(* Three tables about the files of Simplify that the ported files follow (the
   donors): the rows of UPDATES.tsv and of DONOR-TOKENS.tsv, for tools/given.py,
   and those of DONOR-ITEMS.tsv, for tools/lines.py. This file follows no file
   of the compiler.

   UPDATES.tsv: one row for each record update [{ e with f1 = v1; .. }] of the
   typed tree of a donor: the file, the line where the update begins, the line
   where it ends, the type of the record as the typed tree names it, the place
   of that type (the file and the line where its first field is declared, as the
   typed tree has them), the fields that the update gives in the order of the
   text, and all the fields of the type in the order of the type. Two types of
   one name in one file have two places. A row has names and numbers from the
   typed tree, and no text of a source. A donor whose typed tree was not made
   from the text of the tree ([Arities.tree_source]) has one row that says so,
   with [-] for the lines.

   DONOR-TOKENS.tsv: one row for each donor: the file, the number of tokens that
   the compiler's own lexer reads in it (comments left out), and a checksum: the
   MD5 of the characters of those tokens that are not white space, one after the
   other, with nothing between one token and the next (the white space inside a
   string is left out too). tools/given.py reads the donors with a lexer of its
   own and wants this checksum for its own tokens: then it reads the same
   characters that are not white space, outside comments, as the compiler's
   lexer. The checksum is no identity of the tokens or of the source: it does
   not show where a token ends (the two lexers do not cut the characters into
   the same tokens: a label [~f:] is one token here), and it does not show the
   white space of a string.

   DONOR-ITEMS.tsv: one row for each name that an item of a structure of the
   typed tree of a donor defines, at any depth of modules (also in the body of a
   functor): the file; the kind ([value], [external], [type], [exception],
   [module], [module type]); the modules around the item inside the file, from
   the outermost, with dots between them and [()] after the name of a functor
   (empty at the top of the file); the name; the first and the last line of the
   definition of that name; the first and the last line of the whole item. The
   two pairs of lines differ for an item that defines several things together
   ([let rec f .. and g ..], [type a = .. and b = ..]): the definition of [g]
   begins at its own first line, the item at [let]. A value that a pattern binds
   ([let a, b = ..]) has one row for each name, with the lines of the binding.
   An item that binds no name ([let () = ..]) has no row. A row has names and
   numbers from the typed tree, and no text of a source. A donor that is not
   read has one row that says so, with [-] for the kind and the lines. *)

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
        |> List.map (fun ((ld : Data_types.label_description), _) ->
            ld.lbl_name)
      in
      let given =
        Array.to_list fields
        |> List.filter_map (fun ((ld : Data_types.label_description), d) ->
            match (d : Typedtree.record_label_definition) with
            | Kept _ -> None
            | Overridden (lid, _) ->
              Some (lid.loc.loc_start.pos_cnum, ld.lbl_name))
        |> List.sort compare |> List.map snd
      in
      let place =
        if Array.length fields = 0
        then "?"
        else
          let (ld : Data_types.label_description), _ = fields.(0) in
          Printf.sprintf "%s:%d" ld.lbl_loc.loc_start.pos_fname
            (line ld.lbl_loc)
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

(* The rows of the items of one structure. *)
let items_of source (str : Typedtree.structure) =
  let rows = ref [] in
  let row kind path name (own : Location.t) first (whole : Location.t) =
    rows
      := Printf.sprintf "%s\t%s\t%s\t%s\t%d\t%d\t%d\t%d" source kind
           (String.concat "." (List.rev path))
           name first (last_line own) (line whole) (last_line whole)
         :: !rows
  in
  (* the first of several definitions of one item begins where the item does (at
     its keyword); each other one at its own first line *)
  let first i (own : Location.t) (whole : Location.t) =
    if i = 0 then line whole else line own
  in
  let rec items path (str : Typedtree.structure) =
    List.iter
      (fun (it : Typedtree.structure_item) ->
        let whole = it.str_loc in
        match it.str_desc with
        | Tstr_value (_, vbs) ->
          List.iteri
            (fun i (vb : Typedtree.value_binding) ->
              List.iter
                (fun id ->
                  row "value" path (Ident.name id) vb.vb_loc
                    (first i vb.vb_loc whole) whole)
                (Typedtree.pat_bound_idents vb.vb_pat))
            vbs
        | Tstr_primitive vd ->
          row "external" path vd.val_name.txt whole (line whole) whole
        | Tstr_type (_, ds) ->
          List.iteri
            (fun i (d : Typedtree.type_declaration) ->
              row "type" path d.typ_name.txt d.typ_loc (first i d.typ_loc whole)
                whole)
            ds
        | Tstr_exception e ->
          row "exception" path e.tyexn_constructor.ext_name.txt whole
            (line whole) whole
        | Tstr_modtype mtd ->
          row "module type" path mtd.mtd_name.txt whole (line whole) whole
        | Tstr_module mb -> (
          match mb.mb_name.txt with
          | None -> ()
          | Some name ->
            row "module" path name whole (line whole) whole;
            modexpr path name mb.mb_expr)
        | Tstr_recmodule mbs ->
          List.iteri
            (fun i (mb : Typedtree.module_binding) ->
              match mb.mb_name.txt with
              | None -> ()
              | Some name ->
                row "module" path name mb.mb_loc (first i mb.mb_loc whole) whole;
                modexpr path name mb.mb_expr)
            mbs
        | _ -> ())
      str.str_items
  and modexpr path name (me : Typedtree.module_expr) =
    match me.mod_desc with
    | Tmod_structure str -> items (name :: path) str
    | Tmod_functor (_, body) ->
      let name =
        if
          String.length name >= 2
          && String.sub name (String.length name - 2) 2 = "()"
        then name
        else name ^ "()"
      in
      modexpr path name body
    | Tmod_constraint (me, _, _, _) -> modexpr path name me
    | _ -> ()
  in
  items [] str;
  List.rev !rows

let items_not_read source why =
  Printf.sprintf "%s\t-\t\t%s\t-\t-\t-\t-" source why

(* The source of a typed tree in the tree, the rows of its record updates and
   the rows of its items; or, for each of the two tables, the one row that says
   why it was not read. *)
let read cmt_file : string option * string list * string list =
  let no source why =
    None, [not_read source why], [items_not_read source why]
  in
  match Cmt_format.read_cmt cmt_file with
  | exception _ ->
    no (Filename.basename cmt_file) "not read: the typed tree could not be read"
  | cmt -> (
    let named =
      Option.value ~default:(Filename.basename cmt_file) cmt.cmt_sourcefile
    in
    match cmt.cmt_annots with
    | Implementation str -> (
      match Arities.tree_source cmt str with
      | Ok source -> Some source, updates_of source str, items_of source str
      | Error why -> no named why)
    | _ -> no named "not read: no typed tree of an implementation")

let is_white c = c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\012'

(* The number of tokens of a text and the checksum of their characters that are
   not white space. *)
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

(* The row of DONOR-TOKENS.tsv of a file of the tree; none if the tree does not
   have the file (a list of modules that the build writes). *)
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
  | _ ->
    print_endline
      (not_read cmt_file "not read: no typed tree of an implementation")

(* For a test ([declgen --items FILE.cmt]): the rows of one typed tree, whatever
   its source is. *)
let print_items cmt_file =
  let cmt = Cmt_format.read_cmt cmt_file in
  match cmt.cmt_annots with
  | Implementation str ->
    List.iter print_endline
      (items_of (Option.value ~default:"?" cmt.cmt_sourcefile) str)
  | _ ->
    print_endline
      (items_not_read cmt_file "not read: no typed tree of an implementation")

(* For a test ([declgen --tokens FILE.ml]): the row of one file. *)
let print_tokens file =
  match Arities.read_file file with
  | None -> Printf.printf "%s\t-\tnot read: no such file\n" file
  | Some text -> (
    match tokens_of_text file text with
    | Ok (n, digest) -> Printf.printf "%s\t%d\t%s\n" file n digest
    | Error why -> Printf.printf "%s\t-\t%s\n" file why)
