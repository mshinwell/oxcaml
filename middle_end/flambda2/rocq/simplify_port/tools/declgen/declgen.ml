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

(* declgen BUILD_ROOT SOURCE_ROOT OUT_DIR COMMIT FILE.cmt ...

   Writes, into OUT_DIR, one file of Rocq for each compilation unit that the
   given files of Simplify use, and for each of those files itself: the
   declarations of decl/README.md. Also INDEX.tsv, ARITIES.tsv,
   NOT-DECLARED.tsv, and the three tables of donors.ml about the given files
   themselves, UPDATES.tsv, DONOR-TOKENS.tsv and DONOR-ITEMS.tsv.

   declgen --parameters FILE.cmt

   For a test of the count of ARITIES.tsv: prints each value that the
   implementation FILE.cmt binds at its top, and the number of its parameters by
   the rule of arities.ml. It writes no file.

   declgen --updates FILE.cmt declgen --tokens FILE.ml declgen --items FILE.cmt

   For a test of the three tables of donors.ml: prints the rows of the record
   updates of one typed tree, or the row of the tokens of one file, or the rows
   of the items of one typed tree. They write no file. This file follows no file
   of the compiler. *)

open Common
module SS = Set.Make (String)

let source_of_unit u =
  let find ext =
    try Some (Load_path.find_normalized (u ^ ext)) with Not_found -> None
  in
  match match find ".cmti" with Some f -> Some f | None -> find ".cmt" with
  | None -> None
  | Some f -> (
    match Cmt_format.read_cmt f with
    | exception _ -> None
    | cmt -> (
      let found s =
        match Src.source_path s with Some (rel, true) -> Some rel | _ -> None
      in
      (* the build compiles some files from a copy ([misc.mli], which is
         utils/misc.mli): the places inside name the file itself *)
      let inside =
        match cmt.cmt_annots with
        | Interface { sig_items = item :: _; _ } ->
          Some item.sig_loc.loc_start.pos_fname
        | Implementation { str_items = item :: _; _ } ->
          Some item.str_loc.loc_start.pos_fname
        | _ -> None
      in
      match Option.bind cmt.cmt_sourcefile found with
      | Some rel -> Some rel
      | None -> (
        match Option.bind inside found with
        | Some rel -> Some rel
        | None ->
          Option.map fst (Option.bind cmt.cmt_sourcefile Src.source_path))))

let no_source =
  [ "(* This file follows an interface whose source was not found: see the";
    "   comment below. *)" ]

let no_header =
  [ "(* The interface that this file follows has no header: see the comment";
    "   below. *)" ]

let units () =
  let s = ref SS.empty in
  let add comps =
    match comps with
    | "%predef" :: _ -> ()
    | u :: _ -> if not (is_local_unit u) then s := SS.add u !s
    | [] -> ()
  in
  Hashtbl.iter (fun _ (c, _) -> add c) Uses.values;
  Hashtbl.iter (fun _ (u : Uses.type_use) -> add u.comps) Uses.types;
  Hashtbl.iter (fun _ c -> add c) Uses.exceptions;
  Hashtbl.iter (fun _ c -> add c) Uses.modtypes;
  Hashtbl.iter (fun _ c -> add c) Tr.needed_types;
  SS.elements !s

(* The last lines of the file of declarations [rocq].

   In an extracted file Rocq writes [open U] for each file [U] of which it
   prints a name, and then prints the names of [U] without [U.]. In OCaml that
   [open] brings every name of the real module [U]: more than the declarations
   have, so Rocq does not know of them. A name that Rocq prints short, or a name
   in a realisation, could then mean something of [U] instead (after [open
   Simple], [List] is [Simple.List]).

   Rocq does not write [open U] when [U] has at its top a module with the name
   of a file in use, and [U] is itself in use where it would be opened. So each
   file ends with an empty module of its own name: no extracted file opens a
   file of declarations, and Rocq prints each of its names in full. *)
let no_open ~local rocq =
  let why =
    if local
    then
      [ "(* Not in the file of Simplify: an empty module with the name of this \
         file.";
        "   With it Rocq's extraction writes no [open] of this file, which is \
         not a";
        "   module of OCaml, and prints each of its names in full. *)" ]
    else
      [ "(* Not in the interface: an empty module with the name of this file. \
         With";
        "   it Rocq's extraction does not open this file's module in the files \
         that";
        "   use it, and prints each of its names in full. So what the real \
         module";
        "   has, and these declarations do not have, hides no other name \
         there. *)" ]
  in
  String.concat "\n"
    (("" :: why) @ [Printf.sprintf "Module %s. End %s." rocq rocq; ""])

let pass scanned =
  Decl_out.index := [];
  Decl_out.values := [];
  Decl_out.left := [];
  Decl_out.variants := [];
  Walk.emitted_now := SS.empty;
  Hashtbl.reset Decl_out.native_now;
  Hashtbl.reset Emit_types.labelled_now;
  let forced_units =
    SS.filter (fun k -> not (String.contains k '.')) !Walk.forced
  in
  let all =
    SS.elements
      (SS.union forced_units (SS.union (SS.of_list (units ())) scanned))
  in
  let results =
    List.filter_map
      (fun u ->
        match Walk.emit_unit ~full:(is_simplify_unit u) u with
        | Some (body, deps) -> Some (u, body, deps)
        | None -> None)
      all
  in
  let local_units =
    List.sort compare (Hashtbl.fold (fun u _ acc -> u :: acc) Sigs.locals [])
  in
  let results =
    results
    @ List.filter_map
        (fun u ->
          match Walk.emit_local_unit u with
          | Some (body, deps) -> Some (u, body, deps)
          | None -> None)
        local_units
  in
  let table t =
    List.sort compare
      (Hashtbl.fold (fun k s acc -> (k, Decl_out.SS.elements s) :: acc) t [])
  in
  let same =
    SS.equal !Walk.emitted_before !Walk.emitted_now
    && table Decl_out.native_before = table Decl_out.native_now
  in
  Walk.emitted_before := !Walk.emitted_now;
  Hashtbl.reset Decl_out.native_before;
  Hashtbl.iter (Hashtbl.replace Decl_out.native_before) Decl_out.native_now;
  results, same

(* A file is written only if its text has changed, so that what depends on it is
   not made again for nothing. *)
let write_file path contents =
  let same =
    Sys.file_exists path
    &&
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic;
    s = contents
  in
  if not same
  then (
    let oc = open_out_bin path in
    output_string oc contents;
    close_out oc)

let () =
  if Array.length Sys.argv = 3 && Sys.argv.(1) = "--parameters"
  then (
    Arities.print_parameters Sys.argv.(2);
    exit 0);
  if Array.length Sys.argv = 3 && Sys.argv.(1) = "--updates"
  then (
    Donors.print_updates Sys.argv.(2);
    exit 0);
  if Array.length Sys.argv = 3 && Sys.argv.(1) = "--tokens"
  then (
    Donors.print_tokens Sys.argv.(2);
    exit 0);
  if Array.length Sys.argv = 3 && Sys.argv.(1) = "--items"
  then (
    Donors.print_items Sys.argv.(2);
    exit 0);
  build_root := Sys.argv.(1);
  source_root := Sys.argv.(2);
  let out_dir = Sys.argv.(3) in
  let commit = Sys.argv.(4) in
  let cmts = Array.to_list (Array.sub Sys.argv 5 (Array.length Sys.argv - 5)) in
  let scanned = ref SS.empty in
  let last = ref None in
  List.iter
    (fun f ->
      let cmt = Uses.scan f in
      scanned := SS.add cmt.cmt_modname !scanned;
      last := Some cmt)
    cmts;
  (match !last with
  | Some cmt -> Sigs.base_env := Envaux.env_of_only_summary cmt.cmt_initial_env
  | None -> failwith "no file given");
  let rec loop n =
    Tr.changed := false;
    let results, same = pass !scanned in
    if (!Tr.changed || not same) && n < 12 then loop (n + 1) else results, n
  in
  let results, passes = loop 1 in
  let names = Hashtbl.create 97 in
  List.iter
    (fun (u, body, deps) ->
      let rocq = Sigs.unit_rocq u in
      (match Hashtbl.find_opt names rocq with
      | Some u' ->
        failwith (Printf.sprintf "two units for %s.v: %s and %s" rocq u u')
      | None -> Hashtbl.replace names rocq u);
      let source =
        match Hashtbl.find_opt Sigs.locals u with
        | Some (_, file) -> Some file
        | None -> source_of_unit u
      in
      let header =
        match source with
        | Some rel -> ( match Src.header rel with [] -> no_header | h -> h)
        | None -> no_source
      in
      let b = Buffer.create (String.length body + 4096) in
      List.iter (fun l -> Buffer.add_string b (l ^ "\n")) header;
      if is_local_unit u
      then
        Buffer.add_string b
          (Printf.sprintf
             "\n\
              (* GENERATED, not written by hand: the declarations of the \
              modules that\n\
             \   %s\n\
             \   at commit %s makes for itself by applying a functor of another\n\
             \   part of the compiler, and of what the file uses of them. The \
              port keeps\n\
             \   the definitions of these modules as they are in the file, and \
              the\n\
             \   realisations name them as the file does. Made by \
              tools/declgen (see\n\
             \   decl/README.md): a change is made there, not here. *)\n\n"
             (Option.value ~default:"(source not found)" source)
             commit)
      else
        Buffer.add_string b
          (Printf.sprintf
             "\n\
              (* GENERATED, not written by hand: the declarations of what the \
              port of\n\
             \   Simplify uses of the compiler's module [%s], after its \
              interface\n\
             \   %s\n\
             \   at commit %s. Made by tools/declgen (see decl/README.md): a\n\
             \   change is made there, not here. *)\n\n"
             (short_unit u)
             (Option.value ~default:"(source not found)" source)
             commit);
      Buffer.add_string b "From SimplifyPort Require Import Port_monad.\n";
      let deps = SS.elements (SS.remove u deps) in
      if deps <> []
      then
        Buffer.add_string b
          (Printf.sprintf "From SimplifyPort.decl Require %s.\n"
             (String.concat " "
                (List.sort compare (List.map Sigs.unit_rocq deps))));
      Buffer.add_char b '\n';
      Buffer.add_string b body;
      (* the file ends with a module of its own name: see [no_open] *)
      Buffer.add_string b (no_open ~local:(is_local_unit u) rocq);
      write_file (Filename.concat out_dir (rocq ^ ".v")) (Buffer.contents b))
    results;
  (* what an earlier run wrote and this one does not *)
  Array.iter
    (fun f ->
      if
        Filename.check_suffix f ".v"
        && not (Hashtbl.mem names (Filename.chop_suffix f ".v"))
      then Sys.remove (Filename.concat out_dir f))
    (Sys.readdir out_dir);
  let tsv file rows =
    write_file
      (Filename.concat out_dir file)
      (String.concat ""
         (List.map (fun r -> r ^ "\n") (List.sort_uniq compare rows)))
  in
  tsv "INDEX.tsv"
    (List.map
       (fun (o, r, k, a, p) -> Printf.sprintf "%s\t%s\t%s\t%d\t%s" o r k a p)
       !Decl_out.index);
  (* for each declared value: the parameters of its realisation and of its
     definition *)
  tsv "ARITIES.tsv"
    (List.map
       (fun (comps, ocaml, rocq, wrapper) ->
         let definition, where = Arities.row comps in
         Printf.sprintf "%s\t%s\t%d\t%s\t%s" ocaml rocq wrapper definition where)
       !Decl_out.values);
  (* the given files themselves: their record updates, their tokens and their
     items *)
  let donors = List.map Donors.read cmts in
  tsv "UPDATES.tsv" (List.concat_map (fun (_, updates, _) -> updates) donors);
  tsv "DONOR-TOKENS.tsv"
    (List.filter_map
       (fun (source, _, _) -> Option.bind source Donors.tokens)
       donors);
  tsv "DONOR-ITEMS.tsv" (List.concat_map (fun (_, _, items) -> items) donors);
  (* the modules that the files give to their functors, where a module type with
     a name is wanted: in OCaml and in Rocq *)
  let rocq_module comps =
    match comps with
    | u :: mods ->
      String.concat "." (Sigs.unit_rocq u :: Print.modules_rocq u mods)
    | [] -> ""
  in
  let rocq_modtype comps =
    let modc, name = Print.split_last comps in
    match
      Hashtbl.find_opt Sigs.modtype_rocq (key (modc @ [modtype_component name]))
    with
    | Some n -> rocq_module modc ^ "." ^ n
    | None -> ""
  in
  tsv "FUNCTOR-ARGUMENTS.tsv"
    (List.map
       (fun (file, f, mt, given) ->
         Printf.sprintf "%s\t%s\t%s\t%s\t%s\t%s" file f (Print.ocaml_name mt)
           (Print.ocaml_name given) (rocq_modtype mt) (rocq_module given))
       !Uses.functor_arguments);
  tsv "VARIANTS.tsv"
    (List.map
       (fun (ty, arity, ctors, hidden) ->
         Printf.sprintf "%s\t%d\t%s\t%s" ty arity (String.concat " " ctors)
           (if hidden then "a later type has one of these names" else ""))
       !Decl_out.variants);
  tsv "NOT-DECLARED.tsv"
    (List.map (fun (o, why) -> Printf.sprintf "%s\t%s" o why) !Decl_out.left
    @ List.map
        (fun (place, what) ->
          Printf.sprintf
            "%s (%s)\tmade with a functor of outside inside a functor of the \
             file: it depends on that functor's parameter"
            what place)
        !Uses.inside_functor);
  List.iter prerr_endline (List.sort_uniq compare !warnings);
  List.iter
    (fun (file, f, what) ->
      Printf.eprintf
        "%s: the functor %s uses %s of a module that could not be followed\n"
        file f what)
    (List.sort_uniq compare !Uses.not_followed);
  Printf.printf "%d files, %d declarations, %d not declared, %d passes\n"
    (List.length results)
    (List.length !Decl_out.index)
    (List.length !Decl_out.left)
    passes
