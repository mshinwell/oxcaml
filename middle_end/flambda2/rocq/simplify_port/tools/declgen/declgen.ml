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

(* declgen BUILD_ROOT SOURCE_ROOT OUT_DIR FILE.cmt ...

   Writes, into OUT_DIR, one file of Rocq for each compilation unit that the
   given files of Simplify use, and for each of those files itself: the
   declarations of decl/README.md. Also INDEX.tsv, ARITIES.tsv,
   NOT-DECLARED.tsv, and the three tables of donors.ml about the given files
   themselves, UPDATES.tsv, DONOR-TOKENS.tsv and DONOR-ITEMS.tsv. Under the
   header of a file that crs.ml names it writes that file's question for a human
   (none when DECLGEN_SOME_FILES is in the environment: run.sh sets it for a run
   on some of the files).

   What it writes depends on what it reads and on nothing else: no commit is
   given to it, and each file says which text it follows by the name that Git
   gives that text ([Blob]). SOURCE_ROOT must be the sources of which BUILD_ROOT
   is a build. Before a file is written, the text from which the build compiled
   each file that was read is compared with the tree's ([Src.standing]), and the
   compiled interfaces that were loaded with those that the given typed trees
   were compiled against. If one is another, or if a unit of the build cannot be
   compared ([compare_loaded]), it stops and writes nothing.

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

(* The typed tree of the interface of a unit: that of its [.mli] file, or of its
   [.ml] file if it has no other. It is the one that stands beside the compiled
   interface [cmi] of the unit, where the compiler writes it. *)
let typed_tree_beside cmi =
  let base = Filename.remove_extension cmi in
  List.find_opt Sys.file_exists [base ^ ".cmti"; base ^ ".cmt"]

let typed_tree_of_unit u =
  match Load_path.find_normalized (u ^ ".cmi") with
  | exception Not_found -> None
  | cmi -> typed_tree_beside cmi

(* Where the interface of a unit is in the sources of the tree, and whether the
   text of that file is the text from which the build compiled the interface
   that is read: the compiler's own digest of what it read says so
   ([Src.standing]; the build compiles some files from a copy, [misc.mli], which
   is utils/misc.mli). It is not for a unit of the standard library: the build
   read the library of the OCaml that built the compiler, and the file is the
   tree's own of the same name (Src.source_path). *)
let source_of_unit u =
  match typed_tree_of_unit u with
  | None -> None
  | Some f -> (
    match Cmt_format.read_cmt f with
    | exception _ -> None
    | cmt -> (
      if Src.of_the_build f
      then
        match Src.standing ~file:f cmt with
        | Follows rel -> Some (rel, true)
        | List_of_modules _ | Refused _ -> None
      else
        match Option.bind cmt.cmt_sourcefile Src.source_path with
        | Some (rel, _) -> Some (rel, false)
        | None -> None))

(* Every compiled interface that was loaded ([loaded]: each unit, and the digest
   by which the compiled files that import its interface name it), against the
   tree.

   A UNIT OF THE BUILD IS TAKEN ONLY IF ITS TEXT IS KNOWN. Beside its compiled
   interface there must be the typed tree that the compiler wrote with it: that
   typed tree keeps the digest of the compiled interface, which must be the one
   that was loaded. The text from which that typed tree was compiled must be the
   text of the tree ([Src.standing]); or the unit must be a list of the modules
   of a library, which the build writes ([Src.list_of_modules]). Anything else
   is kept in [stale], with the reason, and the generator writes nothing: no
   typed tree, one that cannot be read, one of another compilation, a text that
   is neither in the tree nor in the build root, another text that the build
   wrote.

   A compiled interface that is not of the build is taken only for a unit of the
   standard library ([Stdlib], [Stdlib__X], [CamlinternalX]): that library is of
   the OCaml that made the build, and its text is not compared.

   The result: how many units of the build were compiled from the text of the
   tree; the lists of modules, each by the name of its text; and how many units
   are of the standard library. *)
let compare_loaded loaded =
  let of_tree = ref 0 in
  let of_library = ref 0 in
  let lists = ref [] in
  let refuse fmt = Printf.ksprintf (fun why -> stale := why :: !stale) fmt in
  List.iter
    (fun (u, digest) ->
      match Load_path.find_normalized (u ^ ".cmi") with
      | exception Not_found ->
        refuse
          "the compiled interface of %s was loaded, and no file of it is found \
           now"
          u
      | cmi when not (Src.of_the_build cmi) ->
        if is_stdlib_unit u || starts_with ~prefix:"Camlinternal" u
        then incr of_library
        else
          refuse
            "%s is no unit of the standard library, and its compiled interface \
             %s is not of the build"
            u cmi
      | cmi -> (
        match typed_tree_beside cmi with
        | None ->
          refuse
            "the build has no typed tree beside the compiled interface %s, so \
             the text from which the interface of %s was compiled cannot be \
             compared with the tree"
            cmi u
        | Some f -> (
          match Cmt_format.read_cmt f with
          | exception _ ->
            refuse
              "the typed tree %s could not be read, so the text from which the \
               interface of %s was compiled cannot be compared with the tree"
              f u
          | cmt -> (
            let written_with_it =
              match digest, cmt.cmt_interface_digest with
              | Some d, Some d' -> String.equal d d'
              | _ -> false
            in
            if not written_with_it
            then
              refuse
                "the typed tree %s was not written with the compiled interface \
                 of %s that is read, so it does not say from which text that \
                 interface was compiled"
                f u
            else
              match Src.standing ~file:f cmt with
              | Follows _ -> incr of_tree
              | List_of_modules s -> lists := s :: !lists
              | Refused _ -> ()))))
    loaded;
  !of_tree, List.sort compare !lists, !of_library

(* The comment under the header of a file of declarations: what the file is, and
   the text that it follows, by the name that Git gives that text. *)
let head_of_compiler ~name ~rel ~blob =
  [ "(* GENERATED, not written by hand: the declarations of what the port of";
    Printf.sprintf
      "   Simplify uses of the compiler's module [%s], after its interface" name;
    "   " ^ rel;
    Printf.sprintf "   (Git blob %s). Made by tools/declgen" blob;
    "   (see decl/README.md): a change is made there, not here. *)" ]

let head_of_local ~rel ~blob =
  [ "(* GENERATED, not written by hand: the declarations of the modules that";
    "   " ^ rel;
    Printf.sprintf "   (Git blob %s) makes for itself by" blob;
    "   applying a functor of another part of the compiler, and of what the";
    "   file uses of them. The port keeps the definitions of these modules as";
    "   they are in the file, and the realisations name them as the file does.";
    "   Made by tools/declgen (see decl/README.md): a change is made there,";
    "   not here. *)" ]

(* [digest]: the MD5 digest by which every compiled file that imports the
   interface names it ([ocamlobjinfo] prints it). *)
let head_of_library ~name ~rel ~blob ~digest =
  [ "(* GENERATED, not written by hand: the declarations of what the port of";
    Printf.sprintf
      "   Simplify uses of the standard library's module [%s]. Its names and"
      name;
    "   types are read from the compiled interface of that module in the";
    "   standard library of the OCaml that built the compiler, not from this";
    "   tree's stdlib/ (PROVENANCE.md, last section): the compiled interface";
    "   that the files of the build import by the MD5 digest";
    Printf.sprintf "   %s. The header above is that of this" digest;
    "   tree's file of the same name,";
    "   " ^ rel;
    Printf.sprintf "   (Git blob %s). Made by tools/declgen" blob;
    "   (see decl/README.md): a change is made there, not here. *)" ]

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
  let cmts = Array.to_list (Array.sub Sys.argv 4 (Array.length Sys.argv - 4)) in
  List.iter
    (fun f ->
      if not (Src.of_the_build f)
      then
        failwith
          (Printf.sprintf "%s is no file of the build root %s" f !build_root))
    cmts;
  let scanned = ref SS.empty in
  let last = ref None in
  let given_imports = ref [] in
  List.iter
    (fun f ->
      let cmt = Uses.scan f in
      scanned := SS.add cmt.cmt_modname !scanned;
      given_imports := (f, cmt.cmt_imports) :: !given_imports;
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
  (* IS THE BUILD A BUILD OF THESE SOURCES? What is found otherwise, and what
     cannot be known, is kept in [stale]. First the compiled interfaces that
     were loaded: the text of each, and that each is the one that the given
     typed trees were compiled against. *)
  let loaded = Env.imports () in
  let of_tree, lists, of_library = compare_loaded loaded in
  List.iter
    (fun (f, imports) ->
      List.iter
        (fun (u, digest) ->
          match digest, List.assoc_opt u loaded with
          | Some d, Some (Some d') when not (String.equal d d') ->
            stale
              := Printf.sprintf
                   "%s was compiled against another compiled interface of %s \
                    than the one that is read"
                   (Filename.basename f) u
                 :: !stale
          | _ -> ())
        imports)
    !given_imports;
  (* the file whose header the file of a unit carries, and whether it is the
     file from which the build compiled the interface that is read *)
  let sources = Hashtbl.create 97 in
  let source_of u =
    match Hashtbl.find_opt sources u with
    | Some found -> found
    | None ->
      let found =
        match Hashtbl.find_opt Sigs.locals u with
        | Some (_, file) -> Some file, true
        | None -> (
          match source_of_unit u with
          | Some (rel, compiled) -> Some rel, compiled
          | None -> None, true)
      in
      Hashtbl.replace sources u found;
      found
  in
  List.iter (fun (u, _, _) -> ignore (source_of u)) results;
  (* then what is read of the typed trees of implementations: for each declared
     value, the parameters of its realisation and of its definition; and the
     given files themselves: their record updates, their tokens and their
     items *)
  let arities =
    List.map
      (fun (comps, ocaml, rocq, wrapper) ->
        let definition, where = Arities.row comps in
        Printf.sprintf "%s\t%s\t%d\t%s\t%s" ocaml rocq wrapper definition where)
      !Decl_out.values
  in
  let donors = List.map Donors.read cmts in
  if !stale <> []
  then (
    prerr_endline
      "declgen: the build that is read is not known to be a build of these \
       sources:";
    List.iter
      (fun why -> prerr_endline ("  " ^ why))
      (List.sort_uniq compare !stale);
    prerr_endline "No file is written.";
    exit 2);
  (* the questions for a human, checked before any file is written: what a row
     says of its file against what is about to be written *)
  let without_line place =
    match String.rindex_opt place ':' with
    | Some i
      when i + 1 < String.length place
           && String.for_all
                (fun c -> c >= '0' && c <= '9')
                (String.sub place (i + 1) (String.length place - i - 1)) ->
      String.sub place 0 i
    | _ -> place
  in
  let known file =
    match List.find_opt (fun (u, _, _) -> Sigs.unit_rocq u = file) results with
    | None -> None
    | Some (u, _, _) ->
      let source, _ = source_of u in
      let header =
        match source with Some rel -> Src.header rel <> [] | None -> false
      in
      let declared =
        List.filter_map
          (fun (ocaml, rocq, _, _, place) ->
            if starts_with ~prefix:(file ^ ".") rocq
            then Some (ocaml, without_line place)
            else None)
          !Decl_out.index
      in
      Some { Crs.source; header; declared }
  in
  let crs =
    if Sys.getenv_opt "DECLGEN_SOME_FILES" <> None
    then (
      prerr_endline
        "a run on some of the files of Simplify: no question of crs.ml is \
         written";
      [])
    else Crs.checked ~known
  in
  let names = Hashtbl.create 97 in
  let files =
    List.map
      (fun (u, body, deps) ->
        let rocq = Sigs.unit_rocq u in
        (match Hashtbl.find_opt names rocq with
        | Some u' ->
          failwith (Printf.sprintf "two units for %s.v: %s and %s" rocq u u')
        | None -> Hashtbl.replace names rocq u);
        let source, compiled = source_of u in
        (* a unit of the standard library, and no other, has a file that the
           build did not compile *)
        let of_library =
          is_stdlib_unit u || starts_with ~prefix:"Camlinternal" u
        in
        if of_library && compiled
        then
          failwith
            (Printf.sprintf
               "%s is a unit of the standard library, and the tree's stdlib/ \
                file of the same name does not stand for its interface (%s)"
               u
               (Option.value ~default:"no source found" source));
        if (not of_library) && not compiled
        then
          failwith
            (Printf.sprintf
               "%s is no unit of the standard library, and its interface was \
                not compiled from a file of the tree (%s)"
               u
               (Option.value ~default:"no source found" source));
        (* the text that the file follows, and the name that Git gives it *)
        let rel =
          match source with
          | Some rel -> rel
          | None ->
            failwith
              (Printf.sprintf
                 "%s: no file of the tree was found from which the build \
                  compiled its interface, so its file of declarations can name \
                  none"
                 u)
        in
        let blob =
          match Src.blob rel with
          | Some blob -> blob
          | None -> failwith (Printf.sprintf "%s could not be read" rel)
        in
        let header = match Src.header rel with [] -> no_header | h -> h in
        let b = Buffer.create (String.length body + 4096) in
        let add_lines lines =
          List.iter (fun l -> Buffer.add_string b (l ^ "\n")) lines
        in
        add_lines header;
        (match List.assoc_opt rocq crs with
        | Some lines ->
          Buffer.add_char b '\n';
          add_lines lines
        | None -> ());
        Buffer.add_char b '\n';
        add_lines
          (if is_local_unit u
           then head_of_local ~rel ~blob
           else if not compiled
           then
             let digest =
               match List.assoc_opt u loaded with
               | Some (Some digest) -> Digest.to_hex digest
               | _ ->
                 failwith
                   (Printf.sprintf
                      "%s: the digest of its compiled interface is not known" u)
             in
             head_of_library ~name:(short_unit u) ~rel ~blob ~digest
           else head_of_compiler ~name:(short_unit u) ~rel ~blob);
        Buffer.add_char b '\n';
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
        rocq, Buffer.contents b)
      results
  in
  (* nothing is written before this line *)
  List.iter
    (fun (rocq, contents) ->
      write_file (Filename.concat out_dir (rocq ^ ".v")) contents)
    files;
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
  tsv "ARITIES.tsv" arities;
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
    passes;
  Printf.printf
    "%d compiled interfaces of the build were loaded: %d were compiled from \
     the text of the tree, %d are lists of the modules of a library that the \
     build wrote (named below); %d more are of the standard library of the \
     OCaml that made the build\n"
    (of_tree + List.length lists)
    of_tree (List.length lists) of_library;
  List.iter (fun s -> Printf.printf "list of modules: %s\n" s) lists
