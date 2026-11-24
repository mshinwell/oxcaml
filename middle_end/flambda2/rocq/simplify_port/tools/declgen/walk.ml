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

(* The walk of the signature of a compilation unit, in the order of the
   interface: what Simplify uses of it (or all of it, for a file of
   Simplify itself) is declared. This file follows no file of the
   compiler. *)

open Common
open Decl_out
module SS = Set.Make (String)

(* Modules and units that had something declared in the pass before: an
   alias is written only to one of them. *)
let emitted_before : SS.t ref = ref SS.empty

let emitted_now : SS.t ref = ref SS.empty

(* Modules and units that an alias in a file of Simplify names: they are
   written though nothing of them is declared. Kept from pass to pass. *)
let forced : SS.t ref = ref SS.empty

let force comps =
  let rec prefixes acc = function
    | [] -> []
    | x :: rest ->
      let p = acc @ [x] in
      p :: prefixes p rest
  in
  List.iter
    (fun p ->
      if not (SS.mem (key p) !forced)
      then (
        forced := SS.add (key p) !forced;
        Tr.changed := true))
    (prefixes [] comps)

let type_wanted comps =
  Hashtbl.mem Tr.needed_types (key comps) || Hashtbl.mem Uses.types (key comps)

(* Types that the kit gives. *)
let type_in_kit comps =
  match comps with
  | ["Stdlib"; "ref"] | ["Stdlib__Lazy"; "t"] | ["CamlinternalLazy"; "t"] -> true
  | _ -> Tr.format_arity comps <> None

let type_params (decl : Types.type_declaration) k =
  List.filteri (fun i _ -> not (Tr.is_dropped k i)) decl.type_params

type member = In_kit | Abbreviation | Candidate | Abstract

let member_kind modc name =
  let comps = modc @ [name] in
  if type_in_kit comps
  then In_kit
  else
    match Env.find_type (Sigs.path_of_comps comps) !Sigs.base_env with
    | exception Not_found -> Abstract
    | decl -> (
      match decl.type_manifest, decl.type_private, decl.type_kind with
      | Some ty, priv, kind
        when priv = Asttypes.Public
             || (match kind with Type_variant _ | Type_record _ -> true | _ -> false)
        -> (
        (* [type t = M.t = private A | B]: the equation holds though the
           constructors are private *)
        Tr.reset_vars ();
        match Tr.tr ty, kind with
        | _ -> Abbreviation
        | exception Tr.Unsupported _ -> (
          (* a variant given again from a type that has no name here (the
             result of a functor): its own constructors are what there is *)
          match kind with
          | (Type_variant _ | Type_record _) when Emit_types.wanted comps -> Candidate
          | _ -> Abstract))
      | _, _, (Type_variant _ | Type_record _) when Emit_types.wanted comps ->
        Candidate
      | _ -> Abstract)

(* The instances of a dropped index of the type that the interfaces write:
   each an abbreviation of the type, with the instance as its string. *)
let emit_instances comps params rname place =
  match Hashtbl.find_opt Tr.instances (key comps) with
  | None -> ()
  | Some l ->
    let modc, name = Print.split_last comps in
    let ocaml = Print.ocaml_name comps in
    List.iter
      (fun (suffix, positional) ->
        let icomps = modc @ [name ^ "_" ^ suffix] in
        let iname = claim (Sigs.type_rocq modc (name ^ "_" ^ suffix)) in
        Print.set_type_name icomps iname;
        let n = ref 0 in
        let args =
          List.map
            (function
              | Some s -> s
              | None ->
                incr n;
                Printf.sprintf "'a%d" !n)
            positional
        in
        let applied =
          match args with
          | [a] -> a ^ " " ^ ocaml
          | _ -> "(" ^ String.concat ", " args ^ ") " ^ ocaml
        in
        line
          "(* [%s] where the interface writes this instance of the index that \
           Rocq does not have. *)"
          rname;
        line "Definition %s %s: Type := %s." iname
          (String.concat "" (List.map (fun p -> Printf.sprintf "(%s : Type) " p) params))
          (String.concat " " (rname :: params));
        if params = []
        then extract iname applied
        else
          line "Extract Constant %s %s => %s." iname
            (String.concat " "
               (List.mapi (fun i _ -> Print.quote (Printf.sprintf "'a%d" (i + 1))) params))
            (Print.quote applied);
        add_index applied iname "type" (List.length params) place)
      (List.sort compare l)

(* An abstract type: the parameter and its directive. *)
let declare_abstract comps (decl : Types.type_declaration) params rname place =
  let k = key comps in
  let sort = String.concat " -> " (List.map (fun _ -> "Type") params @ ["Type"]) in
  line "Parameter %s : %s." rname sort;
  extract_type
    ~kept:(List.mapi (fun i _ -> not (Tr.is_dropped k i)) decl.type_params)
    rname (Print.ocaml_name comps) (List.length params);
  add_index (Print.ocaml_name comps) rname "type" (List.length params) place;
  emit_instances comps params rname place

(* A type that is abstract, or an abbreviation. [canon]: the module of
   which the open module is an alias; the type is then the type of the same
   name there. [gap]: why it is abstract though Simplify takes it apart. *)
let emit_type ?gap ~canon modc name =
  let comps = modc @ [name] in
  let k = key comps in
  let ocaml = Print.ocaml_name comps in
  if type_in_kit comps
  then line "(* type %s: in the kit (Port_monad.v). *)" ocaml
  else
    match Env.find_type (Sigs.path_of_comps comps) !Sigs.base_env with
    | exception Not_found -> not_declared comps "the type is not found"
    | decl -> (
      Tr.reset_vars ();
      let params = List.map Tr.var_name (type_params decl k) in
      let rname = claim (Sigs.type_rocq modc name) in
      Print.set_type_name comps rname;
      let place = comment decl.type_loc ("type " ^ name) in
      let abstract gap =
        (match gap with
        | Some why -> line "(* PORT-GAP(type): %s. *)" why
        | None -> ());
        declare_abstract comps decl params rname place
      in
      let definition body =
        let binders =
          String.concat "" (List.map (fun p -> Printf.sprintf "(%s : Type) " p) params)
        in
        line "Definition %s %s: Type := %s." rname binders body;
        extract_type rname ocaml (List.length params);
        add_index ocaml rname "type" (List.length params) place;
        emit_instances comps params rname place
      in
      match canon, decl.type_manifest, decl.type_private with
      | Some target, _, _ ->
        Tr.need_type (target @ [name]);
        definition
          (String.concat " " (Print.global_name `Type (target @ [name]) :: params))
      | None, Some ty, priv
        when gap = None
             && (priv = Asttypes.Public
                || match decl.type_kind with
                   | Type_variant _ | Type_record _ -> true
                   | _ -> false) -> (
        try
          let body = Print.pp (Tr.tr ty) in
          if List.length (Tr.var_names ()) <> List.length params
          then raise (Tr.Unsupported "a type variable that is not a parameter");
          definition body
        with Tr.Unsupported why ->
          let n = String.length why and suffix = "is not a global name" in
          let k = String.length suffix in
          if n > k && String.sub why (n - k) k = suffix
          then (
            (* not a gap: the type is that of the result of a functor *)
            line "(* abstract here: it is %s. *)" why;
            abstract None)
          else abstract (Some ("abstract here; its definition has " ^ why)))
      | None, _, _ ->
        (match decl.type_manifest with
        | Some ty when gap = None ->
          (* said when the generator runs: a type that is equal to another
             in OCaml and abstract here *)
          warn "abstract though it has a definition: %s = %s%s" ocaml
            (if decl.type_private = Asttypes.Private then "private " else "")
            (Format.asprintf "%a" Printtyp.type_expr ty)
        | _ -> ());
        abstract gap)

(* ---- a recursive definition of types ---- *)

type candidate =
  { c_name : string;
    c_comps : string list;
    c_decl : Types.type_declaration;
    c_params : string list;
    c_vars : (int * string) list;
    c_shape : Emit_types.shape;
    mutable c_fallback : string option
  }

(* The strongly connected components of a graph; a component comes after
   those that it depends on. *)
let components (nodes : string list) (deps : string -> string list) =
  let index = Hashtbl.create 17 and low = Hashtbl.create 17 in
  let stack = ref [] and counter = ref 0 and out = ref [] in
  let rec visit v =
    Hashtbl.replace index v !counter;
    Hashtbl.replace low v !counter;
    incr counter;
    stack := v :: !stack;
    List.iter
      (fun w ->
        if not (Hashtbl.mem index w)
        then (
          visit w;
          Hashtbl.replace low v (min (Hashtbl.find low v) (Hashtbl.find low w)))
        else if List.mem w !stack
        then Hashtbl.replace low v (min (Hashtbl.find low v) (Hashtbl.find index w)))
      (deps v);
    if Hashtbl.find low v = Hashtbl.find index v
    then (
      let rec pop acc =
        match !stack with
        | w :: rest ->
          stack := rest;
          if w = v then w :: acc else pop (w :: acc)
        | [] -> acc
      in
      out := pop [] :: !out)
  in
  List.iter (fun v -> if not (Hashtbl.mem index v) then visit v) nodes;
  List.rev !out

(* A type that Simplify takes apart: its shape, if all of it can be
   written; the reason if not. *)
let gather modc name =
  let comps = modc @ [name] in
  let decl = Env.find_type (Sigs.path_of_comps comps) !Sigs.base_env in
  Tr.reset_vars ();
  let params = List.map Tr.var_name (type_params decl (key comps)) in
  match Emit_types.shape_of decl with
  | exception Tr.Unsupported why -> Error why
  | None -> Error "a definition that is neither a variant nor a record"
  | Some sh -> (
    match List.iter (fun t -> ignore (Print.pp t)) (Emit_types.types_of sh) with
    | exception Tr.Unsupported why -> Error why
    | () ->
      Ok
        { c_name = name;
          c_comps = comps;
          c_decl = decl;
          c_params = params;
          c_vars = !Tr.vars;
          c_shape = sh;
          c_fallback = None
        })

(* The comment and the name of a type that is about to be declared. *)
let start modc c =
  Tr.vars := c.c_vars;
  let rname = claim (Sigs.type_rocq modc c.c_name) in
  Print.set_type_name c.c_comps rname;
  let place = comment c.c_decl.type_loc ("type " ^ c.c_name) in
  rname, place

let makers modc c rname place () =
  Tr.vars := c.c_vars;
  try
    Emit_types.emit_makers ~params:c.c_params
      ~private_:(c.c_decl.type_private = Asttypes.Private)
      modc c.c_name rname c.c_shape place
  with Tr.Unsupported why -> not_declared (c.c_comps @ ["(makers)"]) why

let deferred : (unit -> unit) list ref = ref []

(* Abstract, with makers and an eliminator (written after the whole
   definition). *)
let emit_fallback modc c why =
  let rname, place = start modc c in
  line
    "(* PORT-GAP(type): %s: abstract, with a maker for each constructor and one \
     eliminator. *)"
    why;
  declare_abstract c.c_comps c.c_decl c.c_params rname place;
  deferred := makers modc c rname place :: !deferred

(* A module inside a file whose name in Rocq is not OCaml's (a word of
   Rocq): Rocq would print what is in it under the wrong name. *)
let in_renamed_module modc =
  match modc with
  | _ :: mods -> List.exists (fun m -> Sigs.module_rocq m <> m) mods
  | [] -> false

let emit_native_record modc c =
  let fields = match c.c_shape with Record l -> l | Variant _ -> assert false in
  let names = List.map (fun (f, _, _) -> f) fields in
  if in_renamed_module modc
  then
    emit_fallback modc c
      "its module has another name in Rocq, under which Rocq would print its fields"
  else if List.for_all Emit_types.free names && Emit_types.distinct names
  then (
    let rname, place = start modc c in
    Emit_types.emit_record ~params:c.c_params modc rname fields place;
    Emit_types.mirror c.c_comps)
  else emit_fallback modc c "the name of a field of it is taken in Rocq"

(* One variant, or several that are defined together. *)
let emit_native_variants modc cs =
  let started = List.map (fun c -> c, start modc c) cs in
  let prepared =
    List.map
      (fun (c, (rname, place)) ->
        Tr.vars := c.c_vars;
        let ctors = match c.c_shape with Variant l -> l | Record _ -> assert false in
        let rows =
          Emit_types.prepare_variant ~params:c.c_params modc rname ctors place
        in
        c, rname, ctors, rows)
      started
  in
  let last = List.length prepared - 1 in
  List.iteri
    (fun i (c, rname, _, rows) ->
      line "%s %s%s : Type :=" (if i = 0 then "Inductive" else "with") rname
        (Emit_types.binders c.c_params);
      let n = List.length rows in
      if n = 0 && i = last then line ".";
      List.iteri
        (fun j (_, r) -> line "%s%s" r (if i = last && j = n - 1 then "." else ""))
        rows)
    prepared;
  List.iter
    (fun (c, rname, ctors, rows) ->
      List.iter (fun (cname, _) -> Emit_types.implicit cname c.c_params) rows;
      Emit_types.extract_inductive modc c.c_name rname (Print.ocaml_name c.c_comps)
        (List.length c.c_decl.type_params) ctors;
      Emit_types.mirror c.c_comps)
    prepared

(* A recursive definition of types: the abstract ones first; then what
   Simplify takes apart and the abbreviations, each after what it
   mentions; then the makers. Types that mention each other are an
   inductive definition with several types if they are all variants;
   through a record or an abbreviation, they are abstract. *)
let emit_group ~full ~canon modc names =
  let names = List.filter (fun n -> full || type_wanted (modc @ [n])) names in
  match canon with
  | Some _ -> List.iter (fun n -> emit_type ~canon modc n) names
  | None ->
    let kinds = List.map (fun n -> n, member_kind modc n) names in
    List.iter
      (fun (n, k) -> if k = Abstract || k = In_kit then emit_type ~canon modc n)
      kinds;
    let cands =
      List.filter_map
        (fun (n, k) ->
          if k <> Candidate
          then None
          else
            match gather modc n with
            | Ok c -> Some c
            | Error why ->
              emit_type
                ~gap:("abstract, though Simplify takes it apart: its definition has " ^ why)
                ~canon modc n;
              None)
        kinds
    in
    let abbreviations =
      List.filter_map (fun (n, k) -> if k = Abbreviation then Some n else None) kinds
    in
    let ckey c = key c.c_comps in
    let akey n = key (modc @ [n]) in
    List.iter
      (fun c -> c.c_fallback <- Emit_types.structural (ckey c) c.c_shape)
      cands;
    let abbreviation_types n =
      match (Env.find_type (Sigs.path_of_comps (modc @ [n])) !Sigs.base_env).type_manifest with
      | Some ty -> ( try [Tr.tr ty] with Tr.Unsupported _ -> [])
      | None -> []
      | exception Not_found -> []
    in
    let rec decide () =
      let natives = List.filter (fun c -> c.c_fallback = None) cands in
      let nodes = List.map ckey natives @ List.map akey abbreviations in
      let types_of_node k =
        match List.find_opt (fun c -> ckey c = k) natives with
        | Some c -> Emit_types.types_of c.c_shape
        | None -> (
          match List.find_opt (fun n -> akey n = k) abbreviations with
          | Some n -> abbreviation_types n
          | None -> [])
      in
      let deps k =
        let tys = types_of_node k in
        List.filter
          (fun k' -> k' <> k && List.exists (Emit_types.mentions k') tys)
          nodes
      in
      let sccs = components nodes deps in
      let again = ref false in
      List.iter
        (fun scc ->
          if List.length scc > 1
          then (
            let members = List.filter (fun c -> List.mem (ckey c) scc) natives in
            let refuse c why =
              c.c_fallback <- Some why;
              again := true
            in
            let is_record c =
              match c.c_shape with Emit_types.Record _ -> true | Variant _ -> false
            in
            if List.exists (fun n -> List.mem (akey n) scc) abbreviations
            then
              List.iter
                (fun c -> refuse c "it is recursive with other types through an abbreviation")
                members
            else if List.exists is_record members
            then
              List.iter
                (fun c ->
                  if is_record c
                  then refuse c "it is a record that is recursive with other types")
                members
            else if List.exists (fun c -> c.c_params <> (List.hd members).c_params) members
            then
              List.iter
                (fun c -> refuse c "it is recursive with types of other parameters")
                members
            else
              List.iter
                (fun c ->
                  if List.exists
                       (fun k ->
                         List.exists (Emit_types.refused_place k)
                           (Emit_types.types_of c.c_shape))
                       scc
                  then
                    refuse c
                      "it holds a type of its recursive definition inside an abstract type")
                members))
        sccs;
      if !again then decide () else sccs
    in
    let sccs = decide () in
    let outer_deferred = !deferred in
    deferred := [];
    List.iter
      (fun c ->
        match c.c_fallback with Some why -> emit_fallback modc c why | None -> ())
      cands;
    List.iter
      (fun scc ->
        match List.find_opt (fun n -> List.mem (akey n) scc) abbreviations with
        | Some n -> emit_type ~canon modc n
        | None -> (
          let members =
            List.filter (fun c -> c.c_fallback = None && List.mem (ckey c) scc) cands
          in
          match members with
          | [] -> ()
          | [({ c_shape = Record _; _ } as c)] -> emit_native_record modc c
          | _ -> emit_native_variants modc members))
      sccs;
    List.iter (fun f -> f ()) (List.rev !deferred);
    deferred := outer_deferred

(* Types of OCaml that no module declares. *)
let predef = ["char"; "float"; "int32"; "int64"; "nativeint"; "bytes"; "floatarray"]

let emit_predef () =
  List.iter
    (fun s ->
      if Hashtbl.mem Tr.needed_types (key ["Stdlib"; s])
      then (
        let rname = claim (Sigs.type_rocq ["Stdlib"] s) in
        line "(* the type [%s] that OCaml defines before any module *)" s;
        line "Parameter %s : Type." rname;
        extract_type rname s 0;
        add_index s rname "type" 0 "predefined"))
    predef

let rec emit_items ~full ~canon modc (sg : Types.signature) =
  let rec go (items : Types.signature_item list) =
    match items with
    | [] -> ()
    | Sig_type (id, _, _, Exported) :: rest ->
      let rec take acc (items : Types.signature_item list) =
        match items with
        | Sig_type (id', _, Trec_next, Exported) :: rest ->
          take (Ident.name id' :: acc) rest
        | rest -> List.rev acc, rest
      in
      let group, rest = take [Ident.name id] rest in
      emit_group ~full ~canon modc group;
      go rest
    | item :: rest ->
      (match item with
      | Sig_value (id, _, Exported) ->
        let name = Ident.name id in
        if full || Hashtbl.mem Uses.values (key (modc @ [name]))
        then emit_value modc name
      | Sig_typext (id, ext, Text_exception, Exported) ->
        let name = Ident.name id in
        if full || Hashtbl.mem Uses.exceptions (key (modc @ [name]))
        then emit_exception modc name ext
      | Sig_module (id, _, _, _, Exported) ->
        let name = Ident.name id in
        emit_module ~full
          ~canon:(Option.map (fun t -> t @ [name]) canon)
          (modc @ [name])
      | Sig_modtype (id, _, Exported) ->
        if full then not_declared (modc @ [Ident.name id]) "a module type"
      | _ -> ());
      go rest
  in
  go sg

and emit_module ~full ~canon modc =
  let name = List.nth modc (List.length modc - 1) in
  let body ~canon ~rewrite sg =
    let outer_buf = !buf and outer_declared = !declared in
    let outer_native = !native in
    let outer_mod = !Print.cur_mod and outer_rewrite = !Tr.rewrite in
    buf := Buffer.create 4096;
    declared := SS.empty;
    native := SS.empty;
    Print.cur_mod := modc;
    Tr.rewrite := rewrite;
    emit_items ~full ~canon modc sg;
    let body = Buffer.contents !buf in
    buf := outer_buf;
    declared := outer_declared;
    native := outer_native;
    Print.cur_mod := outer_mod;
    Tr.rewrite := outer_rewrite;
    if body <> "" || SS.mem (key modc) !forced
    then (
      emitted_now := SS.add (key modc) !emitted_now;
      (match canon with
      | Some target ->
        line "(* module %s = %s: declared again here under this name. *)" name
          (Print.ocaml_name target)
      | None -> ());
      line "Module %s." (Sigs.module_rocq name);
      Buffer.add_string !buf body;
      line "End %s." (Sigs.module_rocq name))
  in
  match Sigs.module_shape modc with
  | Signature sg -> body ~canon ~rewrite:None sg
  | Alias (Some target) -> (
    if full
    then
      let target = Option.value ~default:target (Sigs.alias_as_written modc) in
      if SS.mem (key target) !emitted_before
      then (
        let rocq =
          match target with
          | u :: mods ->
            String.concat "." (Print.unit_ref u :: List.map Sigs.module_rocq mods)
          | [] -> ""
        in
        line "(* module %s = %s *)" name (Print.ocaml_name target);
        line "Module %s := %s." (Sigs.module_rocq name) rocq)
      else (
        force target;
        line "(* module %s = %s: nothing of it is declared. *)" name
          (Print.ocaml_name target))
    else
      (* an alias inside another interface: its items are declared again
         under the alias, the types as the types of the module itself *)
      match Sigs.module_shape target with
      | Signature sg -> body ~canon:(Some target) ~rewrite:(Some (target, modc)) sg
      | _ -> ())
  | Functor -> if full then not_declared modc "a functor"
  | Alias None | Opaque ->
    if full then not_declared modc "a module whose signature is not a plain one"

let rec module_names acc (sg : Types.signature) modc =
  List.fold_left
    (fun acc (item : Types.signature_item) ->
      match item with
      | Sig_module (id, _, _, _, _) -> (
        let name = Ident.name id in
        let acc = SS.add (Sigs.module_rocq name) acc in
        match Sigs.module_shape (modc @ [name]) with
        | Signature sg -> module_names acc sg (modc @ [name])
        | _ -> acc)
      | _ -> acc)
    acc sg

(* The declarations of a unit and the units that they name. *)
let emit_unit ~full u : (string * SS.t) option =
  Print.cur_unit := u;
  Print.cur_mod := [u];
  Print.deps := SS.empty;
  declared := SS.empty;
  native := SS.empty;
  buf := Buffer.create 65536;
  (match Sigs.module_shape [u] with
  | Signature sg ->
    Print.file_modules := module_names SS.empty sg [u];
    if u = "Stdlib" then emit_predef ();
    emit_items ~full ~canon:None [u] sg
  | _ -> warn "the unit %s has no plain signature" u);
  let body = Buffer.contents !buf in
  if body = "" && not (SS.mem u !forced)
  then None
  else (
    emitted_now := SS.add u !emitted_now;
    Some (body, !Print.deps))

(* ---- what a file of Simplify makes for itself with a functor of outside ---- *)

let local_env_cache : (string, Env.t) Hashtbl.t = Hashtbl.create 17

let env_of_root (r : Sigs.local_root) =
  match Hashtbl.find_opt local_env_cache (key r.l_comps) with
  | Some e -> e
  | None ->
    let e = try Envaux.env_of_only_summary r.l_env with _ -> r.l_env in
    Hashtbl.replace local_env_cache (key r.l_comps) e;
    e

(* A module of the file that only holds such modules. *)
let nested modc f =
  let name = List.nth modc (List.length modc - 1) in
  let outer_buf = !buf and outer_declared = !declared in
  let outer_native = !native and outer_mod = !Print.cur_mod in
  buf := Buffer.create 4096;
  declared := SS.empty;
  native := SS.empty;
  Print.cur_mod := modc;
  f ();
  let body = Buffer.contents !buf in
  buf := outer_buf;
  declared := outer_declared;
  native := outer_native;
  Print.cur_mod := outer_mod;
  if body <> ""
  then (
    line "Module %s." (Sigs.module_rocq name);
    Buffer.add_string !buf body;
    line "End %s." (Sigs.module_rocq name))

(* The declarations of the unit [FILE__local]: for each module that the
   file makes with a functor of outside (or that has such an [include]),
   what the file uses of it. The realisations name the module as the file
   does: the port keeps the module's definition as it is. *)
let emit_local_unit u : (string * SS.t) option =
  match Hashtbl.find_opt Sigs.locals u with
  | None -> None
  | Some (roots, _) ->
    Print.cur_unit := u;
    Print.cur_mod := [u];
    Print.deps := SS.empty;
    declared := SS.empty;
    native := SS.empty;
    buf := Buffer.create 65536;
    local_idents := List.map (fun (r : Sigs.local_root) -> r.l_id, r.l_comps) roots;
    Print.file_modules
      := List.fold_left
           (fun acc (r : Sigs.local_root) ->
             List.fold_left
               (fun acc m -> SS.add (Sigs.module_rocq m) acc)
               acc (List.tl r.l_comps))
           SS.empty roots;
    let saved_env = !Sigs.base_env in
    let emit_root (r : Sigs.local_root) =
      Sigs.base_env := env_of_root r;
      let modc, name = Print.split_last r.l_comps in
      match r.l_kind with
      | `Module ->
        line "(* module %s, lines %d-%d of the file *)" name r.l_line r.l_last_line;
        emit_module ~full:false ~canon:None r.l_comps
      | `Value ->
        if Hashtbl.mem Uses.values (key r.l_comps) then emit_value modc name
      | `Type ->
        if type_wanted r.l_comps then emit_group ~full:false ~canon:None modc [name]
    in
    let rec at prefix (rs : Sigs.local_root list) =
      match rs with
      | [] -> ()
      | r :: rest ->
        let depth = List.length prefix in
        if List.length r.l_comps = depth + 1
        then (
          emit_root r;
          at prefix rest)
        else
          let next = List.nth r.l_comps depth in
          let inside, others =
            List.partition
              (fun (r' : Sigs.local_root) ->
                List.length r'.l_comps > depth + 1 && List.nth r'.l_comps depth = next)
              rs
          in
          nested (prefix @ [next]) (fun () -> at (prefix @ [next]) inside);
          at prefix others
    in
    at [u] roots;
    Sigs.base_env := saved_env;
    local_idents := [];
    let body = Buffer.contents !buf in
    if body = "" then None else Some (body, !Print.deps)
