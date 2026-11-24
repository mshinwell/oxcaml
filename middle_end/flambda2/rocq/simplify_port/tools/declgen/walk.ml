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
      | Some _, Public, _ -> Abbreviation
      | _, _, (Type_variant _ | Type_record _) when Emit_types.wanted comps ->
        Candidate
      | _ -> Abstract)

(* [canon]: the module of which the open module is an alias; the type is
   then the type of the same name there. [forbidden]: see [Emit_types]. *)
let emit_type ~forbidden ~canon modc name : (unit -> unit) option =
  let comps = modc @ [name] in
  let k = key comps in
  let ocaml = Print.ocaml_name comps in
  if type_in_kit comps
  then (
    line "(* type %s: in the kit (Port_monad.v). *)" ocaml;
    None)
  else
    match Env.find_type (Sigs.path_of_comps comps) !Sigs.base_env with
    | exception Not_found ->
      not_declared comps "the type is not found";
      None
    | decl -> (
      Tr.reset_vars ();
      let params = List.map Tr.var_name (type_params decl k) in
      let rname = claim (Sigs.type_rocq modc name) in
      let sort = String.concat " -> " (List.map (fun _ -> "Type") params @ ["Type"]) in
      let place = comment decl.type_loc ("type " ^ name) in
      let abstract gap =
        (match gap with
        | Some why -> line "(* PORT-GAP(type): %s. *)" why
        | None -> ());
        line "Parameter %s : %s." rname sort;
        extract_type rname ocaml (List.length params);
        add_index ocaml rname "type" (List.length params) place
      in
      let definition body =
        let binders =
          String.concat "" (List.map (fun p -> Printf.sprintf "(%s : Type) " p) params)
        in
        line "Definition %s %s: Type := %s." rname binders body;
        extract_type rname ocaml (List.length params);
        add_index ocaml rname "type" (List.length params) place
      in
      match canon, decl.type_manifest, decl.type_private with
      | Some target, _, _ ->
        Tr.need_type (target @ [name]);
        definition
          (String.concat " " (Print.global_name `Type (target @ [name]) :: params));
        None
      | None, Some ty, Public -> (
        try
          let body = Print.pp (Tr.tr ty) in
          if List.length (Tr.var_names ()) <> List.length params
          then raise (Tr.Unsupported "a type variable that is not a parameter");
          definition body;
          None
        with Tr.Unsupported why ->
          abstract (Some ("abstract here; its definition has " ^ why));
          None)
      | None, _, _ ->
        Emit_types.emit ~abstract ~params ~forbidden modc name decl rname place)

(* A recursive definition of types: the abstract ones first, then what is
   taken apart, then the abbreviations, then the makers. *)
let emit_group ~full ~canon modc names =
  let names = List.filter (fun n -> full || type_wanted (modc @ [n])) names in
  match canon with
  | Some _ ->
    List.iter (fun n -> ignore (emit_type ~forbidden:[] ~canon modc n)) names
  | None ->
    let kinds = List.map (fun n -> n, member_kind modc n) names in
    let abbreviations =
      List.filter_map
        (fun (n, k) -> if k = Abbreviation then Some (key (modc @ [n])) else None)
        kinds
    in
    List.iter
      (fun (n, k) ->
        if k = Abstract || k = In_kit
        then ignore (emit_type ~forbidden:[] ~canon modc n))
      kinds;
    let deferred = ref [] in
    let rec candidates = function
      | [] -> ()
      | (n, Candidate) :: rest ->
        let later =
          List.filter_map
            (fun (n', k) -> if k = Candidate then Some (key (modc @ [n'])) else None)
            rest
        in
        (match emit_type ~forbidden:(later @ abbreviations) ~canon modc n with
        | Some f -> deferred := f :: !deferred
        | None -> ());
        candidates rest
      | _ :: rest -> candidates rest
    in
    candidates kinds;
    List.iter
      (fun (n, k) ->
        if k = Abbreviation then ignore (emit_type ~forbidden:[] ~canon modc n))
      kinds;
    List.iter (fun f -> f ()) (List.rev !deferred)

(* Types of OCaml that no module declares. *)
let predef = ["char"; "float"; "int32"; "int64"; "nativeint"; "bytes"; "array"; "floatarray"]

let emit_predef () =
  List.iter
    (fun s ->
      if Hashtbl.mem Tr.needed_types (key ["Stdlib"; s])
      then (
        let rname = claim (Sigs.type_rocq ["Stdlib"] s) in
        line "(* the type [%s] that OCaml defines before any module *)" s;
        line "Parameter %s : %s." rname (if s = "array" then "Type -> Type" else "Type");
        extract_type rname s (if s = "array" then 1 else 0);
        add_index s rname "type" (if s = "array" then 1 else 0) "predefined"))
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
    let outer_mod = !Print.cur_mod and outer_rewrite = !Tr.rewrite in
    buf := Buffer.create 4096;
    declared := SS.empty;
    Print.cur_mod := modc;
    Tr.rewrite := rewrite;
    emit_items ~full ~canon modc sg;
    let body = Buffer.contents !buf in
    buf := outer_buf;
    declared := outer_declared;
    Print.cur_mod := outer_mod;
    Tr.rewrite := outer_rewrite;
    if body <> ""
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
      else
        line "(* module %s = %s: nothing of it is declared. *)" name
          (Print.ocaml_name target)
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
  buf := Buffer.create 65536;
  (match Sigs.module_shape [u] with
  | Signature sg ->
    Print.file_modules := module_names SS.empty sg [u];
    if u = "Stdlib" then emit_predef ();
    emit_items ~full ~canon:None [u] sg
  | _ -> warn "the unit %s has no plain signature" u);
  let body = Buffer.contents !buf in
  if body = ""
  then None
  else (
    emitted_now := SS.add u !emitted_now;
    Some (body, !Print.deps))
