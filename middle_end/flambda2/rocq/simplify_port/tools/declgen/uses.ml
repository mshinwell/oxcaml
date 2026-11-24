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

(* What the files of Simplify use of other compilation units: every value,
   every constructor built or matched, every field read, built or written,
   every type written, every exception. Read from the typed trees. This
   file follows no file of the compiler. *)

open Typedtree
open Common
module SS = Set.Make (String)

type type_use =
  { comps : string list;
    mutable built : SS.t;
    mutable matched : SS.t;
    mutable fields : SS.t;
    mutable fields_written : SS.t
  }

(* key of the name -> the name and the files that use it *)
let values : (string, string list * SS.t ref) Hashtbl.t = Hashtbl.create 997

let types : (string, type_use) Hashtbl.t = Hashtbl.create 997

let exceptions : (string, string list) Hashtbl.t = Hashtbl.create 17

let cur_file = ref ""

let use_value comps =
  match Hashtbl.find_opt values (key comps) with
  | Some (_, files) -> files := SS.add !cur_file !files
  | None -> Hashtbl.replace values (key comps) (comps, ref (SS.singleton !cur_file))

let type_use comps =
  match Hashtbl.find_opt types (key comps) with
  | Some u -> u
  | None ->
    let u =
      { comps;
        built = SS.empty;
        matched = SS.empty;
        fields = SS.empty;
        fields_written = SS.empty
      }
    in
    Hashtbl.replace types (key comps) u;
    u

(* The type that declares the constructors: [type t = M.t = A | B] is
   followed to [M.t]. *)
let rec canon_type env p =
  let p = norm_type env p in
  match Env.find_type p env with
  | { type_manifest = Some ty; type_kind = Type_variant _ | Type_record _; _ }
    -> (
    match Types.get_desc ty with
    | Tconstr (p', _, _) ->
      (* (not through the application of a functor: that has no name) *)
      let c = canon_type env p' in
      if comps_of_path c = None then p else c
    | _ -> p)
  | _ -> p
  | exception Not_found -> p

let type_comps env p = comps_of_path (canon_type (env_of env) p)

let exception_comps env (p : Path.t) =
  match p with
  | Pident id when Ident.is_predef id -> Some ["%predef"; Ident.name id]
  | Pdot (m, s) -> (
    match comps_of_path (norm_module (env_of env) m) with
    | Some l -> Some (l @ [s])
    | None -> None)
  | _ -> None

let constructor env (cd : Data_types.constructor_description) how =
  match cd.cstr_tag with
  | Cstr_extension (p, _) -> (
    match exception_comps env p with
    | Some comps -> Hashtbl.replace exceptions (key comps) comps
    | None -> ())
  | Cstr_constant _ | Cstr_block _ | Cstr_unboxed -> (
    match type_comps env (Data_types.cstr_res_type_path cd) with
    | None -> ()
    (* the constructors of a format string: the port writes a string *)
    | Some ("CamlinternalFormatBasics" :: _) -> ()
    | Some comps -> (
      let u = type_use comps in
      match how with
      | `Built -> u.built <- SS.add cd.cstr_name u.built
      | `Matched -> u.matched <- SS.add cd.cstr_name u.matched))

let field env (l : Data_types.label_description) how =
  match type_comps env (Data_types.lbl_res_type_path l) with
  | None -> ()
  | Some comps -> (
    let u = type_use comps in
    u.fields <- SS.add l.lbl_name u.fields;
    match how with
    | `Written -> u.fields_written <- SS.add l.lbl_name u.fields_written
    | `Read -> ())

(* ---- what a file makes for itself with a functor of outside ---- *)

(* The unit [FILE__local] of the file that is being read. *)
let pseudo = ref ""

let functor_depth = ref 0

(* The plain modules of the file that the place is inside, innermost
   first. *)
let enclosing : string list ref = ref []

let in_root = ref false

(* The environments at the end of the structures that the place is
   inside, innermost first. *)
let final_envs : Env.t list ref = ref []

let roots : Sigs.local_root list ref = ref []

(* Such modules that are inside a functor of the file: they depend on its
   parameter and cannot be declared apart. Place, and what. *)
let inside_functor : (string * string) list ref = ref []

let register kind name id (loc : Location.t) =
  let comps = (!pseudo :: List.rev !enclosing) @ [name] in
  let env = match !final_envs with e :: _ -> e | [] -> Env.empty in
  roots
    := { Sigs.l_comps = comps;
         l_id = id;
         l_env = env;
         l_kind = kind;
         l_line = loc.loc_start.pos_lnum;
         l_last_line = loc.loc_end.pos_lnum
       }
       :: !roots;
  local_idents := (id, comps) :: !local_idents

let rec strip (me : module_expr) =
  match me.mod_desc with Tmod_constraint (me, _, _, _) -> strip me | _ -> me

(* Is the module the application of a functor of outside Simplify? *)
let outside_application (me : module_expr) =
  let rec head (me : module_expr) =
    let me = strip me in
    match me.mod_desc with
    | Tmod_apply (f, _, _) | Tmod_apply_unit f -> head f
    | Tmod_ident (p, _) -> Some (me.mod_env, p)
    | _ -> None
  in
  match (strip me).mod_desc with
  | Tmod_apply _ | Tmod_apply_unit _ -> (
    match head me with
    | Some (env, p) -> (
      match comps_of_path (source_module (env_of env) p) with
      | Some (u :: _) -> not (is_simplify_unit u)
      | _ -> false)
    | None -> false)
  | _ -> false

let iterator =
  let super = Tast_iterator.default_iterator in
  let structure sub (str : structure) =
    final_envs := str.str_final_env :: !final_envs;
    super.structure sub str;
    final_envs := List.tl !final_envs
  in
  let module_expr sub (me : module_expr) =
    match me.mod_desc with
    | Tmod_functor _ ->
      incr functor_depth;
      super.module_expr sub me;
      decr functor_depth
    | _ -> super.module_expr sub me
  in
  let structure_item sub (si : structure_item) =
    match si.str_desc with
    | Tstr_module ({ mb_id = Some id; _ } as mb) ->
      let name = Ident.name id in
      let me = strip mb.mb_expr in
      let by_include =
        match me.mod_desc with
        | Tmod_structure str ->
          List.exists
            (fun (i : structure_item) ->
              match i.str_desc with
              | Tstr_include incl -> outside_application incl.incl_mod
              | _ -> false)
            str.str_items
        | _ -> false
      in
      if (outside_application mb.mb_expr || by_include) && not !in_root
      then
        if !functor_depth > 0
        then (
          inside_functor
            := ( Printf.sprintf "%s:%d" !cur_file si.str_loc.loc_start.pos_lnum,
                 "module " ^ name )
               :: !inside_functor;
          super.structure_item sub si)
        else (
          register `Module name id si.str_loc;
          in_root := true;
          super.structure_item sub si;
          in_root := false)
      else (
        match me.mod_desc with
        | Tmod_structure _ ->
          enclosing := name :: !enclosing;
          super.structure_item sub si;
          enclosing := List.tl !enclosing
        | _ -> super.structure_item sub si)
    | Tstr_include incl
      when !enclosing = [] && (not !in_root) && !functor_depth = 0
           && outside_application incl.incl_mod ->
      List.iter
        (fun (item : Types.signature_item) ->
          match item with
          | Sig_value (id, _, _) -> register `Value (Ident.name id) id si.str_loc
          | Sig_type (id, _, _, _) -> register `Type (Ident.name id) id si.str_loc
          | Sig_module (id, _, _, _, _) ->
            register `Module (Ident.name id) id si.str_loc
          | _ -> ())
        incl.incl_type;
      super.structure_item sub si
    | _ -> super.structure_item sub si
  in
  let expr sub (e : expression) =
    (match e.exp_desc with
    | Texp_ident (p, _, _) -> (
      match comps_of_path (source_path (env_of e.exp_env) p) with
      | Some comps -> use_value comps
      | None -> ())
    | Texp_construct (_, cd, _) -> constructor e.exp_env cd `Built
    | Texp_record { fields; _ } ->
      Array.iter (fun (l, _) -> field e.exp_env l `Read) fields
    | Texp_field (_, _, l) -> field e.exp_env l `Read
    | Texp_setfield (_, _, l, _) -> field e.exp_env l `Written
    | Texp_letop { let_; ands; _ } ->
      List.iter
        (fun (b : binding_op) ->
          match comps_of_path (source_path (env_of e.exp_env) b.bop_op_path) with
          | Some comps -> use_value comps
          | None -> ())
        (let_ :: ands)
    | _ -> ());
    super.expr sub e
  in
  let pat : type k. Tast_iterator.iterator -> k general_pattern -> unit =
   fun sub p ->
    (match p.pat_desc with
    | Tpat_construct (_, cd, _, _) -> constructor p.pat_env cd `Matched
    | Tpat_record (fields, _) ->
      List.iter (fun (_, l, _) -> field p.pat_env l `Read) fields
    | _ -> ());
    super.pat sub p
  in
  let typ sub (ct : core_type) =
    (match ct.ctyp_desc with
    | Ttyp_constr (p, _, _) -> (
      match comps_of_path (source_path (env_of ct.ctyp_env) p) with
      | Some comps -> ignore (type_use comps)
      | None -> ())
    | _ -> ());
    super.typ sub ct
  in
  { super with expr; pat; typ; structure; structure_item; module_expr }

(* Reads one typed tree. Returns the unit's name. *)
let scan file =
  let cmt = Cmt_format.read_cmt file in
  cur_file := Option.value ~default:file cmt.cmt_sourcefile;
  init_load_path cmt;
  Envaux.reset_cache ();
  env_cache := [];
  pseudo := cmt.cmt_modname ^ "__local";
  local_idents := [];
  roots := [];
  functor_depth := 0;
  enclosing := [];
  in_root := false;
  final_envs := [];
  (match cmt.cmt_annots with
  | Implementation str -> iterator.structure iterator str
  | _ -> warn "not an implementation: %s" file);
  if !roots <> [] then Hashtbl.replace Sigs.locals !pseudo (List.rev !roots, !cur_file);
  local_idents := [];
  cmt
