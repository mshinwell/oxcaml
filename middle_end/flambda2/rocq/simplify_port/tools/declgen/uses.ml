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

(* ---- what a functor of the file uses of the modules that it is given ---- *)

(* A file of Simplify that has a functor of its own and applies it
   ([Edge (Name.Map) (Name.Set)] in data_flow_graph.ml) uses, of the
   modules that it gives, what the body of the functor uses of its
   parameters: [Src_map.find] is then [Name.Map.find]. The module that is
   given may itself be made in the file (a structure written in the place,
   the result of another functor of the file), so the modules of the file
   are followed. What a module of the file is: *)
type modval =
  | Path of Env.t * Path.t  (** a module with a name, in an environment *)
  | Under of Ident.t * string list
      (** a module under a parameter of a functor of the file *)
  | Struct of (string * modval) list  (** a structure: its modules *)
  | Applied of Ident.t * modval list  (** a functor of the file, applied *)
  | Own  (** what the file defines itself: nothing of outside *)
  | Unknown

(* The parameters of the functors of the file. *)
let params : Ident.t list ref = ref []

(* The modules of the file that are not functors. *)
let modules : (Ident.t * modval) list ref = ref []

(* The functors of the file: the parameters in order, and the body. *)
let functors : (Ident.t * (Ident.t option list * modval)) list ref = ref []

(* What the bodies use of a parameter: the parameter, the names under it,
   and whether the thing is a value or a type. *)
let param_uses : (Ident.t * string list * [`Value | `Type]) list ref = ref []

(* The applications of a functor of the file: the functor and what it is
   given. *)
let applications : (Ident.t * modval list) list ref = ref []

(* What a functor of the file uses of a module that could not be
   followed: file, functor, what. *)
let not_followed : (string * string * string) list ref = ref []

let find_ident id l =
  match List.find_opt (fun (id', _) -> Ident.same id id') l with
  | Some (_, x) -> Some x
  | None -> None

(* [v] where each parameter of [sigma] is the module given for it. *)
let rec subst sigma (v : modval) =
  match v with
  | Under (p, names) -> (
    match find_ident p sigma with Some a -> project a names | None -> v)
  | Struct l -> Struct (List.map (fun (n, v) -> n, subst sigma v) l)
  | Applied (f, args) -> Applied (f, List.map (subst sigma) args)
  | Path _ | Own | Unknown -> v

(* The module of these names under [v]. *)
and project (v : modval) (names : string list) =
  match names with
  | [] -> v
  | n :: rest -> (
    match v with
    | Path (env, p) -> project (Path (env, Path.Pdot (p, n))) rest
    | Under (p, ns) -> Under (p, ns @ names)
    | Struct l -> (
      match List.assoc_opt n l with Some v -> project v rest | None -> Own)
    | Applied (f, args) -> (
      match apply f args with Some v -> project v names | None -> Unknown)
    | Own -> Own
    | Unknown -> Unknown)

and apply f args =
  match find_ident f !functors with
  | Some (ps, body) when List.length ps = List.length args ->
    let sigma =
      List.concat
        (List.map2 (fun p a -> match p with Some p -> [p, a] | None -> []) ps args)
    in
    Some (subst sigma body)
  | _ -> None

let rec modval_of_path env (p : Path.t) =
  match p with
  | Pident id -> (
    if List.exists (Ident.same id) !params
    then Under (id, [])
    else match find_ident id !modules with Some v -> v | None -> Path (env, p))
  | Pdot (q, s) -> project (modval_of_path env q) [s]
  | Papply _ | Pextra_ty _ -> Unknown

let rec functor_of (me : module_expr) =
  match (strip me).mod_desc with
  | Tmod_functor (param, body) ->
    let p = match param with Named (id, _, _) -> id | Unit -> None in
    let ps, body = functor_of body in
    p :: ps, body
  | _ -> [], me

let rec modval_of (me : module_expr) : modval =
  let me = strip me in
  match me.mod_desc with
  | Tmod_ident (p, _) -> modval_of_path me.mod_env p
  | Tmod_structure str ->
    Struct
      (List.filter_map
         (fun (item : structure_item) ->
           match item.str_desc with
           | Tstr_module { mb_id = Some id; mb_expr; _ } -> (
             module_defined id mb_expr;
             match find_ident id !modules with
             | Some v -> Some (Ident.name id, v)
             | None -> None)
           | _ -> None)
         str.str_items)
  | Tmod_apply _ -> (
    match spine me [] with Some (f, args) -> Applied (f, args) | None -> Unknown)
  | _ -> Unknown

(* The functor of the file that is applied, and what it is given. *)
and spine (me : module_expr) args =
  match (strip me).mod_desc with
  | Tmod_apply (f, arg, _) -> spine f (modval_of arg :: args)
  | Tmod_ident (Pident id, _) when Option.is_some (find_ident id !functors) -> Some (id, args)
  | _ -> None

(* A module of the file is defined. *)
and module_defined id (me : module_expr) =
  if Option.is_none (find_ident id !modules) && Option.is_none (find_ident id !functors)
  then
    match functor_of me with
    | [], _ -> modules := (id, modval_of me) :: !modules
    | ps, body ->
      List.iter
        (function
          | Some p -> if not (List.exists (Ident.same p) !params) then params := p :: !params
          | None -> ())
        ps;
      functors := (id, (ps, modval_of body)) :: !functors

let add_param_use param names kind =
  if not
       (List.exists
          (fun (p, n, k) -> Ident.same p param && n = names && k = kind)
          !param_uses)
  then param_uses := (param, names, kind) :: !param_uses

(* A value or a type whose module has no global name as it is written. *)
let indirect_use use kind env (p : Path.t) =
  match p with
  | Pdot (m, x) -> (
    match modval_of_path env m with
    | Under (param, names) -> add_param_use param (names @ [x]) kind
    | Path (env', q) when not (Path.same q m) -> (
      match comps_of_path (source_path (env_of env') (Path.Pdot (q, x))) with
      | Some comps -> use kind comps
      | None -> ())
    | _ -> ())
  | _ -> ()

(* At the end of a file: what each application makes the file use. An
   application inside another functor may give a module under that
   functor's parameter: that is a use of the parameter, so this is done
   until nothing is new. *)
let uses_of_applications use =
  let split names =
    match List.rev names with
    | last :: rest -> List.rev rest, last
    | [] -> [], ""
  in
  let rec round () =
    let before = List.length !param_uses in
    List.iter
      (fun (f, args) ->
        match find_ident f !functors with
        | Some (ps, _) when List.length ps = List.length args ->
          List.iter2
            (fun p arg ->
              match p with
              | None -> ()
              | Some param ->
                List.iter
                  (fun (id, names, kind) ->
                    if Ident.same id param
                    then
                      let mods, last = split names in
                      match project arg mods with
                      | Path (env, q) -> (
                        match
                          comps_of_path (source_path (env_of env) (Path.Pdot (q, last)))
                        with
                        | Some comps -> use kind comps
                        | None -> ())
                      | Under (param', names') ->
                        add_param_use param' (names' @ [last]) kind
                      | Unknown ->
                        if kind = `Value
                        then
                          not_followed
                            := ( !cur_file,
                                 Ident.name f,
                                 String.concat "." (Ident.name param :: names) )
                               :: !not_followed
                      | Struct _ | Applied _ | Own -> ())
                  !param_uses)
            ps args
        | _ -> ())
      !applications;
    if List.length !param_uses > before then round ()
  in
  round ()

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
    | Tmod_functor (param, _) ->
      (match param with
      | Named (Some id, _, _) ->
        if not (List.exists (Ident.same id) !params) then params := id :: !params
      | Named (None, _, _) | Unit -> ());
      incr functor_depth;
      super.module_expr sub me;
      decr functor_depth
    | Tmod_apply _ ->
      (match spine me [] with
      | Some app -> applications := app :: !applications
      | None -> ());
      super.module_expr sub me
    | _ -> super.module_expr sub me
  in
  let structure_item sub (si : structure_item) =
    match si.str_desc with
    | Tstr_module ({ mb_id = Some id; _ } as mb) ->
      let name = Ident.name id in
      let me = strip mb.mb_expr in
      module_defined id mb.mb_expr;
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
  let use kind comps =
    match kind with
    | `Value -> use_value comps
    | `Type -> ignore (type_use comps)
  in
  let expr sub (e : expression) =
    (match e.exp_desc with
    | Texp_ident (p, _, _) -> (
      let p = source_path (env_of e.exp_env) p in
      match comps_of_path p with
      | Some comps -> use_value comps
      | None -> indirect_use use `Value e.exp_env p)
    | Texp_letmodule (Some id, _, _, me, _) -> module_defined id me
    | Texp_construct (_, cd, _) -> constructor e.exp_env cd `Built
    | Texp_record { fields; _ } ->
      Array.iter (fun (l, _) -> field e.exp_env l `Read) fields
    | Texp_field (_, _, l) -> field e.exp_env l `Read
    | Texp_setfield (_, _, l, _) -> field e.exp_env l `Written
    | Texp_letop { let_; ands; _ } ->
      List.iter
        (fun (b : binding_op) ->
          let p = source_path (env_of e.exp_env) b.bop_op_path in
          match comps_of_path p with
          | Some comps -> use_value comps
          | None -> indirect_use use `Value e.exp_env p)
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
      let p = source_path (env_of ct.ctyp_env) p in
      match comps_of_path p with
      | Some comps -> ignore (type_use comps)
      | None -> indirect_use use `Type ct.ctyp_env p)
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
  params := [];
  modules := [];
  functors := [];
  param_uses := [];
  applications := [];
  (match cmt.cmt_annots with
  | Implementation str -> iterator.structure iterator str
  | _ -> warn "not an implementation: %s" file);
  uses_of_applications (fun kind comps ->
      match kind with
      | `Value -> use_value comps
      | `Type -> ignore (type_use comps));
  if !roots <> [] then Hashtbl.replace Sigs.locals !pseudo (List.rev !roots, !cur_file);
  local_idents := [];
  cmt
