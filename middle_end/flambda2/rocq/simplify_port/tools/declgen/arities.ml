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

(* The number of parameters that the DEFINITION of a declared value takes before
   it does anything else, read from the typed tree of the implementation: the
   rows of ARITIES.tsv. This file follows no file of the compiler.

   What it reads: the typed trees ([.cmt]) of the build; and the bytes of the
   source files, of the tree and of the build's copies, only to compare them
   with the digest that each typed tree has of its source ([tree_source]). It
   writes none of the text of a source: a row has names and numbers from the
   typed tree, and the place.

   Why: the port gives a declared function its first arguments only ([papp1 f
   a]), which in OCaml runs nothing of [f] as long as [f] is written with more
   parameters than it is given. The interface cannot say so ([val f : a -> b ->
   c] may be [let f a = work (); fun b -> ...]); the definition can.

   The count ([parameters], below, has the reason). OCaml takes the parameters
   that one function literal writes together as one group, and the cases of a
   [function] after them are one more of the group. For [let f = E]: if [E] is
   [fun p1 .. pn -> B], [n]; one more if [B] is the cases of a [function]; and,
   if [B] is itself a function literal (a second group), the count of [B], but
   only when each of [p1 .. pn] is inert: a variable or [_], and no default.
   Anything else is 0 (another name, an application, a [let] before the [fun]):
   that is 0 by this rule of what is written, and does not say that the value is
   no function. For [external f : .. = "p"]: the number of arguments of the
   primitive.

   The definition is found by the names: the unit, then each module, then the
   value, with the last binding of a name in a structure. A module that is
   another module is followed; an [include] is followed into the module that it
   includes; the application of a functor is followed into the body of the
   functor, where the parameter stands for the argument. What cannot be followed
   is said in the row. *)

open Common

type ctx =
  { unit_name : string;
    mutable env : (Ident.t * modval Lazy.t) list
  }

(* What a module expression is, as far as it can be followed. *)
and modval =
  | Struct of ctx * Typedtree.structure_item list
  | Functor of ctx * Ident.t option * Typedtree.module_expr
  | Unknown of string

type found =
  | Expr of ctx * Typedtree.expression * Location.t
  | Prim of ctx * int * Location.t
  | Not_read of string

let stdlib_reason =
  "not read: the standard library of the tree is compiled by the tree's own \
   compiler"

(* The file of the tree that a typed tree was made from, when the text that the
   build read is the text of the tree ([Src.standing]; [file] is the file of the
   typed tree). A list of the modules of a library, which the build writes and
   [Src.list_of_modules] knows, has no file in the tree: it is accepted, and has
   no definition of a value. Any other typed tree of the build is refused:
   [Src.standing] keeps the reason, and the generator writes nothing. *)
let tree_source ~file (cmt : Cmt_format.cmt_infos) =
  match Src.standing ~file cmt with
  | Follows rel -> Ok rel
  | List_of_modules s -> Ok s
  | Refused why -> Error ("not read: " ^ why)

(* Whether a unit is of the build that is read: its compiled interface is a file
   of the build root (or is on no directory of the load path). The others are of
   the library of the OCaml that made the build. *)
let unit_of_the_build u =
  match Load_path.find_normalized (u ^ ".cmi") with
  | exception Not_found -> true
  | cmi -> Src.of_the_build cmi

(* A BUILD THAT LACKS THE TYPED TREE OF AN IMPLEMENTATION THAT IS READ HERE IS
   REFUSED: the reason is kept in [stale], and the generator writes nothing. So
   a build of a part of the compiler, which has the compiled interfaces of the
   units that Simplify uses and not the typed trees of their implementations,
   does not give a table in which every row of those units says "not read". A
   unit is read here only for a row: the definition of a declared value is
   looked for in it, or through it (a module that is another module). *)
let no_implementation u why =
  if unit_of_the_build u
  then
    stale
      := Printf.sprintf
           "%s: %s: it is read for a row of ARITIES.tsv (a declared value is \
            defined in that unit, or through it)"
           u why
         :: !stale

(* For each unit: its structure, or why it was not read; and its file. *)
let units : (string, modval) Hashtbl.t = Hashtbl.create 97

let unit_file : (string, string) Hashtbl.t = Hashtbl.create 97

let has_module (sg : Types.signature) name =
  List.find_map
    (fun (item : Types.signature_item) ->
      match item with
      | Sig_module (id, _, _, _, _) when String.equal (Ident.name id) name ->
        Some id
      | _ -> None)
    sg

let has_value (sg : Types.signature) name =
  List.exists
    (fun (item : Types.signature_item) ->
      match item with
      | Sig_value (id, _, _) -> String.equal (Ident.name id) name
      | _ -> false)
    sg

let binds_module (mb : Typedtree.module_binding) name =
  match mb.mb_id with
  | Some id when String.equal (Ident.name id) name -> Some id
  | _ -> None

let force (m : modval Lazy.t) =
  try Lazy.force m
  with Lazy.Undefined -> Unknown "not read: a module that is made of itself"

let rec eval ctx (me : Typedtree.module_expr) : modval =
  match me.mod_desc with
  | Tmod_structure str -> eval_structure ctx str
  | Tmod_ident (p, _) -> eval_path ctx p
  | Tmod_functor (param, body) ->
    let id = match param with Unit -> None | Named (id, _, _) -> id in
    Functor (ctx, id, body)
  | Tmod_apply (f, arg, _) -> (
    match eval ctx f with
    | Functor (fctx, id, body) ->
      let env =
        match id with
        | Some id -> (id, lazy (eval ctx arg)) :: fctx.env
        | None -> fctx.env
      in
      eval { fctx with env } body
    | Unknown _ as m -> m
    | Struct _ -> Unknown "not read: an application of what is no functor")
  | Tmod_apply_unit f -> (
    match eval ctx f with
    | Functor (fctx, _, body) -> eval fctx body
    | Unknown _ as m -> m
    | Struct _ -> Unknown "not read: an application of what is no functor")
  | Tmod_constraint (me, _, _, _) -> eval ctx me
  | Tmod_unpack _ -> Unknown "not read: a module that is made from a value"

(* The modules of a structure stand in its environment under their identifiers:
   those that it binds, and those that an [include] or an [open] of a module
   expression brings. *)
and eval_structure ctx (str : Typedtree.structure) : modval =
  let ctx' = { ctx with env = ctx.env } in
  let binding (mb : Typedtree.module_binding) =
    match mb.mb_id with
    | Some id -> [id, lazy (eval ctx' mb.mb_expr)]
    | None -> []
  in
  let of_signature (sg : Types.signature) (me : Typedtree.module_expr) =
    let m = lazy (eval ctx' me) in
    List.filter_map
      (fun (item : Types.signature_item) ->
        match item with
        | Sig_module (id, _, _, _, _) ->
          Some (id, lazy (lookup_module (force m) (Ident.name id)))
        | _ -> None)
      sg
  in
  let bindings =
    List.concat_map
      (fun (item : Typedtree.structure_item) ->
        match item.str_desc with
        | Tstr_module mb -> binding mb
        | Tstr_recmodule mbs -> List.concat_map binding mbs
        | Tstr_include incl -> of_signature incl.incl_type incl.incl_mod
        | Tstr_open od -> of_signature od.open_bound_items od.open_expr
        | _ -> [])
      str.str_items
  in
  ctx'.env <- bindings @ ctx.env;
  Struct (ctx', str.str_items)

and eval_path ctx (p : Path.t) : modval =
  match p with
  | Pident id -> (
    if Ident.persistent id
    then read_unit (Ident.name id)
    else
      match List.find_opt (fun (i, _) -> Ident.same i id) ctx.env with
      | Some (_, m) -> force m
      | None ->
        Unknown
          (Printf.sprintf "not read: the module %s could not be followed"
             (Ident.name id)))
  | Pdot (p, s) -> lookup_module (eval_path ctx p) s
  | Papply _ | Pextra_ty _ -> Unknown "not read: a path that is no module"

(* The module [name] of a module: the last one of that name. *)
and lookup_module (m : modval) (name : string) : modval =
  match m with
  | Unknown _ -> m
  | Functor _ ->
    Unknown "not read: a module inside a functor that is not applied"
  | Struct (ctx, items) ->
    let rec go (items : Typedtree.structure_item list) =
      match items with
      | [] ->
        Unknown (Printf.sprintf "not read: no module %s in the structure" name)
      | item :: rest -> (
        let id =
          match item.str_desc with
          | Tstr_module mb -> binds_module mb name
          | Tstr_recmodule mbs ->
            List.find_map (fun mb -> binds_module mb name) mbs
          | Tstr_include incl -> has_module incl.incl_type name
          | _ -> None
        in
        match id with Some id -> eval_path ctx (Pident id) | None -> go rest)
    in
    go (List.rev items)

and read_unit u : modval =
  match Hashtbl.find_opt units u with
  | Some m -> m
  | None ->
    let m =
      if is_stdlib_unit u
      then Unknown stdlib_reason
      else
        match Load_path.find_normalized (u ^ ".cmt") with
        | exception Not_found ->
          no_implementation u
            "the build has no typed tree of its implementation (no file .cmt \
             of that name is on the load path)";
          Unknown
            (Printf.sprintf "not read: no typed tree of an implementation of %s"
               (short_unit u))
        | f -> (
          match Cmt_format.read_cmt f with
          | exception _ ->
            (* a typed tree that the build has and that cannot be read is
               refused *)
            if Src.of_the_build f
            then
              stale
                := Printf.sprintf "the typed tree %s could not be read" f
                   :: !stale;
            Unknown
              (Printf.sprintf "not read: the typed tree of %s could not be read"
                 (short_unit u))
          | cmt -> (
            match cmt.cmt_annots with
            | Implementation str -> (
              match tree_source ~file:f cmt with
              | Ok file ->
                Hashtbl.replace unit_file u file;
                eval_structure { unit_name = u; env = [] } str
              | Error why -> Unknown why)
            | _ ->
              no_implementation u
                (Printf.sprintf
                   "the typed tree %s is not that of a whole implementation" f);
              Unknown
                (Printf.sprintf
                   "not read: no typed tree of an implementation of %s"
                   (short_unit u))))
    in
    Hashtbl.replace units u m;
    m

(* The definition of the value [name] of a module: the last one. *)
let rec lookup_value (m : modval) (name : string) : found =
  match m with
  | Unknown why -> Not_read why
  | Functor _ ->
    Not_read "not read: a value inside a functor that is not applied"
  | Struct (ctx, items) ->
    let binds (vb : Typedtree.value_binding) =
      List.exists
        (fun id -> String.equal (Ident.name id) name)
        (Typedtree.pat_bound_idents vb.vb_pat)
    in
    let rec go (items : Typedtree.structure_item list) =
      match items with
      | [] ->
        Not_read (Printf.sprintf "not read: no definition of %s was found" name)
      | item :: rest -> (
        match item.str_desc with
        | Tstr_value (_, vbs) when List.exists binds vbs -> (
          let vb = List.find binds (List.rev vbs) in
          match vb.vb_pat.pat_desc with
          | Tpat_var _ -> Expr (ctx, vb.vb_expr, vb.vb_loc)
          (* [let (f : t) = e]: the typed tree has [_ as f] *)
          | Tpat_alias ({ pat_desc = Tpat_any; _ }, _, _, _, _) ->
            Expr (ctx, vb.vb_expr, vb.vb_loc)
          | _ ->
            Not_read
              (Printf.sprintf
                 "not read: %s is bound by a pattern that is not its name alone"
                 name))
        | Tstr_primitive vd when String.equal (Ident.name vd.val_id) name -> (
          match vd.val_val.val_kind with
          | Val_prim p -> Prim (ctx, p.prim_arity, vd.val_loc)
          | _ -> Not_read "not read: an [external] that is no primitive")
        | Tstr_include incl when has_value incl.incl_type name ->
          lookup_value (eval ctx incl.incl_mod) name
        | _ -> go rest)
    in
    go (List.rev items)

(* A parameter whose taking in runs nothing: a variable or [_], with or without
   a type ([(x : t)] is [_ as x] in the typed tree) or a label. A pattern that
   is matched ([lazy x], [Some x], a record, a tuple, [()]) and an optional
   parameter with a default are not. *)
let rec inert_pattern (p : Typedtree.pattern) =
  match p.pat_desc with
  | Tpat_any | Tpat_var _ -> true
  | Tpat_alias (p, _, _, _, _) -> inert_pattern p
  | _ -> false

let inert (param : Typedtree.function_param) =
  match param.fp_kind with
  | Tparam_pat p -> inert_pattern p
  | Tparam_optional_default _ -> false

(* The parameters that a function literal takes before it runs anything.

   OCaml takes the parameters of ONE function literal together ([Texp_function]
   has the arity of what is written): [fun (lazy x) y -> ..] forces nothing
   until it has both, and the cases of a [function] after the parameters are one
   more of them. A function literal that is the whole body of another is a
   second group: when the first group is full, OCaml matches its patterns and
   computes its defaults, and then gives the inner function. So [fun (lazy x) ->
   fun y -> ..] forces its argument when it has one, and [fun (Some x) -> fun y
   -> ..] can fail then. The count goes on into such a body only if every
   parameter so far is inert. *)
let rec parameters (e : Typedtree.expression) : int =
  match e.exp_desc with
  | Texp_function (params, body) -> (
    List.length params
    +
    match body with
    | Tfunction_cases _ -> 1
    | Tfunction_body e' ->
      if List.for_all inert params then parameters e' else 0)
  | _ -> 0

(* For a test of the count ([declgen --parameters FILE.cmt]): each value that
   the implementation binds at its top by a name alone, and its number. *)
let print_parameters cmt_file =
  match (Cmt_format.read_cmt cmt_file).cmt_annots with
  | Implementation str ->
    List.iter
      (fun (item : Typedtree.structure_item) ->
        match item.str_desc with
        | Tstr_value (_, vbs) ->
          List.iter
            (fun (vb : Typedtree.value_binding) ->
              match vb.vb_pat.pat_desc with
              | Tpat_var (id, _, _)
              | Tpat_alias ({ pat_desc = Tpat_any; _ }, id, _, _, _) ->
                Printf.printf "%s\t%d\n" (Ident.name id) (parameters vb.vb_expr)
              | _ -> ())
            vbs
        | _ -> ())
      str.str_items
  | _ ->
    prerr_endline
      "declgen --parameters: not the typed tree of an implementation";
    exit 2

let what (e : Typedtree.expression) =
  match e.exp_desc with
  | Texp_ident (p, _, _) -> Printf.sprintf "another name (%s)" (Path.name p)
  | Texp_apply _ -> "an application"
  | Texp_let _ -> "a [let]"
  | Texp_constant _ -> "a constant"
  | Texp_construct _ | Texp_variant _ | Texp_tuple _ | Texp_record _
  | Texp_array _ ->
    "a value that is built"
  | Texp_match _ | Texp_ifthenelse _ | Texp_try _ -> "a choice"
  | Texp_lazy _ -> "a lazy value"
  | _ -> "another expression"

(* A thing that a file of Simplify makes for itself with a functor of outside
   ([Sigs.local_root]): found in the file by its identifier. *)
let local_root unit_name (r : Sigs.local_root) :
    [`Module of modval | `Value of found] =
  let rec search (m : modval) =
    match m with
    | Struct (ctx, items) when String.equal ctx.unit_name unit_name ->
      List.find_map
        (fun (item : Typedtree.structure_item) ->
          let in_module (mb : Typedtree.module_binding) =
            match mb.mb_id with
            | Some id when Ident.same id r.l_id ->
              Some (`Module (eval_path ctx (Pident id)))
            | Some id -> search (eval_path ctx (Pident id))
            | None -> None
          in
          match item.str_desc with
          | Tstr_module mb -> in_module mb
          | Tstr_recmodule mbs -> List.find_map in_module mbs
          | Tstr_include incl ->
            List.find_map
              (fun (si : Types.signature_item) ->
                match si with
                | Sig_module (id, _, _, _, _) when Ident.same id r.l_id ->
                  Some (`Module (eval_path ctx (Pident id)))
                | Sig_value (id, _, _) when Ident.same id r.l_id ->
                  Some
                    (`Value
                       (lookup_value (eval ctx incl.incl_mod) (Ident.name id)))
                | _ -> None)
              incl.incl_type
          | _ -> None)
        items
    | _ -> None
  in
  match search (read_unit unit_name) with
  | Some x -> x
  | None -> (
    match read_unit unit_name with
    | Unknown why -> `Value (Not_read why)
    | _ -> `Value (Not_read "not read: the module was not found in the file"))

(* The definition of the declared value of this name (the unit, the modules, the
   value). *)
let find (comps : string list) : found =
  let rec follow (m : modval) (rest : string list) : found =
    match rest with
    | [] -> Not_read "not read: a name without a value"
    | [name] -> lookup_value m name
    | s :: rest -> follow (lookup_module m s) rest
  in
  match comps with
  | [] -> Not_read "not read: a name without a value"
  | u :: rest -> (
    match Sigs.root_of comps with
    | Some r -> (
      let k = String.length u - String.length "__local" in
      let unit_name = String.sub u 0 k in
      let rec drop n l = if n = 0 then l else drop (n - 1) (List.tl l) in
      let rest = drop (List.length r.l_comps) comps in
      match local_root unit_name r, rest with
      | `Module m, _ :: _ -> follow m rest
      | `Value f, [] -> f
      | `Value (Not_read why), _ -> Not_read why
      | _ -> Not_read "not read: the name was not found in the file")
    | None ->
      if is_local_unit u
      then Not_read "not read: the name was not found in the file"
      else follow (read_unit u) rest)

let place ctx (loc : Location.t) =
  let file =
    match Hashtbl.find_opt unit_file ctx.unit_name with
    | Some f -> f
    | None -> loc.loc_start.pos_fname
  in
  Printf.sprintf "%s:%d" file loc.loc_start.pos_lnum

(* The last two columns of the row of a declared value: the number of parameters
   of its definition ([-] when no definition was read), and the place of the
   definition or the reason. *)
let row (comps : string list) : string * string =
  let found =
    try find comps
    with Not_found | Failure _ ->
      Not_read "not read: the name could not be followed"
  in
  match found with
  | Not_read why -> "-", why
  | Prim (ctx, n, loc) -> string_of_int n, place ctx loc ^ ": an [external]"
  | Expr (ctx, e, loc) ->
    let n = parameters e in
    ( string_of_int n,
      if n > 0
      then place ctx loc
      else
        Printf.sprintf "%s: no function is written: %s" (place ctx loc) (what e)
    )
