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

(* The generator of the declarations of the port of Simplify: what every
   part shares. This file follows no file of the compiler.

   The generator reads the compiled interfaces ([.cmi]) and typed trees
   ([.cmt]) of a build of the compiler with the compiler's own library of
   types and environments, so every name is resolved as the compiler
   resolves it. *)

(* The [_build/default] of the build that is read. *)
let build_root = ref ""

(* The root of the sources of the same commit (for headers and the text of
   declarations). *)
let source_root = ref ""

let fix_dir d =
  if d = ""
  then !build_root
  else if Filename.is_relative d
  then Filename.concat !build_root d
  else d

let init_load_path (cmt : Cmt_format.cmt_infos) =
  Load_path.init ~auto_include:Load_path.no_auto_include
    ~visible:(List.map fix_dir cmt.cmt_loadpath.visible)
    ~hidden:(List.map fix_dir cmt.cmt_loadpath.hidden)

(* An environment of a typed tree is kept as a summary; this makes it whole
   again. The last few are remembered: neighbours share environments. *)
let env_cache : (Env.t * Env.t) list ref = ref []

let env_of (e : Env.t) =
  match List.assq_opt e !env_cache with
  | Some e' -> e'
  | None ->
    let e' = try Envaux.env_of_only_summary e with _ -> e in
    env_cache
      := (e, e')
         :: (match !env_cache with a :: b :: c :: _ -> [a; b; c] | l -> l);
    e'

let norm_value env p =
  try Env.normalize_value_path None env p with _ -> p

let norm_module env p =
  try Env.normalize_module_path None env p with _ -> p

let norm_type env p = try Env.normalize_type_path None env p with _ -> p

let starts_with ~prefix s =
  String.length s >= String.length prefix
  && String.sub s 0 (String.length prefix) = prefix

let has_double_underscore u =
  let n = String.length u in
  let rec go i = i + 1 < n && ((u.[i] = '_' && u.[i + 1] = '_') || go (i + 1)) in
  go 0

let is_simplify_unit u = starts_with ~prefix:"Flambda2_simplify__" u

(* A library's list of its modules ([Flambda2_identifiers], whose
   [Variable] is [Flambda2_identifiers__Variable]; [Stdlib], whose [List]
   is [Stdlib__List]). *)
let is_library_unit u =
  u = "Stdlib" || (starts_with ~prefix:"Flambda2_" u && not (has_double_underscore u))

(* The name of a module as the compiler's sources write it: an alias is
   followed when it is local to a file of Simplify, or a member of a file of
   Simplify ([Simplify_import.DA]) or of a library's list of modules. An
   alias inside another interface is kept: [Code_id.Map] stays, though it
   is [Int_ids.Code_id.Map]. *)
let rec source_module env (p : Path.t) : Path.t =
  let alias_target p =
    match Env.find_module p env with
    | { md_type = Mty_alias target; _ } -> Some target
    | _ -> None
    | exception Not_found -> None
  in
  match p with
  | Pident id -> (
    if Ident.persistent id
    then p
    else match alias_target p with Some t -> source_module env t | None -> p)
  | Pdot (m, s) -> (
    let m' = source_module env m in
    let p' = Path.Pdot (m', s) in
    let follow =
      match Path.head m' with
      | id when Ident.persistent id -> (
        let u = Ident.name id in
        is_simplify_unit u
        || match m' with Pident _ -> is_library_unit u | _ -> false)
      | _ -> true
      | exception _ -> false
    in
    if not follow
    then p'
    else match alias_target p' with Some t -> source_module env t | None -> p')
  | Papply _ | Pextra_ty _ -> p

(* The same for a value or a type: its module is made so. *)
let source_path env (p : Path.t) : Path.t =
  match p with
  | Pdot (m, s) -> Pdot (source_module env m, s)
  | _ -> p

(* A global name as a list: the compilation unit, then the modules, then
   the name. [None] for what is local to a file or goes through the
   application of a functor. *)
let rec comps_of_path (p : Path.t) : string list option =
  match p with
  | Pident id -> if Ident.persistent id then Some [Ident.name id] else None
  | Pdot (p, s) -> (
    match comps_of_path p with Some l -> Some (l @ [s]) | None -> None)
  | Papply _ | Pextra_ty _ -> None

(* [Flambda2_identifiers__Variable] is [Variable]: the name that the
   compiler's sources write. [Stdlib__List] is [List]. *)
let short_unit u =
  let n = String.length u in
  let rec find i =
    if i + 1 >= n
    then None
    else if u.[i] = '_' && u.[i + 1] = '_'
    then Some i
    else find (i + 1)
  in
  match find 0 with
  | Some i when i > 0 && i + 2 < n -> String.sub u (i + 2) (n - i - 2)
  | _ -> u

let is_stdlib_unit u = u = "Stdlib" || starts_with ~prefix:"Stdlib__" u

let key comps = String.concat "." comps

let warnings : string list ref = ref []

let warn fmt = Printf.ksprintf (fun s -> warnings := s :: !warnings) fmt
