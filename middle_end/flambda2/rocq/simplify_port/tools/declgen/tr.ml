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

(* From a type of OCaml to a type of Rocq, in the form of the port's guide:
   every arrow's result is in the monad. This file follows no file of the
   compiler. *)

open Common
module SS = Set.Make (String)

exception Unsupported of string

type tref =
  | Kit of string  (** a type of the kit or of Rocq, written as it is *)
  | Global of string list  (** a declared type: unit, modules, name *)

type ty =
  | Var of string
  | Arrow of ty list * ty  (** all the arguments, then the result *)
  | Tuple of ty list
  | Constr of tref * ty list

(* ---- what the translation finds on its way ---- *)

(* Types that the declarations mention: they must be declared too. *)
let needed_types : (string, string list) Hashtbl.t = Hashtbl.create 997

(* Set when a pass finds something that an earlier pass did not know. *)
let changed = ref false

let need_type comps =
  if not (Hashtbl.mem needed_types (key comps))
  then (
    Hashtbl.replace needed_types (key comps) comps;
    changed := true)

(* Parameters of abstract types that are given a polymorphic variant
   somewhere: an index that Rocq does not need. They are dropped. *)
let dropped : (string, int list) Hashtbl.t = Hashtbl.create 17

let is_dropped k i =
  match Hashtbl.find_opt dropped k with Some l -> List.mem i l | None -> false

let add_drop k i =
  if not (is_dropped k i)
  then (
    Hashtbl.replace dropped k
      (i :: Option.value ~default:[] (Hashtbl.find_opt dropped k));
    changed := true)

(* ---- type variables, for one declaration at a time ---- *)

let vars : (int * string) list ref = ref []

let reset_vars () = vars := []

let var_name (ty : Types.type_expr) =
  let id = Types.get_id ty in
  match List.assoc_opt id !vars with
  | Some s -> s
  | None ->
    let given =
      match Types.get_desc ty with
      | Tvar (Some s) | Tunivar (Some s) -> String.capitalize_ascii s
      | _ -> "A"
    in
    let taken s = List.exists (fun (_, s') -> s = s') !vars in
    let rec fresh i =
      let s = if i = 0 then given else Printf.sprintf "%s%d" given i in
      if taken s then fresh (i + 1) else s
    in
    let s = fresh 0 in
    vars := (id, s) :: !vars;
    s

let var_names () = List.rev_map snd !vars

(* ---- the translation ---- *)

let predef_kit = ["int"; "bool"; "unit"; "string"; "list"; "option"; "exn"]

let format_arity comps =
  match comps with
  | ["Stdlib"; "format"] | ["CamlinternalFormatBasics"; "format"] -> Some 3
  | ["Stdlib"; "format4"] | ["CamlinternalFormatBasics"; "format4"] -> Some 4
  | ["Stdlib"; "format6"] | ["CamlinternalFormatBasics"; "format6"] -> Some 6
  | _ -> None

let is_abstract comps =
  match Env.find_type (Sigs.path_of_comps comps) !Sigs.base_env with
  | { type_kind = Type_abstract _; type_manifest = None; _ } -> true
  | _ -> false
  | exception Not_found -> false

(* While the items of a module that is an alias of another are written
   under the alias: the other module, then the alias. A type of the other
   module is then written as the type of the same name under the alias. *)
let rewrite : (string list * string list) option ref = ref None

let rewritten comps =
  match !rewrite with
  | None -> comps
  | Some (target, alias) ->
    let rec strip prefix l =
      match prefix, l with
      | [], rest -> Some rest
      | p :: prefix, x :: l when p = x -> strip prefix l
      | _ -> None
    in
    (match strip target comps with
     | Some [name] -> alias @ [name]
     | _ -> comps)

let resolve (p : Path.t) : tref =
  let p = source_path !Sigs.base_env p in
  match p with
  | Pident id when Ident.is_predef id ->
    let s = Ident.name id in
    if List.mem s predef_kit
    then Kit s
    else if s = "lazy_t"
    then Kit "lazy_t"
    else Global ["Stdlib"; s]
  | _ -> (
    match comps_of_path p with
    | Some ["Stdlib"; "ref"] -> Kit "ref"
    | Some (["Stdlib__Lazy"; "t"] | ["CamlinternalLazy"; "t"]) -> Kit "lazy_t"
    | Some comps -> (
      match format_arity comps with
      | Some _ -> raise (Unsupported "a format outside the arguments of a function")
      | None -> Global (rewritten comps))
    | None -> raise (Unsupported ("the type " ^ Path.name p ^ " is not a global name")))

let rec chain (ty : Types.type_expr) acc =
  match Types.get_desc ty with
  | Tarrow (l, a, b, _) -> chain b ((l, a) :: acc)
  | _ -> List.rev acc, ty

let format_of (ty : Types.type_expr) =
  match Types.get_desc ty with
  | Tconstr (p, args, _) -> (
    match comps_of_path (source_path !Sigs.base_env p) with
    | Some comps -> (
      match format_arity comps with
      | Some n when List.length args = n -> Some (List.nth args (n - 1))
      | _ -> None)
    | None -> None)
  | _ -> None

let rec tr (ty : Types.type_expr) : ty =
  match Types.get_desc ty with
  | Tvar _ | Tunivar _ -> Var (var_name ty)
  | Tarrow _ ->
    let t, _, _ = tr_arrow ty in
    t
  | Ttuple l -> Tuple (List.map (fun (_, t) -> tr t) l)
  | Tconstr (p, args, _) -> (
    match resolve p with
    | Kit s -> Constr (Kit s, List.map tr args)
    | Global comps ->
      let k = key comps in
      List.iteri
        (fun i a ->
          match Types.get_desc a with
          | Tvariant _ when is_abstract comps -> add_drop k i
          | _ -> ())
        args;
      need_type comps;
      let args = List.filteri (fun i _ -> not (is_dropped k i)) args in
      Constr (Global comps, List.map tr args))
  | Tpoly (t, []) -> tr t
  | Tpoly _ -> raise (Unsupported "a polymorphic field or method")
  | Tvariant _ -> raise (Unsupported "a polymorphic variant")
  | Tobject _ | Tfield _ | Tnil -> raise (Unsupported "an object type")
  | Tpackage _ -> raise (Unsupported "a first-class module")
  | Tlink _ | Tsubst _ -> raise (Unsupported "an inner node of a type")

(* A function type: the type of Rocq, the labels of the arguments, and
   whether the last argument is a format (it is then a [string], and the
   caller declares one function for each number of arguments that may
   follow the format). *)
and tr_arrow ty : ty * Asttypes.arg_label list * bool =
  let args, res = chain ty [] in
  let rec split before = function
    | [] -> None
    | (l, a) :: rest -> (
      match format_of a with
      | Some result -> Some (List.rev before, l, result, rest)
      | None -> split ((l, a) :: before) rest)
  in
  match split [] args with
  | None ->
    Arrow (List.map (fun (_, a) -> tr a) args, tr res), List.map fst args, false
  | Some (before, l, result, []) ->
    ( Arrow
        ( List.map (fun (_, a) -> tr a) before
          @ [Constr (Kit "string", [])],
          tr result ),
      List.map fst before @ [l],
      true )
  | Some _ -> raise (Unsupported "arguments after a format")
