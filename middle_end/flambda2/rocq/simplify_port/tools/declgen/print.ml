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

(* The text of Rocq for a type and for a name, as seen from the file and
   the module that are being written. This file follows no file of the
   compiler. *)

open Common
module SS = Set.Make (String)

(* The compilation unit whose file is being written, and the module of it
   that is open (the unit, then the modules). *)
let cur_unit = ref ""

let cur_mod : string list ref = ref []

(* The other units that the file names: its [Require]. *)
let deps : SS.t ref = ref SS.empty

(* The names of all the modules inside the file: a unit of the same name
   is then written [decl.NAME]. *)
let file_modules : SS.t ref = ref SS.empty

let unit_ref u =
  let r = Sigs.unit_rocq u in
  if u = !cur_unit
  then r
  else (
    deps := SS.add u !deps;
    if SS.mem r !file_modules then "decl." ^ r else r)

let split_last l =
  match List.rev l with
  | last :: rest -> List.rev rest, last
  | [] -> invalid_arg "split_last"

(* The name that a type was given where it was declared, when it is not
   the one that the rules give (a second declaration of a name in a module
   gets one more underscore). Kept from one pass to the next. *)
let type_names : (string, string) Hashtbl.t = Hashtbl.create 97

let set_type_name comps rname =
  let modc, last = split_last comps in
  if rname <> Sigs.type_rocq modc last
     && Hashtbl.find_opt type_names (key comps) <> Some rname
  then (
    Hashtbl.replace type_names (key comps) rname;
    Tr.changed := true)

(* The names in Rocq of the modules [mods] of the unit [u], outermost
   first: one of them may be a module type. *)
let modules_rocq u mods =
  let rec go prefix = function
    | [] -> []
    | m :: rest ->
      let prefix = prefix @ [m] in
      let name =
        match Hashtbl.find_opt Sigs.modtype_rocq (key prefix) with
        | Some n -> n
        | None -> Sigs.module_rocq m
      in
      name :: go prefix rest
  in
  go [u] mods

(* The name in Rocq of a declared thing. *)
let global_name kind comps =
  let modc, last = split_last comps in
  let name =
    match kind with
    | `Type -> (
      match Hashtbl.find_opt type_names (key comps) with
      | Some n -> n
      | None -> Sigs.type_rocq modc last)
    | `Value -> Sigs.value_rocq last
    | `Field -> Sigs.field_rocq modc last
    | `Ctor -> Sigs.ctor_rocq last
  in
  if modc = !cur_mod
  then name
  else
    match modc with
    | u :: mods -> String.concat "." ((unit_ref u :: modules_rocq u mods) @ [name])
    | [] -> name

(* The name in OCaml: what the realisation says. An operator is in
   parentheses. *)
let ocaml_name comps =
  let comps =
    match List.rev comps with
    | last :: rest
      when (not (Sigs.is_identifier last))
           || List.mem last ["mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"; "or"] ->
      List.rev (("( " ^ last ^ " )") :: rest)
    | _ -> comps
  in
  match comps with
  | "%predef" :: rest -> String.concat "." rest
  | "Stdlib" :: rest -> String.concat "." rest
  | u :: _ when is_local_unit u -> (
    (* a module that a file makes for itself: its name there *)
    match Sigs.root_of comps with
    | Some r ->
      let rec drop n l = if n = 0 then l else drop (n - 1) (List.tl l) in
      String.concat "." (drop (List.length r.l_comps - 1) comps)
    | None -> String.concat "." (List.tl comps))
  | u :: rest -> String.concat "." (short_unit u :: rest)
  | [] -> ""

let rec pp (ty : Tr.ty) =
  match ty with
  | Var v -> v
  | Arrow (args, res) ->
    String.concat " -> " (List.map pp_arg args @ ["M " ^ pp_atom res])
  | Arrow_pure (args, res) -> String.concat " -> " (List.map pp_arg (args @ [res]))
  | Tuple [a; b] -> "(" ^ pp_arg a ^ " * " ^ pp_arg b ^ ")"
  | Tuple l when List.length l >= 3 && List.length l <= 6 ->
    Printf.sprintf "tuple%d %s" (List.length l)
      (String.concat " " (List.map pp_atom l))
  | Tuple _ -> raise (Tr.Unsupported "a tuple of more than six")
  | Constr (r, []) -> tref r
  | Constr (r, args) -> tref r ^ " " ^ String.concat " " (List.map pp_atom args)

and pp_arg ty =
  match ty with Arrow _ | Arrow_pure _ -> "(" ^ pp ty ^ ")" | _ -> pp ty

and pp_atom ty =
  match ty with
  | Var _ | Constr (_, []) | Tuple [_; _] -> pp ty
  | _ -> "(" ^ pp ty ^ ")"

and tref = function
  | Tr.Kit s -> s
  | Tr.Global comps -> global_name `Type comps

(* [forall {A B : Type}, ] for the type variables of a declaration. *)
let quantifier () =
  match Tr.var_names () with
  | [] -> ""
  | l -> Printf.sprintf "forall {%s : Type}, " (String.concat " " l)

(* A string of OCaml inside a string of Rocq. *)
let quote s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c -> if c = '"' then Buffer.add_string b "\"\"" else Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

(* The realisation of a function whose arguments have these labels. *)
let realisation ocaml (labels : Asttypes.arg_label list) =
  if List.for_all (fun l -> l = Asttypes.Nolabel) labels
  then ocaml
  else
    let binders = List.mapi (fun i _ -> Printf.sprintf "x__%d" (i + 1)) labels in
    let args =
      List.map2
        (fun (l : Asttypes.arg_label) x ->
          match l with
          | Nolabel -> x
          | Labelled s -> "~" ^ s ^ ":" ^ x
          | Optional s -> "?" ^ s ^ ":" ^ x)
        labels binders
    in
    Printf.sprintf "(fun %s -> %s %s)" (String.concat " " binders) ocaml
      (String.concat " " args)
