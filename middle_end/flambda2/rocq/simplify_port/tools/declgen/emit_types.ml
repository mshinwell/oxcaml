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

(* Variants and records: what Simplify takes apart is an inductive type or
   a record of Rocq with the compiler's own names of constructors and
   fields; what Rocq cannot take so is abstract, with a maker for each
   constructor and one eliminator. This file follows no file of the
   compiler. *)

open Common
open Decl_out
module SS = Set.Make (String)

(* Types written as an inductive type or a record in an earlier pass: a
   type may hold itself inside one of them. *)
let mirrored : (string, unit) Hashtbl.t = Hashtbl.create 97

let mirror comps =
  if not (Hashtbl.mem mirrored (key comps))
  then (
    Hashtbl.replace mirrored (key comps) ();
    Tr.changed := true)

type ctor =
  { c_name : string;
    c_args : Tr.ty list;  (** by place *)
    c_fields : (string * bool) list option;  (** an inline record: fields, mutable? *)
    c_res : Tr.ty option  (** a GADT's result *)
  }

type shape =
  | Variant of ctor list
  | Record of (string * Tr.ty * bool) list

exception Refused of string

(* Does the type [self] occur in [ty] where Rocq would refuse it? *)
let rec mentions self (ty : Tr.ty) =
  match ty with
  | Var _ -> false
  | Constr (Global c, args) -> key c = self || List.exists (mentions self) args
  | Constr (Kit _, args) | Tuple args -> List.exists (mentions self) args
  | Arrow (args, res) | Arrow_pure (args, res) ->
    List.exists (mentions self) (res :: args)

let rec refused_place self (ty : Tr.ty) =
  match ty with
  | Var _ -> false
  | Constr (Global c, _) when key c = self -> false
  | Constr (Global c, args) ->
    if Hashtbl.mem mirrored (key c)
    then List.exists (refused_place self) args
    else List.exists (mentions self) args
  | Constr (Kit ("list" | "option"), args) | Tuple args ->
    List.exists (refused_place self) args
  | Constr (Kit _, args) -> List.exists (mentions self) args
  | Arrow (args, res) | Arrow_pure (args, res) ->
    List.exists (mentions self) args || refused_place self res

let shape_of (decl : Types.type_declaration) : shape option =
  let field (ld : Types.label_declaration) =
    Ident.name ld.ld_id, Tr.tr ld.ld_type, ld.ld_mutable = Asttypes.Mutable
  in
  match decl.type_kind with
  | Type_variant (cds, _) ->
    Some
      (Variant
         (List.map
            (fun (cd : Types.constructor_declaration) ->
              let c_args, c_fields =
                match cd.cd_args with
                | Cstr_tuple l -> List.map Tr.tr l, None
                | Cstr_record lds ->
                  let fs = List.map field lds in
                  ( List.map (fun (_, t, _) -> t) fs,
                    Some (List.map (fun (n, _, m) -> n, m) fs) )
              in
              { c_name = Ident.name cd.cd_id;
                c_args;
                c_fields;
                c_res = Option.map Tr.tr cd.cd_res
              })
            cds))
  | Type_record (lds, _) -> Some (Record (List.map field lds))
  | Type_abstract _ | Type_open -> None

(* Why Rocq cannot have the type under the compiler's names, whatever its
   neighbours are; [None] if it can. *)
let structural self (sh : shape) : string option =
  match sh with
  | Record fields ->
    if List.exists (fun (_, ty, _) -> mentions self ty) fields
    then Some "the record holds itself"
    else None
  | Variant ctors ->
    if List.exists (fun c -> c.c_res <> None) ctors
    then Some "it is a GADT"
    else if List.exists (fun c -> List.exists (refused_place self) c.c_args) ctors
    then Some "it holds itself inside an abstract type or to the left of an arrow"
    else None

let types_of (sh : shape) =
  match sh with
  | Record fields -> List.map (fun (_, t, _) -> t) fields
  | Variant ctors -> List.concat_map (fun c -> c.c_args) ctors

(* A name that a constructor or a field can take as it is. (A name that a
   value or a type took in this pass does not count: the value or the type
   gives way in the next.) *)
let free s = (not (List.mem s Sigs.reserved)) && not (SS.mem s !native)

let distinct l = List.length (List.sort_uniq compare l) = List.length l

let binders params =
  String.concat "" (List.map (fun p -> Printf.sprintf " (%s : Type)" p) params)

let applied rname params = String.concat " " (rname :: params)

let implicit name params =
  if params <> []
  then line "Arguments %s {%s}." name (String.concat " " params)

let xs n = List.init n (fun i -> Printf.sprintf "x__%d" (i + 1))

(* In OCaml: the constructor applied to the binders, as a term and as a
   pattern (they are the same text). *)
let ocaml_ctor modc c =
  let name = Print.ocaml_name (modc @ [c.c_name]) in
  let vars = xs (List.length c.c_args) in
  match c.c_fields, vars with
  | Some fs, _ ->
    Printf.sprintf "%s { %s }" name
      (String.concat "; " (List.map2 (fun (f, _) x -> f ^ " = " ^ x) fs vars))
  | None, [] -> name
  | None, [x] -> name ^ " " ^ x
  | None, _ -> Printf.sprintf "%s (%s)" name (String.concat ", " vars)

let ocaml_record modc fields =
  let vars = xs (List.length fields) in
  let qualify i f = if i = 0 then Print.ocaml_name (modc @ [f]) else f in
  Printf.sprintf "{ %s }"
    (String.concat "; "
       (List.mapi (fun i ((f, _, _), x) -> qualify i f ^ " = " ^ x) (List.combine fields vars)))

let rec vars_of acc (ty : Tr.ty) =
  match ty with
  | Var v -> if List.mem v acc then acc else acc @ [v]
  | Constr (_, args) | Tuple args -> List.fold_left vars_of acc args
  | Arrow (args, res) | Arrow_pure (args, res) ->
    List.fold_left vars_of acc (args @ [res])

let forall vars =
  if vars = []
  then ""
  else Printf.sprintf "forall {%s : Type}, " (String.concat " " vars)

let wanted comps =
  match Hashtbl.find_opt Uses.types (key comps) with
  | Some u ->
    not (SS.is_empty u.built && SS.is_empty u.matched && SS.is_empty u.fields)
  | None -> false

(* The payload records of the open module that are records of Rocq: what
   they hold (fields, types, parameters), and their names. A later inline
   record that holds the same uses the same record. *)
let payloads : (string * string) list ref = ref []

(* One variant of a definition: its payload records are written, its
   constructors named. Returns the rows of the inductive type, the names
   of the constructors, whether one was renamed, and whether a payload is
   abstract (the type then keeps its makers and its eliminator). [block]:
   the types that are defined together with it, itself included. *)
let prepare_variant ~params ~block ~renamed_module modc rname ctors place =
  let self_ty = applied rname params in
  (* in a module that has another name in Rocq (a word of Rocq), Rocq would
     print the constructors and the fields under that name: the constructors
     get their strings, the inline records are abstract *)
  let renamed = ref renamed_module and abstract_payload = ref false in
  let rows =
    List.map
      (fun c ->
        let args =
          match c.c_fields with
          | Some fs ->
            let held =
              String.concat "; "
                (List.map2 (fun (f, _) ty -> f ^ " : " ^ Print.pp ty) fs c.c_args)
            in
            let what = held ^ " | " ^ String.concat " " params in
            let in_block =
              List.exists (fun k -> List.exists (mentions k) c.c_args) block
            in
            let names = List.map fst fs in
            let pname =
              if (not renamed_module) && (not in_block)
                 && List.for_all free names && distinct names
              then (
                let pname = claim (String.uncapitalize_ascii c.c_name ^ "_payload_") in
                line "Record %s%s : Type := { %s }." pname (binders params) held;
                List.iter
                  (fun f ->
                    claim_native f;
                    add_index (Print.ocaml_name (modc @ [f])) f "field" 0 place)
                  names;
                implicit ("Build_" ^ pname) params;
                List.iter (fun f -> implicit f params) names;
                payloads := (what, pname) :: !payloads;
                pname)
              else
                match List.assoc_opt what !payloads with
                | Some pname when (not in_block) && not renamed_module -> pname
                | _ ->
                  let pname = claim (String.uncapitalize_ascii c.c_name ^ "_payload_") in
                  abstract_payload := true;
                  line
                    "(* The inline record of [%s]: abstract (a name of its fields is \
                     taken, or it holds the type); [mk_%s] makes one, [match_%s] \
                     reads it. *)"
                    c.c_name c.c_name rname;
                  line "Parameter %s : %s." pname
                    (String.concat " -> " (List.map (fun _ -> "Type") params @ ["Type"]));
                  pname
            in
            [(if params = [] then pname else "(" ^ applied pname params ^ ")")]
          | None -> List.map Print.pp_arg c.c_args
        in
        let cname =
          if free c.c_name
          then (
            claim_native c.c_name;
            c.c_name)
          else (
            renamed := true;
            claim (Sigs.sanitize c.c_name))
        in
        add_index (Print.ocaml_name (modc @ [c.c_name])) cname "constructor"
          (List.length c.c_args) place;
        cname, Printf.sprintf "| %s : %s" cname (String.concat " -> " (args @ [self_ty])))
      ctors
  in
  rows, !renamed, !abstract_payload

let emit_record ~params modc rname fields place =
  line "Record %s%s : Type := { %s }." rname (binders params)
    (String.concat "; "
       (List.map
          (fun (f, ty, _) ->
            claim_native f;
            add_index (Print.ocaml_name (modc @ [f])) f "field" 0 place;
            f ^ " : " ^ Print.pp ty)
          fields));
  implicit ("Build_" ^ rname) params;
  List.iter (fun (f, _, _) -> implicit f params) fields;
  List.iter
    (fun (f, ty, mut) ->
      if mut
      then (
        let sname = claim ("set_" ^ f) in
        line "Parameter %s : %s%s -> %s -> M unit." sname (forall params)
          (if params = [] then rname else "(" ^ applied rname params ^ ")")
          (Print.pp_arg ty);
        extract sname
          (Printf.sprintf "(fun x__1 x__2 -> x__1.%s <- x__2)"
             (Print.ocaml_name (modc @ [f])));
        add_index (Print.ocaml_name (modc @ [f]) ^ " <-") sname "field setter" 2 place))
    fields

(* The makers and the eliminator of a type that stays abstract. *)
let emit_makers ~params ~private_ modc name rname (sh : shape) place =
  let self_ty = Tr.Constr (Tr.Global (modc @ [name]), List.map (fun p -> Tr.Var p) params) in
  let res_var = if List.mem "Res" params then "Res_" else "Res" in
  let maker mname args result real =
    (* OCaml makes no value of a private type outside its module *)
    if not private_ then
    let mname = claim mname in
    let tys = args @ [result] in
    line "Parameter %s : %s%s." mname
      (forall (List.fold_left vars_of [] tys))
      (String.concat " -> " (List.map Print.pp_arg tys));
    extract mname real;
    add_index real mname "maker" (List.length args) place
  in
  let lam n body =
    if n = 0 then body else Printf.sprintf "(fun %s -> %s)" (String.concat " " (xs n)) body
  in
  let eliminator cases real =
    let ename = claim ("match_" ^ rname) in
    let branch args =
      let args = if args = [] then [Tr.Constr (Tr.Kit "unit", [])] else args in
      "(" ^ String.concat " -> " (List.map Print.pp_arg args) ^ " -> M " ^ res_var ^ ")"
    in
    line "Parameter %s : %s%s -> %s -> M %s." ename
      (forall (List.fold_left vars_of [] (self_ty :: List.concat cases) @ [res_var]))
      (Print.pp_arg self_ty)
      (String.concat " -> " (List.map branch cases))
      res_var;
    extract ename real;
    add_index ("match on " ^ Print.ocaml_name (modc @ [name])) ename "eliminator"
      (1 + List.length cases) place
  in
  match sh with
  | Variant ctors ->
    List.iter
      (fun c ->
        maker ("mk_" ^ c.c_name) c.c_args
          (Option.value ~default:self_ty c.c_res)
          (lam (List.length c.c_args) (ocaml_ctor modc c)))
      ctors;
    if List.for_all (fun c -> c.c_res = None) ctors
    then
      eliminator
        (List.map (fun c -> c.c_args) ctors)
        (Printf.sprintf "(fun x__0 %s -> match x__0 with %s)"
           (String.concat " " (List.mapi (fun i _ -> Printf.sprintf "f__%d" (i + 1)) ctors))
           (String.concat " | "
              (List.mapi
                 (fun i c ->
                   Printf.sprintf "%s -> f__%d %s" (ocaml_ctor modc c) (i + 1)
                     (if c.c_args = [] then "()" else String.concat " " (xs (List.length c.c_args))))
                 ctors)))
  | Record fields ->
    let tys = List.map (fun (_, t, _) -> t) fields in
    let n = List.length fields in
    maker ("mk_" ^ rname) tys self_ty (lam n (ocaml_record modc fields));
    eliminator [tys]
      (Printf.sprintf "(fun x__0 f__1 -> let %s = x__0 in f__1 %s)"
         (ocaml_record modc fields) (String.concat " " (xs n)))

