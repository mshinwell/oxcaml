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
  | Arrow (args, res) -> List.exists (mentions self) (res :: args)

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
  | Arrow (args, res) -> List.exists (mentions self) args || refused_place self res

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

(* Whether the type can be an inductive type or a record of Rocq under the
   compiler's names; raises [Refused] with the reason if not. Returns the
   names of constructors that must be renamed (a keyword, or taken). *)
let check ~forbidden self (sh : shape) =
  let all_types =
    match sh with
    | Record fields -> List.map (fun (_, t, _) -> t) fields
    | Variant ctors -> List.concat_map (fun c -> c.c_args) ctors
  in
  if List.exists (fun k -> List.exists (mentions k) all_types) forbidden
  then raise (Refused "it is recursive with a type that is declared after it");
  let free s = (not (List.mem s Sigs.reserved)) && not (SS.mem s !declared) in
  let seen = ref SS.empty in
  let fresh_field f =
    if (not (free f)) || SS.mem f !seen
    then raise (Refused ("the name of the field [" ^ f ^ "] is taken in Rocq"));
    seen := SS.add f !seen
  in
  match sh with
  | Record fields ->
    List.iter
      (fun (f, ty, _) ->
        fresh_field f;
        if refused_place self ty || mentions self ty
        then raise (Refused "the record holds itself"))
      fields;
    []
  | Variant ctors ->
    List.concat_map
      (fun c ->
        if c.c_res <> None then raise (Refused "it is a GADT");
        List.iter
          (fun ty ->
            if refused_place self ty
            then
              raise
                (Refused
                   "it holds itself inside an abstract type or to the left of \
                    an arrow"))
          c.c_args;
        (match c.c_fields with
        | Some fs ->
          List.iter (fun (f, _) -> fresh_field f) fs;
          if List.exists (mentions self) c.c_args
          then raise (Refused "an inline record of it holds the type itself")
        | None -> ());
        if free c.c_name && not (SS.mem c.c_name !seen)
        then (
          seen := SS.add c.c_name !seen;
          [])
        else [c.c_name])
      ctors

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
  | Arrow (args, res) -> List.fold_left vars_of acc (args @ [res])

let forall vars =
  if vars = []
  then ""
  else Printf.sprintf "forall {%s : Type}, " (String.concat " " vars)

let wanted comps =
  match Hashtbl.find_opt Uses.types (key comps) with
  | Some u ->
    not (SS.is_empty u.built && SS.is_empty u.matched && SS.is_empty u.fields)
  | None -> false

(* The type as an inductive type of Rocq. *)
let emit_variant ~params ~ocaml_type modc rname ctors renamed place =
  let self_ty = applied rname params in
  let rows =
    List.map
      (fun c ->
        let args =
          match c.c_fields with
          | Some fs ->
            let pname = claim (String.uncapitalize_ascii c.c_name ^ "_payload_") in
            line "Record %s%s : Type := { %s }." pname (binders params)
              (String.concat "; "
                 (List.map2
                    (fun (f, _) ty ->
                      declared := SS.add f !declared;
                      add_index (Print.ocaml_name (modc @ [f])) f "field" 0 place;
                      f ^ " : " ^ Print.pp ty)
                    fs c.c_args));
            implicit ("Build_" ^ pname) params;
            List.iter (fun (f, _) -> implicit f params) fs;
            [(if params = [] then pname else "(" ^ applied pname params ^ ")")]
          | None -> List.map Print.pp_arg c.c_args
        in
        let cname = claim (Sigs.sanitize c.c_name) in
        add_index (Print.ocaml_name (modc @ [c.c_name])) cname "constructor"
          (List.length c.c_args) place;
        cname, Printf.sprintf "| %s : %s" cname (String.concat " -> " (args @ [self_ty])))
      ctors
  in
  line "Inductive %s%s : Type :=" rname (binders params);
  let n = List.length rows in
  List.iteri (fun i (_, r) -> line "%s%s" r (if i = n - 1 then "." else "")) rows;
  List.iter (fun (cname, _) -> implicit cname params) rows;
  if renamed <> []
  then
    line "Extract Inductive %s => %s [ %s ]." rname
      (Print.quote ocaml_type)
      (String.concat " "
         (List.map (fun c -> Print.quote (Print.ocaml_name (modc @ [c.c_name]))) ctors))

let emit_record ~params modc rname fields place =
  line "Record %s%s : Type := { %s }." rname (binders params)
    (String.concat "; "
       (List.map
          (fun (f, ty, _) ->
            declared := SS.add f !declared;
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
let emit_makers ~params modc name rname (sh : shape) place =
  let self_ty = Tr.Constr (Tr.Global (modc @ [name]), List.map (fun p -> Tr.Var p) params) in
  let res_var = if List.mem "Res" params then "Res_" else "Res" in
  let maker mname args result real =
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
    if List.for_all (fun c -> c.c_res = None || c.c_res = Some self_ty) ctors
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

(* [forbidden]: types of the same recursive definition that are declared
   after this one. Returns what is to be written after the whole
   definition (the makers and the eliminator), if anything. *)
let emit ~abstract ~params ~forbidden modc name (decl : Types.type_declaration)
    rname place : (unit -> unit) option =
  let comps = modc @ [name] in
  if not (wanted comps)
  then (
    abstract None;
    None)
  else
    match shape_of decl with
    | exception Tr.Unsupported why ->
      abstract (Some ("abstract, though Simplify takes it apart: its definition has " ^ why));
      None
    | None ->
      abstract None;
      None
    | Some sh -> (
      match check ~forbidden (key comps) sh with
      | exception Refused why ->
        abstract
          (Some
             (why ^ ": abstract, with a maker for each constructor and one eliminator"));
        let saved = !Tr.vars in
        Some
          (fun () ->
            Tr.vars := saved;
            try emit_makers ~params modc name rname sh place
            with Tr.Unsupported why -> not_declared (comps @ ["(makers)"]) why)
      | renamed -> (
        mirror comps;
        (match sh with
        | Variant ctors ->
          emit_variant ~params ~ocaml_type:(Print.ocaml_name comps) modc rname ctors
            renamed place
        | Record fields -> emit_record ~params modc rname fields place);
        None))
