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
    let name = Ident.name ld.ld_id in
    ( name,
      Tr.with_place (Some name) (fun () -> Tr.tr ld.ld_type),
      ld.ld_mutable = Asttypes.Mutable )
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

(* One variant of a definition: its constructors are named. Returns the
   rows of the inductive type. A constructor with an inline record takes
   the fields by place, in the order of the type. *)
let prepare_variant ~params modc rname ctors place =
  let self_ty = applied rname params in
  List.map
    (fun c ->
      let cname =
        if free c.c_name
        then (
          claim_native c.c_name;
          c.c_name)
        else claim (Sigs.sanitize c.c_name)
      in
      add_index (Print.ocaml_name (modc @ [c.c_name])) cname "constructor"
        (List.length c.c_args) place;
      (match c.c_fields with
      | Some fs ->
        List.iteri
          (fun i (f, _) ->
            add_index
              (Print.ocaml_name (modc @ [c.c_name]) ^ " { " ^ f ^ " }")
              (Printf.sprintf "%s, argument %d" cname (i + 1))
              "inline field" 0 place)
          fs
      | None -> ());
      ( cname,
        Printf.sprintf "| %s : %s" cname
          (String.concat " -> " (List.map Print.pp_arg c.c_args @ [self_ty])) ))
    ctors

(* The directive of a mirrored variant: Rocq prints each constructor by the
   compiler's qualified name. With an inline record, the constructor is a
   function of the tuple of its arguments, and the match is a function of
   one function for each constructor, then the scrutinee. The same when a
   later type of the module has a constructor of the same name, which
   hides this one in OCaml: the strings then say the type. [arity]: the
   number of parameters of the type in OCaml. *)
let extract_inductive modc name rname ocaml_type arity ctors =
  let hidden = Sigs.later_constructors modc name in
  let is_hidden c = SS.mem c.c_name hidden in
  if not !in_modtype
  then
    variants
      := ( ocaml_type,
           arity,
           List.map (fun c -> Print.ocaml_name (modc @ [c.c_name])) ctors,
           List.exists is_hidden ctors )
         :: !variants;
  let special = List.exists (fun c -> c.c_fields <> None || is_hidden c) ctors in
  let annotated =
    if arity = 0
    then ocaml_type
    else
      Printf.sprintf "(%s) %s"
        (String.concat ", " (List.init arity (fun _ -> "_")))
        ocaml_type
  in
  let ctor_string c =
    if c.c_fields = None && not (is_hidden c)
    then Print.ocaml_name (modc @ [c.c_name])
    else
      let n = List.length c.c_args in
      let body = Printf.sprintf "(%s : %s)" (ocaml_ctor modc c) annotated in
      if n = 0
      then body
      else
        Printf.sprintf "(fun %s -> %s)"
          (if n = 1 then "x__1" else "(" ^ String.concat ", " (xs n) ^ ")")
          body
  in
  let match_string =
    if not special
    then ""
    else
      " "
      ^ Print.quote
          (Printf.sprintf "(fun %s x__0 -> match (x__0 : %s) with %s)"
             (String.concat " "
                (List.mapi (fun i _ -> Printf.sprintf "f__%d" (i + 1)) ctors))
             annotated
             (String.concat " | "
                (List.mapi
                   (fun i c ->
                     Printf.sprintf "%s -> f__%d %s" (ocaml_ctor modc c) (i + 1)
                       (if c.c_args = []
                        then "()"
                        else String.concat " " (xs (List.length c.c_args))))
                   ctors)))
  in
  directive "Extract Inductive %s => %s [ %s ]%s." rname (Print.quote ocaml_type)
    (String.concat " " (List.map (fun c -> Print.quote (ctor_string c)) ctors))
    match_string

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

(* ---- tuples with labels ---- *)

(* Rocq has no label in a tuple, and OCaml refuses a tuple without its
   labels. So each type of a tuple with labels that the interfaces write
   is a type of its own here, with one constructor. Its directive makes
   the tuple with its labels from a plain tuple, and takes it apart. The
   type is declared in the module that writes it first, before the item
   that writes it. Its name is that of the labelled argument or of the
   field where it is first written, or else its own labels, then
   [_tuple]. *)

(* The labels and the types -> the module that declares the type, and its
   name there. Kept from pass to pass. *)
let labelled : (string, string list * string) Hashtbl.t = Hashtbl.create 17

(* Those declared in this pass. *)
let labelled_now : (string, unit) Hashtbl.t = Hashtbl.create 17

let rec ty_key (ty : Tr.ty) =
  match ty with
  | Var v -> "'" ^ v
  | Arrow (args, res) ->
    "(" ^ String.concat " -> " (List.map ty_key args) ^ " -> M " ^ ty_key res ^ ")"
  | Arrow_pure (args, res) ->
    "(" ^ String.concat " -> " (List.map ty_key (args @ [res])) ^ ")"
  | Tuple l -> "(" ^ String.concat " * " (List.map ty_key l) ^ ")"
  | Constr (r, args) ->
    let name = match r with Tr.Kit s -> s | Tr.Global comps -> key comps in
    "(" ^ String.concat " " (name :: List.map ty_key args) ^ ")"

(* A type of OCaml as OCaml writes it, with the names that the
   realisations have. *)
let rec ocaml_type (ty : Types.type_expr) =
  match Types.get_desc ty with
  | Tconstr (p, args, _) -> (
    let name =
      match source_path !Sigs.base_env p with
      | Pident id when Ident.is_predef id -> Ident.name id
      | p' -> (
        match comps_of_path p' with
        | Some comps -> Print.ocaml_name comps
        | None ->
          raise (Tr.Unsupported ("the type " ^ Path.name p ^ " is not a global name")))
    in
    match args with
    | [] -> name
    | [a] -> ocaml_type_atom a ^ " " ^ name
    | l -> "(" ^ String.concat ", " (List.map ocaml_type l) ^ ") " ^ name)
  | Ttuple l ->
    String.concat " * "
      (List.map
         (fun (label, t) ->
           (match label with Some s -> s ^ ":" | None -> "") ^ ocaml_type_atom t)
         l)
  | Tvariant _ -> (
    match Tr.fixed_tags ty with
    | Some tags ->
      "[ " ^ String.concat " | " (List.map (fun t -> "`" ^ t) tags) ^ " ]"
    | None -> raise (Tr.Unsupported "a polymorphic variant in a tuple with labels"))
  | Tpoly (t, []) -> ocaml_type t
  | Tvar _ | Tunivar _ ->
    raise (Tr.Unsupported "a type variable in a tuple with labels")
  | _ -> raise (Tr.Unsupported "a tuple with labels that holds a function or an object")

and ocaml_type_atom ty =
  match Types.get_desc ty with
  | Ttuple _ -> "(" ^ ocaml_type ty ^ ")"
  | _ -> ocaml_type ty

let ocaml_type_atom_list (l : (string option * Types.type_expr) list) =
  String.concat " * "
    (List.map
       (fun (label, t) ->
         (match label with Some s -> s ^ ":" | None -> "") ^ ocaml_type_atom t)
       l)

let labelled_tuple (l : (string option * Types.type_expr) list) : Tr.ty =
  let written_at = !Tr.place in
  let tys = List.map (fun (_, t) -> Tr.with_place None (fun () -> Tr.tr t)) l in
  if List.fold_left vars_of [] tys <> []
  then raise (Tr.Unsupported "a type variable in a tuple with labels");
  let label_of (label, _) = match label with Some s -> s ^ ":" | None -> "" in
  let k = String.concat " * " (List.map2 (fun c ty -> label_of c ^ ty_key ty) l tys) in
  let home, name =
    match Hashtbl.find_opt labelled k with
    | Some x -> x
    | None ->
      let home = !Print.cur_mod in
      let base =
        match written_at with
        | Some s -> s
        | None -> String.concat "_" (List.filter_map fst l)
      in
      let taken name =
        Hashtbl.fold (fun _ (h, n) found -> found || (h = home && n = name)) labelled false
      in
      let rec fresh i =
        let name =
          if i = 1 then base ^ "_tuple" else Printf.sprintf "%s_tuple%d" base i
        in
        if taken name then fresh (i + 1) else name
      in
      let x = home, fresh 1 in
      Hashtbl.replace labelled k x;
      Tr.changed := true;
      x
  in
  let comps = home @ [name] in
  if home <> !Print.cur_mod
  then
    warn "a tuple with labels (%s) is written in %s; its type is declared in %s" name
      (key !Print.cur_mod) (key home)
  else if not (Hashtbl.mem labelled_now k)
  then (
    Hashtbl.replace labelled_now k ();
    let ocaml = "(" ^ ocaml_type_atom_list l ^ ")" in
    before_item (fun () ->
        let rname = claim name in
        Print.set_type_name comps rname;
        let cname = claim (String.capitalize_ascii name) in
        let vars = xs (List.length l) in
        let tuple = "(" ^ String.concat ", " vars ^ ")" in
        let with_labels =
          "("
          ^ String.concat ", "
              (List.map2
                 (fun (label, _) x ->
                   match label with Some s -> "~" ^ s ^ ":" ^ x | None -> x)
                 l vars)
          ^ ")"
        in
        line
          "(* The tuple with labels %s that the interface writes: Rocq has no \
           label in a tuple. [%s] makes one, and a [match] takes it apart. *)"
          ocaml cname;
        line "Inductive %s : Type :=" rname;
        line "| %s : %s." cname
          (String.concat " -> " (List.map Print.pp_arg tys @ [rname]));
        directive "Extract Inductive %s => %s [ %s ] %s." rname (Print.quote ocaml)
          (Print.quote (Printf.sprintf "(fun %s -> %s)" tuple with_labels))
          (Print.quote
             (Printf.sprintf "(fun f__1 x__0 -> let %s = x__0 in f__1 %s)" with_labels
                (String.concat " " vars)));
        add_index ocaml rname "type" 0 "a tuple with labels";
        add_index ocaml cname "constructor" (List.length l) "a tuple with labels"));
  Tr.Constr (Tr.Global comps, [])

let () = Tr.labelled_tuple := labelled_tuple
