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

(* The signatures of the compiler's modules, and the names that their items
   take in Rocq. This file follows no file of the compiler. *)

open Common
module SS = Set.Make (String)

(* The environment in which the files of Simplify are compiled (the
   libraries that the build opens for them). *)
let base_env : Env.t ref = ref Env.empty

(* A thing that a file of Simplify makes for itself with a functor of
   outside: its name under [FILE__local], the identifier that the file
   gives it, the environment in which it stands, and its line. *)
type local_root =
  { l_comps : string list;
    l_id : Ident.t;
    l_env : Env.t;
    l_kind : [`Module | `Value | `Type];
    l_line : int;
    l_last_line : int
  }

(* For each unit [FILE__local]: its roots in the order of the file, and the
   source file. *)
let locals : (string, local_root list * string) Hashtbl.t = Hashtbl.create 17

let rec is_prefix prefix l =
  match prefix, l with
  | [], _ -> true
  | p :: prefix, x :: l -> p = x && is_prefix prefix l
  | _ :: _, [] -> false

let root_of comps =
  match comps with
  | u :: _ when is_local_unit u -> (
    match Hashtbl.find_opt locals u with
    | Some (roots, _) -> List.find_opt (fun r -> is_prefix r.l_comps comps) roots
    | None -> None)
  | _ -> None

let path_of_comps comps : Path.t =
  match comps with
  | [] -> invalid_arg "path_of_comps"
  | u :: rest -> (
    match root_of comps with
    | Some r ->
      let rec drop n l = if n = 0 then l else drop (n - 1) (List.tl l) in
      List.fold_left
        (fun p s -> Path.Pdot (p, s))
        (Path.Pident r.l_id)
        (drop (List.length r.l_comps) comps)
    | None -> (
      (* under a module type that is declared: under the module that
         stands for it *)
      let under =
        List.find_opt (fun (_, mt) -> is_prefix mt comps) !modtype_idents
      in
      match under with
      | Some (id, mt) ->
        let rec drop n l = if n = 0 then l else drop (n - 1) (List.tl l) in
        List.fold_left
          (fun p s -> Path.Pdot (p, s))
          (Path.Pident id)
          (drop (List.length mt) comps)
      | None ->
        List.fold_left
          (fun p s -> Path.Pdot (p, s))
          (Path.Pident (Ident.create_persistent u))
          rest))

type module_shape =
  | Signature of Types.signature
  | Alias of string list option
  | Functor
  | Opaque

let shape_cache : (string, module_shape) Hashtbl.t = Hashtbl.create 97

(* The shape of the module of this name. *)
let module_shape comps =
  match Hashtbl.find_opt shape_cache (key comps) with
  | Some s -> s
  | None ->
    let env = !base_env in
    let s =
      match Env.find_module (path_of_comps comps) env with
      | exception Not_found -> Opaque
      | md -> (
        match md.md_type with
        | Mty_alias p -> Alias (comps_of_path (norm_module env p))
        | mty -> (
          match Mtype.scrape env mty with
          | Mty_signature sg -> Signature sg
          | Mty_functor _ -> Functor
          | Mty_alias p -> Alias (comps_of_path (norm_module env p))
          | Mty_ident _ -> Opaque))
    in
    Hashtbl.replace shape_cache (key comps) s;
    s

(* For a module that is an alias: the module that it names, as the
   sources write it ([Flambda.Apply], itself an alias of [Apply_expr]). *)
let alias_as_written comps =
  let env = !base_env in
  match Env.find_module (path_of_comps comps) env with
  | { md_type = Mty_alias p; _ } -> comps_of_path (source_module env p)
  | _ -> None
  | exception Not_found -> None

(* ---- names in Rocq ---- *)

(* The name in Rocq of each module type that is declared (key of its name
   in OCaml): it is not always the one that a module of that name would
   have. *)
let modtype_rocq : (string, string) Hashtbl.t = Hashtbl.create 17

(* Words that Rocq does not take as names, and the names of the kit's types,
   which the declarations write unqualified. *)
let reserved =
  [ "at"; "as"; "by"; "cofix"; "else"; "end"; "exists"; "exists2"; "fix";
    "for"; "forall"; "fun"; "if"; "in"; "let"; "match"; "Prop"; "return";
    "SProp"; "then"; "Type"; "using"; "where"; "with"; "Set"; "Variable";
    "Parameter"; "Definition"; "Axiom"; "Theorem"; "Fixpoint"; "Eval"; "IF";
    "mod"; "Hypothesis"; "CoFixpoint"; "lazymatch"; "multimatch";
    "discriminated"; "M"; "int"; "bool"; "unit"; "string"; "list"; "option";
    "ref"; "lazy_t"; "exn"; "exception"; "tuple3"; "tuple4"; "tuple5";
    "tuple6"; "fmt_args"; "prod"; "Z"; "nat"; "decl" ]

let sanitize s = if List.mem s reserved then s ^ "_" else s

(* Is this a name that Rocq can write? Operators are not. *)
let is_identifier s =
  s <> ""
  && (match s.[0] with 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false)
  && String.for_all
       (function
         | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
         | _ -> false)
       s

(* The name of the file of a compilation unit. *)
let unit_rocq u =
  let s = short_unit u in
  if List.mem s reserved || s = "Stdlib" || s = "Import" || s = "Export"
  then s ^ "_"
  else s

(* A module inside a file: only what Rocq cannot read is renamed
   ([Module Import] is a command of Rocq). *)
let module_rocq s =
  if List.mem s reserved || s = "Import" || s = "Export" then s ^ "_" else s

type names =
  { value_names : SS.t;
    field_names : SS.t
  }

let names_cache : (string, names) Hashtbl.t = Hashtbl.create 97

(* The values and the fields of records that the module declares: a type of
   the same name as one of them gives way. *)
let names_of_module comps =
  match Hashtbl.find_opt names_cache (key comps) with
  | Some n -> n
  | None ->
    let n =
      match module_shape comps with
      | Signature sg ->
        List.fold_left
          (fun n (item : Types.signature_item) ->
            match item with
            | Sig_value (id, _, _) ->
              { n with value_names = SS.add (Ident.name id) n.value_names }
            | Sig_type (_, { type_kind = Type_record (lds, _); _ }, _, _) ->
              List.fold_left
                (fun n (ld : Types.label_declaration) ->
                  { n with
                    field_names = SS.add (Ident.name ld.ld_id) n.field_names
                  })
                n lds
            | _ -> n)
          { value_names = SS.empty; field_names = SS.empty }
          sg
      | Alias _ | Functor | Opaque ->
        { value_names = SS.empty; field_names = SS.empty }
    in
    Hashtbl.replace names_cache (key comps) n;
    n

(* An operator that a module other than [Stdlib] declares (the addition of
   [Code_size], the binding operators of [Or_bottom.Let_syntax]) has a name
   spelled from its characters: [op_plus], [let_op_lt_star]. *)
let operator_name s =
  let spell c =
    match c with
    | '+' -> "plus" | '-' -> "minus" | '*' -> "star" | '/' -> "slash"
    | '<' -> "lt" | '>' -> "gt" | '=' -> "eq" | '!' -> "bang" | '|' -> "bar"
    | '&' -> "amp" | '@' -> "at" | '^' -> "hat" | '~' -> "tilde"
    | ':' -> "colon" | '$' -> "dollar" | '.' -> "dot" | '%' -> "percent"
    | '?' -> "question" | '#' -> "hash"
    | c -> String.make 1 c
  in
  let prefix, symbols =
    let starts p = String.length s > String.length p && String.sub s 0 (String.length p) = p in
    if starts "let"
    then "let_op", String.sub s 3 (String.length s - 3)
    else if starts "and"
    then "and_op", String.sub s 3 (String.length s - 3)
    else "op", s
  in
  String.concat "_" (prefix :: List.map spell (List.of_seq (String.to_seq symbols)))

let value_rocq s = if is_identifier s then sanitize s else operator_name s

(* The constructors of the variants that the module declares after the
   type [name]: in OCaml such a constructor hides one of [name] that has
   the same name. *)
let later_constructors modc name =
  match module_shape modc with
  | Signature sg ->
    let after = ref false and acc = ref SS.empty in
    List.iter
      (fun (item : Types.signature_item) ->
        match item with
        | Sig_type (id, decl, _, _) ->
          if !after
          then (
            match decl.type_kind with
            | Type_variant (cds, _) ->
              List.iter
                (fun (cd : Types.constructor_declaration) ->
                  acc := SS.add (Ident.name cd.cd_id) !acc)
                cds
            | _ -> ())
          else if Ident.name id = name
          then after := true
        | _ -> ())
      sg;
    !acc
  | _ -> SS.empty

(* [modc] is the module that declares the item. *)
let field_rocq modc s =
  let n = names_of_module modc in
  if SS.mem s n.value_names then s ^ "_" else sanitize s

let type_rocq modc s =
  let n = names_of_module modc in
  if SS.mem s n.value_names || SS.mem s n.field_names
  then s ^ "_"
  else sanitize s

let ctor_rocq s = sanitize s
