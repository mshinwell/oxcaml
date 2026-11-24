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

let path_of_comps comps : Path.t =
  match comps with
  | [] -> invalid_arg "path_of_comps"
  | u :: rest ->
    List.fold_left
      (fun p s -> Path.Pdot (p, s))
      (Path.Pident (Ident.create_persistent u))
      rest

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

(* ---- names in Rocq ---- *)

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

let value_rocq s = sanitize s

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
