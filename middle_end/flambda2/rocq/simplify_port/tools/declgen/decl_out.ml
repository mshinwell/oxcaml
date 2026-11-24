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

(* The declarations of one compilation unit, written in the form of the
   port's guide: values and exceptions here, types in [Emit_types]. This
   file follows no file of the compiler. *)

open Common
module SS = Set.Make (String)

let buf = ref (Buffer.create 65536)

(* OCaml name, Rocq name, kind, arity, place. *)
let index : (string * string * string * int * string) list ref = ref []

(* OCaml name, why it is not declared. *)
let left : (string * string) list ref = ref []

(* The names already declared in the module that is open, in Rocq. *)
let declared : SS.t ref = ref SS.empty

let indent () = String.make (2 * (List.length !Print.cur_mod - 1)) ' '

let line fmt =
  Printf.ksprintf
    (fun s ->
      Buffer.add_string !buf (indent ());
      Buffer.add_string !buf s;
      Buffer.add_char !buf '\n')
    fmt

(* Where the item that is being written begins in the buffer. *)
let item_start = ref (-1)

let begin_item () = item_start := Buffer.length !buf

(* Writes the lines of [f] before the item that is being written. *)
let before_item f =
  let outer = !buf in
  let b = Buffer.create 1024 in
  buf := b;
  (match f () with
  | () -> buf := outer
  | exception e ->
    buf := outer;
    raise e);
  let text = Buffer.contents b in
  let n = Buffer.length outer in
  let pos = if !item_start < 0 || !item_start > n then n else !item_start in
  let rest = Buffer.sub outer pos (n - pos) in
  Buffer.truncate outer pos;
  Buffer.add_string outer text;
  Buffer.add_string outer rest;
  item_start := pos + String.length text

(* The names of constructors and fields that the open module has under
   the compiler's own names (Rocq prints them, so they cannot change). *)
let native : SS.t ref = ref SS.empty

(* The same for every module, in the pass before and in this one: a value
   or a type of one of these names gives way, wherever it is declared. *)
let native_before : (string, SS.t) Hashtbl.t = Hashtbl.create 97

let native_now : (string, SS.t) Hashtbl.t = Hashtbl.create 97

(* A name for a value or a type that is free in the open module: one more
   underscore if not. *)
let rec claim name =
  let kept =
    Option.value ~default:SS.empty
      (Hashtbl.find_opt native_before (key !Print.cur_mod))
  in
  if SS.mem name !declared || SS.mem name kept
  then claim (name ^ "_")
  else (
    declared := SS.add name !declared;
    name)

(* A constructor or a field takes the compiler's name. *)
let claim_native name =
  native := SS.add name !native;
  declared := SS.add name !declared;
  let k = key !Print.cur_mod in
  Hashtbl.replace native_now k
    (SS.add name (Option.value ~default:SS.empty (Hashtbl.find_opt native_now k)))

let rocq_qualified name =
  match !Print.cur_mod with
  | u :: mods ->
    String.concat "."
      ((Sigs.unit_rocq u :: List.map Sigs.module_rocq mods) @ [name])
  | [] -> name

(* Inside a module type: its items have no directive (Rocq honours none
   there: what a functor uses of its parameter is printed by its name in
   Rocq) and no row in the index (they are no names of OCaml). *)
let in_modtype = ref false

let add_index ocaml rname kind arity place =
  if not !in_modtype
  then index := (ocaml, rocq_qualified rname, kind, arity, place) :: !index

(* A directive of the extraction. *)
let directive fmt =
  Printf.ksprintf (fun s -> if not !in_modtype then line "%s" s) fmt

let not_declared comps why =
  left := (Print.ocaml_name comps, why) :: !left;
  line "(* NOT DECLARED: %s: %s. *)" (Print.ocaml_name comps) why

let comment (loc : Location.t) fallback =
  let place, text = Src.place_and_text loc in
  (match text with
  | Some t -> line "(* %s  %s *)" place t
  | None -> line "(* %s  %s *)" place (Src.one_line fallback));
  place

let extract rname ocaml =
  directive "Extract Inlined Constant %s => %s." rname (Print.quote ocaml)

(* The directive for a type. One without parameters has its OCaml name as
   an inlined string. One with parameters cannot (Rocq has no inlined
   string for a type with parameters): Rocq prints it by its own name in
   Rocq, which is the compiler's when the modules have the compiler's
   names. *)
let extract_type ?(kept = []) rname ocaml nparams =
  (* [kept]: for each parameter of the type in OCaml, whether Rocq has it
     (an index that was dropped is [_] in OCaml) *)
  let kept = if kept = [] then List.init nparams (fun _ -> true) else kept in
  let n = ref 0 in
  let args =
    List.map
      (fun k ->
        if k
        then (
          incr n;
          Printf.sprintf "'a%d" !n)
        else "_")
      kept
  in
  let applied =
    if args = [] then ocaml else Printf.sprintf "(%s) %s" (String.concat ", " args) ocaml
  in
  if nparams = 0
  then extract rname applied
  else
    let vars = List.init nparams (fun i -> Printf.sprintf "'a%d" (i + 1)) in
    directive "Extract Constant %s %s => %s." rname
      (String.concat " " (List.map Print.quote vars))
      (Print.quote applied)

(* What the kit gives: not declared again. *)
let in_kit =
  [ "Stdlib.ref"; "Stdlib.raise"; "Stdlib.raise_notrace"; "Stdlib.ignore";
    "Stdlib.compare"; "Stdlib.succ"; "Stdlib.pred"; "Stdlib.max"; "Stdlib.min";
    "Stdlib.not"; "Stdlib__Lazy.force"; "Stdlib.Not_found"; "Misc.fatal_error";
    "Misc.fatal_errorf"; "Misc.Fatal_error" ]

let type_text (ty : Types.type_expr) =
  Format.asprintf "%a" Printtyp.type_scheme ty

(* The realisation of a function: its plain name; with optional arguments,
   a closed function that gives each its label. *)
let realisation ocaml (labels : Asttypes.arg_label list) =
  if List.for_all
       (fun (l : Asttypes.arg_label) ->
         match l with Optional _ -> false | _ -> true)
       labels
  then ocaml
  else
    let binders = List.mapi (fun i _ -> Printf.sprintf "x__%d" (i + 1)) labels in
    let args =
      List.map2
        (fun (l : Asttypes.arg_label) x ->
          match l with Optional s -> "?" ^ s ^ ":" ^ x | _ -> x)
        labels binders
    in
    Printf.sprintf "(fun %s -> %s %s)" (String.concat " " binders) ocaml
      (String.concat " " args)

let max_format_args = 16

let emit_value modc name =
  let comps = modc @ [name] in
  let ocaml = Print.ocaml_name comps in
  if List.mem (key comps) in_kit
  then line "(* %s: in the kit (Port_monad.v). *)" ocaml
  else if (not (Sigs.is_identifier name)) && List.hd comps = "Stdlib"
  then not_declared comps "an operator of Stdlib: the kit and Rocq have their own"
  else
    match Env.find_value (Sigs.path_of_comps comps) !Sigs.base_env with
    | exception Not_found -> not_declared comps "not found in the interface"
    | vd -> (
      Tr.reset_vars ();
      try
        match Types.get_desc vd.val_type with
        | Tarrow _ ->
          let ty, labels, is_format = Tr.tr_arrow vd.val_type in
          if not is_format
          then (
            let text = Print.pp ty in
            let rname = claim (Sigs.value_rocq name) in
            let place = comment vd.val_loc ("val " ^ name ^ " : " ^ type_text vd.val_type) in
            line "Parameter %s : %s%s." rname (Print.quantifier ()) text;
            extract rname (realisation ocaml labels);
            add_index ocaml rname "value" (List.length labels) place)
          else (
            (* a family: one declaration for each number of arguments
               after the format *)
            let args, res =
              match ty with Arrow (args, res) -> args, res | _ -> assert false
            in
            let before = args in
            let own = Tr.var_names () in
            let prefix = if List.exists (fun v -> String.length v > 1 && v.[0] = 'A') own then "B" else "A" in
            let place = comment vd.val_loc ("val " ^ name ^ " : " ^ type_text vd.val_type) in
            for n = 0 to max_format_args do
              let extra = List.init n (fun i -> Printf.sprintf "%s%d" prefix (i + 1)) in
              let ty' = Tr.Arrow (before @ List.map (fun v -> Tr.Var v) extra, res) in
              let vars = own @ extra in
              let q =
                if vars = []
                then ""
                else Printf.sprintf "forall {%s : Type}, " (String.concat " " vars)
              in
              let rname = claim (Printf.sprintf "%s%d" (Sigs.value_rocq name) n) in
              line "Parameter %s : %s%s." rname q (Print.pp ty');
              extract rname ocaml;
              add_index ocaml rname "value" (List.length before + n) place
            done)
        | _ ->
          let ty = Tr.tr vd.val_type in
          let text = Print.pp ty in
          let rname = claim (Sigs.value_rocq name) in
          let place = comment vd.val_loc ("val " ^ name ^ " : " ^ type_text vd.val_type) in
          line "Parameter %s : %s%s." rname (Print.quantifier ()) text;
          extract rname ocaml;
          add_index ocaml rname "value" 0 place
      with Tr.Unsupported why -> not_declared comps why)

let emit_exception modc name (ext : Types.extension_constructor) =
  let comps = modc @ [name] in
  let ocaml = Print.ocaml_name comps in
  if List.mem (key comps) in_kit
  then line "(* %s: in the kit (Port_monad.v). *)" ocaml
  else (
    Tr.reset_vars ();
    try
      let payload, real =
        match ext.ext_args with
        | Cstr_tuple [] ->
          ( "unit",
            Printf.sprintf "((fun () -> %s), (function %s -> Some () | _ -> None))"
              ocaml ocaml )
        | Cstr_tuple [t] ->
          ( Print.pp_atom (Tr.tr t),
            Printf.sprintf
              "((fun x__1 -> %s x__1), (function %s x__1 -> Some x__1 | _ -> None))"
              ocaml ocaml )
        | Cstr_tuple l ->
          let binders = List.mapi (fun i _ -> Printf.sprintf "x__%d" (i + 1)) l in
          let tuple = "(" ^ String.concat ", " binders ^ ")" in
          ( Print.pp_atom (Tr.Tuple (List.map Tr.tr l)),
            Printf.sprintf
              "((fun %s -> %s %s), (function %s %s -> Some %s | _ -> None))" tuple
              ocaml tuple ocaml tuple tuple )
        | Cstr_record _ -> raise (Tr.Unsupported "an exception with a record")
      in
      let rname = claim (Sigs.ctor_rocq name) in
      let place = comment ext.ext_loc ("exception " ^ name) in
      line "Parameter %s : exception %s." rname payload;
      extract rname real;
      add_index ocaml rname "exception" 0 place
    with Tr.Unsupported why -> not_declared comps why)
