open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaBlockLoadSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List
open ListDef

type known_array = simple option list

type known_arrays =
  { known_array_vars : (variable * known_array) list;
    known_array_symbols : (symbol * known_array) list
  }

(** val no_arrays : known_arrays **)

let no_arrays = { known_array_vars = []; known_array_symbols = [] }

(** val forget_in_array : variable -> known_array -> known_array **)

let forget_in_array x array = map (forget_field x) array

(** val forget_array_var : variable -> known_arrays -> known_arrays **)

let forget_array_var x known =
  { known_array_vars =
      map
        (fun entry -> fst entry, forget_in_array x (snd entry))
        (filter
           (fun entry -> negb (Pos.eqb x (fst entry)))
           known.known_array_vars);
    known_array_symbols =
      map
        (fun entry -> fst entry, forget_in_array x (snd entry))
        known.known_array_symbols
  }

(** val forget_array_vars : variable list -> known_arrays -> known_arrays **)

let rec forget_array_vars xs known =
  match xs with
  | [] -> known
  | x :: xs0 -> forget_array_vars xs0 (forget_array_var x known)

(** val array_made_by : named -> known_array option **)

let array_made_by = function
  | Prim (p, elements) -> (
    match p with
    | Variadic p0 -> (
      match p0 with
      | Make_block _ -> None
      | Make_immutable_array _ -> Some (map (fun x -> Some x) elements))
    | _ -> None)
  | _ -> None

(** val arrays_under_let : known_arrays -> variable -> named -> known_arrays **)

let arrays_under_let known x d =
  let known0 = forget_array_var x known in
  match array_made_by d with
  | Some array ->
    { known_array_vars = (x, forget_in_array x array) :: known0.known_array_vars;
      known_array_symbols = known0.known_array_symbols
    }
  | None -> known0

(** val static_array_made : static_binding -> (symbol * known_array) list **)

let static_array_made = function
  | Bind_symbol (s, const) -> (
    match const with
    | Static_const_immutable_value_array elements ->
      (s, map (fun x -> Some x) elements) :: []
    | _ -> [])
  | _ -> []

(** val arrays_under_statics : known_arrays -> static_binding list ->
    known_arrays **)

let arrays_under_statics known bindings =
  { known_array_vars = known.known_array_vars;
    known_array_symbols =
      app (flat_map static_array_made bindings) known.known_array_symbols
  }

(** val known_array_of : known_arrays -> simple -> known_array option **)

let known_array_of known = function
  | Var x -> lookup x known.known_array_vars
  | Symbol sym -> lookup sym known.known_array_symbols
  | Const _ -> None

(** val length_of_known : known_array -> simple option **)

let length_of_known array =
  let n = Z.of_nat (length array) in
  if in_range (int_width Standard_tagged_immediate) n
  then Some (Const (Tagged_immediate n))
  else None

(** val element_loaded : known_array -> simple -> simple option **)

let element_loaded array = function
  | Const c -> (
    match c with
    | Tagged_immediate i ->
      if Z.leb Z0 i
      then match nth_error array (Z.to_nat i) with Some o -> o | None -> None
      else None
    | _ -> None)
  | _ -> None

(** val of_known_array : known_arrays -> prim -> simple list -> simple option **)

let of_known_array known p args =
  match p with
  | Unary p0 -> (
    match p0 with
    | Array_length _ -> (
      match args with
      | [] -> None
      | array :: l -> (
        match l with
        | [] -> (
          match known_array_of known array with
          | Some array0 -> length_of_known array0
          | None -> None)
        | _ :: _ -> None))
    | _ -> None)
  | Binary p0 -> (
    match p0 with
    | Array_load (_, _, _) -> (
      match args with
      | [] -> None
      | array :: l -> (
        match l with
        | [] -> None
        | index :: l0 -> (
          match l0 with
          | [] -> (
            match known_array_of known array with
            | Some array0 -> element_loaded array0 index
            | None -> None)
          | _ :: _ -> None)))
    | _ -> None)
  | _ -> None

(** val load_known_array_named : known_arrays -> named -> named **)

let load_known_array_named known d =
  match d with
  | Prim (p, args) -> (
    match of_known_array known p args with
    | Some result -> Simple result
    | None -> d)
  | _ -> d

(** val load_arrays_knowing : known_arrays -> expr -> expr **)

let rec load_arrays_knowing known e =
  match e with
  | Let (x, kind, d, body) ->
    Let
      ( x,
        kind,
        load_known_array_named known d,
        load_arrays_knowing (arrays_under_let known x d) body )
  | Let_static (bindings, body) ->
    Let_static
      (bindings, load_arrays_knowing (arrays_under_statics known bindings) body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, load_arrays_in_handler known h, load_arrays_knowing known body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, load_arrays_knowing known body)
  | _ -> e

(** val load_arrays_in_handler : known_arrays -> continuation_handler ->
    continuation_handler **)

and load_arrays_in_handler known = function
  | Handler (params, metadata, handler) ->
    Handler
      ( params,
        metadata,
        load_arrays_knowing (forget_array_vars params known) handler )

(** val load_known_arrays : expr -> expr **)

let load_known_arrays e = load_arrays_knowing no_arrays e
