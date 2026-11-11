open BinPos
open Datatypes
open FlambdaBlockLoadSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List

type wrapping =
  | Boxed of boxable_number
  | Tagged

(** val wrapping_eq_dec : wrapping -> wrapping -> bool **)

let wrapping_eq_dec w w' =
  match w with
  | Boxed kind -> (
    match w' with
    | Boxed kind0 -> (
      match kind with
      | Boxable_naked_float32 -> (
        match kind0 with Boxable_naked_float32 -> true | _ -> false)
      | Boxable_naked_float -> (
        match kind0 with Boxable_naked_float -> true | _ -> false)
      | Boxable_naked_int32 -> (
        match kind0 with Boxable_naked_int32 -> true | _ -> false)
      | Boxable_naked_int64 -> (
        match kind0 with Boxable_naked_int64 -> true | _ -> false)
      | Boxable_naked_nativeint -> (
        match kind0 with Boxable_naked_nativeint -> true | _ -> false)
      | Boxable_naked_vec128 -> (
        match kind0 with Boxable_naked_vec128 -> true | _ -> false)
      | Boxable_naked_vec256 -> (
        match kind0 with Boxable_naked_vec256 -> true | _ -> false)
      | Boxable_naked_vec512 -> (
        match kind0 with Boxable_naked_vec512 -> true | _ -> false)
      | Boxable_naked_mask -> (
        match kind0 with Boxable_naked_mask -> true | _ -> false))
    | Tagged -> false)
  | Tagged -> ( match w' with Boxed _ -> false | Tagged -> true)

(** val wrapping_eqb : wrapping -> wrapping -> bool **)

let wrapping_eqb w w' = if wrapping_eq_dec w w' then true else false

type known_numbers =
  { known_wrapped_vars : (variable * (wrapping * simple)) list;
    known_boxed_symbols : (symbol * const) list
  }

(** val no_numbers : known_numbers **)

let no_numbers = { known_wrapped_vars = []; known_boxed_symbols = [] }

(** val forget_wrapped_var : variable -> known_numbers -> known_numbers **)

let forget_wrapped_var x known =
  { known_wrapped_vars =
      filter
        (fun entry ->
          negb (Pos.eqb x (fst entry))
          && negb (var_in_simple x (snd (snd entry))))
        known.known_wrapped_vars;
    known_boxed_symbols = known.known_boxed_symbols
  }

(** val forget_wrapped_vars : variable list -> known_numbers -> known_numbers **)

let rec forget_wrapped_vars xs known =
  match xs with
  | [] -> known
  | x :: xs0 -> forget_wrapped_vars xs0 (forget_wrapped_var x known)

(** val number_wrapped : named -> (wrapping * simple) option **)

let number_wrapped = function
  | Prim (p, args) -> (
    match unary_applied p args with
    | Some p0 -> (
      let u, contents = p0 in
      match u with
      | Box_number kind -> Some (Boxed kind, contents)
      | Tag_immediate -> Some (Tagged, contents)
      | _ -> None)
    | None -> None)
  | _ -> None

(** val numbers_under_let : known_numbers -> variable -> named -> known_numbers
    **)

let numbers_under_let known x d =
  let known0 = forget_wrapped_var x known in
  match number_wrapped d with
  | Some p ->
    let how, contents = p in
    if var_in_simple x contents
    then known0
    else
      { known_wrapped_vars = (x, (how, contents)) :: known0.known_wrapped_vars;
        known_boxed_symbols = known0.known_boxed_symbols
      }
  | None -> known0

(** val static_number_boxed : static_binding -> (symbol * const) list **)

let static_number_boxed = function
  | Bind_symbol (s, const0) -> (
    match const0 with
    | Static_const_boxed_number contents -> (
      match contents with Const c -> (s, c) :: [] | _ -> [])
    | _ -> [])
  | _ -> []

(** val numbers_under_statics : known_numbers -> static_binding list ->
    known_numbers **)

let numbers_under_statics known bindings =
  { known_wrapped_vars = known.known_wrapped_vars;
    known_boxed_symbols =
      app (flat_map static_number_boxed bindings) known.known_boxed_symbols
  }

(** val unwrapped : known_numbers -> wrapping -> simple -> simple option **)

let unwrapped known how = function
  | Var x -> (
    match lookup x known.known_wrapped_vars with
    | Some p ->
      let how', contents = p in
      if wrapping_eqb how how' then Some contents else None
    | None -> None)
  | Symbol s -> (
    match how with
    | Boxed kind -> (
      match lookup s known.known_boxed_symbols with
      | Some c -> if is_number_of_kind kind c then Some (Const c) else None
      | None -> None)
    | Tagged -> None)
  | Const _ -> None

(** val unwrapping_of_known : known_numbers -> prim -> simple list -> simple
    option **)

let unwrapping_of_known known p args =
  match unary_applied p args with
  | Some p0 -> (
    let u, tagged = p0 in
    match u with
    | Unbox_number kind -> unwrapped known (Boxed kind) tagged
    | Untag_immediate -> unwrapped known Tagged tagged
    | _ -> None)
  | None -> None

(** val unbox_known_named : known_numbers -> named -> named **)

let unbox_known_named known d =
  match d with
  | Prim (p, args) -> (
    match unwrapping_of_known known p args with
    | Some contents -> Simple contents
    | None -> d)
  | _ -> d

(** val unbox_numbers_knowing : known_numbers -> expr -> expr **)

let rec unbox_numbers_knowing known e =
  match e with
  | Let (x, kind, d, body) ->
    Let
      ( x,
        kind,
        unbox_known_named known d,
        unbox_numbers_knowing (numbers_under_let known x d) body )
  | Let_static (bindings, body) ->
    Let_static
      ( bindings,
        unbox_numbers_knowing (numbers_under_statics known bindings) body )
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, unbox_numbers_in_handler known h, unbox_numbers_knowing known body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, unbox_numbers_knowing known body)
  | _ -> e

(** val unbox_numbers_in_handler : known_numbers -> continuation_handler ->
    continuation_handler **)

and unbox_numbers_in_handler known = function
  | Handler (params, metadata, handler) ->
    Handler
      ( params,
        metadata,
        unbox_numbers_knowing (forget_wrapped_vars params known) handler )

(** val unbox_known_numbers : expr -> expr **)

let unbox_known_numbers e = unbox_numbers_knowing no_numbers e
