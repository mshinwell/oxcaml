open BinNums
open BinPos
open Datatypes
open FlambdaGiveScrutineeSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaUntagParamsSpec
open List
open ListDef
open OxCamlList

(** val number_simple : variable -> coq_Z -> simple -> simple **)

let number_simple x c s =
  match s with
  | Var y -> if Pos.eqb y x then Const (Naked_immediate c) else s
  | _ -> s

(** val number_in_apply_cont : variable -> coq_Z option -> apply_cont ->
    apply_cont **)

let number_in_apply_cont x known ac =
  match known with
  | Some c ->
    { ac_continuation = ac.ac_continuation;
      ac_args = map (number_simple x c) ac.ac_args;
      ac_trap_action = ac.ac_trap_action
    }
  | None -> ac

(** val source_under_let : variable -> variable -> named -> variable option ->
    variable option **)

let source_under_let x y d source =
  if Pos.eqb y x
  then
    match untag_of d with
    | Some t -> if Pos.eqb t x then None else Some t
    | None -> None
  else
    match source with
    | Some t -> if Pos.eqb y t then None else source
    | None -> None

(** val source_under : variable -> variable list -> variable option -> variable
    option **)

let source_under x params source =
  if among x params
  then None
  else
    match source with
    | Some t -> if among t params then None else source
    | None -> None

(** val number_read : variable -> variable option -> coq_Z -> simple -> simple **)

let number_read x source c s =
  match s with
  | Var y -> (
    if Pos.eqb y x
    then Const (Naked_immediate c)
    else
      match source with
      | Some t -> if Pos.eqb y t then Const (Tagged_immediate c) else s
      | None -> s)
  | _ -> s

(** val number_in_named : variable -> variable option -> coq_Z option -> named
    -> named **)

let number_in_named x source known d =
  match known with
  | Some c -> (
    match d with
    | Simple s -> Simple (number_read x source c s)
    | Prim (p, args) -> Prim (p, map (number_read x source c) args)
    | _ -> d)
  | None -> d

(** val number_in_scrutinee : variable -> variable option -> coq_Z option ->
    simple -> simple **)

let number_in_scrutinee x source known scrutinee =
  match known with
  | Some c -> number_read x source c scrutinee
  | None -> scrutinee

(** val number_in_region : variable -> variable option -> coq_Z option -> expr
    -> expr **)

let rec number_in_region x source known e =
  match e with
  | Let (y, kind, d, body) ->
    Let
      ( y,
        kind,
        number_in_named x source known d,
        number_in_region x
          (source_under_let x y d source)
          (if Pos.eqb y x then None else known)
          body )
  | Let_static (bindings, body) ->
    Let_static (bindings, number_in_region x source known body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        number_in_handler x source
          (match arm_fact x k body with Some c -> Some c | None -> known)
          h,
        number_in_region x source known body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, number_in_handler x source known h)
          handlers,
        number_in_region x source known body )
  | Apply_cont ac -> Apply_cont (number_in_apply_cont x known ac)
  | Switch (scrutinee, arms) ->
    Switch
      ( number_in_scrutinee x source known scrutinee,
        map
          (fun pat ->
            let d, ac = pat in
            d, number_in_apply_cont x (arm_known x scrutinee d known) ac)
          arms )
  | _ -> e

(** val number_in_handler : variable -> variable option -> coq_Z option ->
    continuation_handler -> continuation_handler **)

and number_in_handler x source known = function
  | Handler (params, metadata, handler) ->
    Handler
      ( params,
        metadata,
        number_in_region x
          (source_under x params source)
          (known_under x params known)
          handler )

(** val number_in_arms : variable -> coq_Z option -> expr -> expr **)

let number_in_arms x known e = number_in_region x None known e

(** val scrutinees : expr -> variable list **)

let rec scrutinees = function
  | Let (_, _, _, body) -> scrutinees body
  | Let_static (_, body) -> scrutinees body
  | Let_cont_non_recursive (_, h, body) ->
    app (handler_scrutinees h) (scrutinees body)
  | Let_cont_recursive (handlers, body) ->
    app
      (flat_map
         (fun pat ->
           let _, h = pat in
           handler_scrutinees h)
         handlers)
      (scrutinees body)
  | Switch (scrutinee, _) -> (
    match scrutinee with Var x -> x :: [] | _ -> [])
  | _ -> []

(** val handler_scrutinees : continuation_handler -> variable list **)

and handler_scrutinees = function
  | Handler (_, _, handler) -> scrutinees handler

(** val numbers_in_arms : expr -> expr **)

let numbers_in_arms e =
  fold_left (fun e0 x -> number_in_arms x None e0) e (scrutinees e)
