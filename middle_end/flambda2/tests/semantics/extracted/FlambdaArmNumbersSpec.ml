open BinNums
open BinPos
open Datatypes
open FlambdaGiveScrutineeSpec
open FlambdaModel
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

(** val number_in_arms : variable -> coq_Z option -> expr -> expr **)

let rec number_in_arms x known e =
  match e with
  | Let (y, kind, d, body) ->
    Let (y, kind, d, number_in_arms x (if Pos.eqb y x then None else known) body)
  | Let_static (bindings, body) ->
    Let_static (bindings, number_in_arms x known body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        number_in_handler x
          (match arm_fact x k body with Some c -> Some c | None -> known)
          h,
        number_in_arms x known body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, number_in_handler x known h)
          handlers,
        number_in_arms x known body )
  | Apply_cont ac -> Apply_cont (number_in_apply_cont x known ac)
  | Switch (scrutinee, arms) ->
    Switch
      ( scrutinee,
        map
          (fun pat ->
            let d, ac = pat in
            d, number_in_apply_cont x (arm_known x scrutinee d known) ac)
          arms )
  | _ -> e

(** val number_in_handler : variable -> coq_Z option -> continuation_handler ->
    continuation_handler **)

and number_in_handler x known = function
  | Handler (params, metadata, handler) ->
    Handler
      (params, metadata, number_in_arms x (known_under x params known) handler)

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
