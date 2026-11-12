open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedContsSpec
open List

(** val applied_at_tail : continuation -> continuation_handler -> expr -> bool **)

let applied_at_tail k h body =
  let (Handler (params, metadata, handler)) = h in
  match inline_cont_at_tail k params metadata handler body with
  | Some _ -> true
  | None -> false

(** val params_not_free : variable list -> continuation_handler -> bool **)

let params_not_free params h =
  forallb (fun param -> negb (var_free_in_handler_b param h)) params

(** val sink_into_handler : continuation -> continuation_handler -> expr -> expr
    option **)

let rec sink_into_handler k h = function
  | Let (x, kind, d, body0) ->
    if var_free_in_handler_b x h
    then None
    else
      option_map (fun x0 -> Let (x, kind, d, x0)) (sink_into_handler k h body0)
  | Let_static (bindings, body0) ->
    option_map (fun x -> Let_static (bindings, x)) (sink_into_handler k h body0)
  | Let_cont_non_recursive (k', handler, body0) ->
    let (Handler (params', metadata', handler')) = handler in
    if
      (negb (cont_free_b k body0) && negb (cont_free_in_handler_b k h))
      && params_not_free params' h
    then
      match sink_into_handler k h handler' with
      | Some sunk ->
        Some
          (Let_cont_non_recursive (k', Handler (params', metadata', sunk), body0))
      | None ->
        if applied_at_tail k h handler'
        then
          Some
            (Let_cont_non_recursive
               ( k',
                 Handler
                   (params', metadata', Let_cont_non_recursive (k, h, handler')),
                 body0 ))
        else None
    else if
      (negb (Pos.eqb k k') && negb (cont_free_b k handler'))
      && negb (cont_free_in_handler_b k' h)
    then
      option_map
        (fun x ->
          Let_cont_non_recursive (k', Handler (params', metadata', handler'), x))
        (sink_into_handler k h body0)
    else None
  | _ -> None

(** val sink_let_conts : expr -> expr **)

let rec sink_let_conts e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, sink_let_conts body)
  | Let_static (bindings, body) -> Let_static (bindings, sink_let_conts body)
  | Let_cont_non_recursive (k, handler0, body) -> (
    let (Handler (params, metadata, handler)) = handler0 in
    let h = Handler (params, metadata, sink_let_conts handler) in
    let body0 = sink_let_conts body in
    match sink_into_handler k h body0 with
    | Some sunk -> sunk
    | None -> Let_cont_non_recursive (k, h, body0))
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, sink_let_conts body)
  | _ -> e
