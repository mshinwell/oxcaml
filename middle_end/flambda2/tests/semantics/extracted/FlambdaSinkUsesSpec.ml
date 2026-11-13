open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaSinkContsSpec
open FlambdaUnusedContsSpec

(** val sink_to_use : continuation -> continuation_handler -> expr -> expr **)

let rec sink_to_use k h body =
  match body with
  | Let (x, kind, d, rest) ->
    if var_free_in_handler_b x h
    then Let_cont_non_recursive (k, h, body)
    else Let (x, kind, d, sink_to_use k h rest)
  | Let_static (bindings, rest) -> Let_static (bindings, sink_to_use k h rest)
  | Let_cont_non_recursive (k', handler, rest) ->
    let (Handler (params', metadata', handler')) = handler in
    if
      (negb (Pos.eqb k k') && negb (cont_free_b k handler'))
      && negb (cont_free_in_handler_b k' h)
    then
      Let_cont_non_recursive
        (k', Handler (params', metadata', handler'), sink_to_use k h rest)
    else if
      (negb (cont_free_b k rest) && negb (cont_free_in_handler_b k h))
      && params_not_free params' h
    then
      Let_cont_non_recursive
        (k', Handler (params', metadata', sink_to_use k h handler'), rest)
    else Let_cont_non_recursive (k, h, body)
  | _ -> Let_cont_non_recursive (k, h, body)

(** val sink_conts_to_uses : expr -> expr **)

let rec sink_conts_to_uses e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, sink_conts_to_uses body)
  | Let_static (bindings, body) -> Let_static (bindings, sink_conts_to_uses body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    sink_to_use k
      (Handler (params, metadata, sink_conts_to_uses handler))
      (sink_conts_to_uses body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, sink_conts_to_uses body)
  | _ -> e
