open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedContsSpec

(** val sink_to_use : continuation -> continuation_handler -> expr -> expr
    option **)

let rec sink_to_use k h = function
  | Let (x, kind, d, body0) ->
    if var_free_in_handler_b x h
    then None
    else option_map (fun x0 -> Let (x, kind, d, x0)) (sink_to_use k h body0)
  | Let_static (bindings, body0) ->
    option_map (fun x -> Let_static (bindings, x)) (sink_to_use k h body0)
  | Let_cont_non_recursive (k', handler, body0) ->
    let (Handler (params', metadata', handler')) = handler in
    if
      (negb (Pos.eqb k k') && negb (cont_free_b k handler'))
      && negb (cont_free_in_handler_b k' h)
    then
      option_map
        (fun x ->
          Let_cont_non_recursive (k', Handler (params', metadata', handler'), x))
        (sink_to_use k h body0)
    else None
  | Apply ap ->
    if cont_free_b k (Apply ap)
    then Some (Let_cont_non_recursive (k, h, Apply ap))
    else None
  | Switch (scrutinee, arms) ->
    if arms_apply k arms
    then Some (Let_cont_non_recursive (k, h, Switch (scrutinee, arms)))
    else None
  | _ -> None

(** val sink_conts_to_uses : expr -> expr **)

let rec sink_conts_to_uses e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, sink_conts_to_uses body)
  | Let_static (bindings, body) -> Let_static (bindings, sink_conts_to_uses body)
  | Let_cont_non_recursive (k, handler0, body) -> (
    let (Handler (params, metadata, handler)) = handler0 in
    let h = Handler (params, metadata, sink_conts_to_uses handler) in
    let body0 = sink_conts_to_uses body in
    match sink_to_use k h body0 with
    | Some sunk -> sunk
    | None -> Let_cont_non_recursive (k, h, body0))
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, sink_conts_to_uses body)
  | _ -> e
