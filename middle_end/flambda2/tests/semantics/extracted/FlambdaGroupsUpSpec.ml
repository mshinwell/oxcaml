open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec

(** val group_over : (expr -> expr) -> expr -> expr **)

let group_over wrap inner =
  match inner with
  | Let_static (bindings, body) -> Let_static (bindings, wrap body)
  | _ -> wrap inner

(** val groups_up : expr -> expr **)

let rec groups_up e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, groups_up body)
  | Let_static (bindings, body) -> (
    match groups_up body with
    | Let_static (bindings', body') ->
      Let_static (code_first (app bindings bindings'), body')
    | x -> Let_static (code_first bindings, x))
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    group_over
      (fun x ->
        Let_cont_non_recursive
          (k, Handler (params, metadata, groups_up handler), x))
      (groups_up body)
  | Let_cont_recursive (handlers, body) ->
    group_over (fun x -> Let_cont_recursive (handlers, x)) (groups_up body)
  | _ -> e
