open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open List

(** val float_over : (expr -> expr) -> expr -> expr **)

let float_over wrap inner =
  match inner with
  | Let_static (bindings, body) ->
    let_static_if_any
      (filter binds_code bindings)
      (wrap
         (let_static_if_any
            (filter (fun binding -> negb (binds_code binding)) bindings)
            body))
  | _ -> wrap inner

(** val float_code : expr -> expr **)

let rec float_code e =
  match e with
  | Let (x, kind, d, body) ->
    float_over (fun x0 -> Let (x, kind, d, x0)) (float_code body)
  | Let_static (bindings, body) -> (
    match float_code body with
    | Let_static (bindings', body') ->
      Let_static (code_first (app bindings bindings'), body')
    | x -> Let_static (code_first bindings, x))
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    float_over
      (fun x ->
        Let_cont_non_recursive
          (k, Handler (params, metadata, float_code handler), x))
      (float_code body)
  | Let_cont_recursive (handlers, body) ->
    float_over (fun x -> Let_cont_recursive (handlers, x)) (float_code body)
  | _ -> e
