open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec

(** val inline_in_group : code_id list -> static_binding list -> static_binding
    list -> static_binding list **)

let rec inline_in_group kept done0 = function
  | [] -> done0
  | binding :: todo0 ->
    let others = codes_of (app done0 todo0) [] in
    inline_in_group kept
      (app done0 (inline_calls_in_binding kept others binding :: []))
      todo0

(** val inline_sibling_calls : code_id list -> expr -> expr **)

let rec inline_sibling_calls kept e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, inline_sibling_calls kept body)
  | Let_static (bindings, body) ->
    Let_static (inline_in_group kept [] bindings, inline_sibling_calls kept body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler (params, metadata, inline_sibling_calls kept handler),
        inline_sibling_calls kept body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, inline_sibling_calls kept body)
  | _ -> e
