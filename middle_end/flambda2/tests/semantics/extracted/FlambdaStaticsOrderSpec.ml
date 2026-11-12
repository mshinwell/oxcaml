open BinPos
open FlambdaModel
open List

(** val binds_same_name : static_binding -> static_binding -> bool **)

let binds_same_name binding binding' =
  match binding with
  | Bind_code (id, _) -> (
    match binding' with Bind_code (id', _) -> Pos.eqb id id' | _ -> false)
  | Bind_deleted_code _ -> false
  | Bind_symbol (s, _) -> (
    match binding' with Bind_symbol (s', _) -> Pos.eqb s s' | _ -> false)

(** val to_front : (static_binding -> bool) -> static_binding list ->
    static_binding list **)

let rec to_front is_it bindings =
  match bindings with
  | [] -> []
  | binding :: rest -> (
    if is_it binding
    then bindings
    else
      match to_front is_it rest with
      | [] -> bindings
      | found :: rest' ->
        if is_it found then found :: binding :: rest' else bindings)

(** val order_as : static_binding list -> static_binding list -> static_binding
    list **)

let order_as pattern bindings =
  fold_right
    (fun named bindings0 -> to_front (binds_same_name named) bindings0)
    bindings pattern

(** val order_statics_as : expr -> expr -> expr **)

let rec order_statics_as pattern e =
  match e with
  | Let (x, kind, d, body) -> (
    match pattern with
    | Let (_, _, _, pattern0) -> Let (x, kind, d, order_statics_as pattern0 body)
    | _ -> e)
  | Let_static (bindings, body) -> (
    match pattern with
    | Let_static (pattern_bindings, pattern0) ->
      Let_static
        (order_as pattern_bindings bindings, order_statics_as pattern0 body)
    | _ -> e)
  | Let_cont_non_recursive (k, handler0, body) -> (
    let (Handler (params, metadata, handler)) = handler0 in
    match pattern with
    | Let_cont_non_recursive (_, handler1, pattern0) ->
      let (Handler (_, _, pattern_handler)) = handler1 in
      Let_cont_non_recursive
        ( k,
          Handler (params, metadata, order_statics_as pattern_handler handler),
          order_statics_as pattern0 body )
    | _ -> e)
  | Let_cont_recursive (handlers, body) -> (
    match pattern with
    | Let_cont_recursive (_, pattern0) ->
      Let_cont_recursive (handlers, order_statics_as pattern0 body)
    | _ -> e)
  | _ -> e
