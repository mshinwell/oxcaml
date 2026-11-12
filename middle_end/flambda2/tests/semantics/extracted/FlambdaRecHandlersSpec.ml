open FlambdaModel
open FlambdaNormaliseSpec
open ListDef

(** val rewrite_rec_handlers : (expr -> expr) -> expr -> expr **)

let rec rewrite_rec_handlers f e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, rewrite_rec_handlers f body)
  | Let_static (bindings, body) ->
    Let_static (bindings, rewrite_rec_handlers f body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, rewrite_rec_handlers_in_handler f h, rewrite_rec_handlers f body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, rewrite_rec_handler f h)
          handlers,
        rewrite_rec_handlers f body )
  | _ -> e

(** val rewrite_rec_handlers_in_handler : (expr -> expr) -> continuation_handler
    -> continuation_handler **)

and rewrite_rec_handlers_in_handler f = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, rewrite_rec_handlers f handler)

(** val rewrite_rec_handler : (expr -> expr) -> continuation_handler ->
    continuation_handler **)

and rewrite_rec_handler f = function
  | Handler (params, metadata, handler) ->
    Handler
      (params, metadata, rewrite_code_body f (rewrite_rec_handlers f handler))
