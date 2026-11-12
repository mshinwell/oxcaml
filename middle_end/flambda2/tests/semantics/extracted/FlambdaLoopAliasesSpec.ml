open FlambdaAliasesSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaTypesSpec
open ListDef

(** val follow_aliases_in_loops : typing_env -> expr -> expr **)

let rec follow_aliases_in_loops tenv e =
  match e with
  | Let (x, kind, d, body) ->
    Let
      (x, kind, d, follow_aliases_in_loops (typing_env_under_let tenv x d) body)
  | Let_static (bindings, body) ->
    Let_static (bindings, follow_aliases_in_loops tenv body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        follow_aliases_in_loops_in_handler tenv h,
        follow_aliases_in_loops tenv body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, follow_aliases_in_loop tenv h)
          handlers,
        follow_aliases_in_loops tenv body )
  | _ -> e

(** val follow_aliases_in_loops_in_handler : typing_env -> continuation_handler
    -> continuation_handler **)

and follow_aliases_in_loops_in_handler tenv = function
  | Handler (params, metadata, handler) ->
    Handler
      (params, metadata, follow_aliases_in_loops (drop_vars params tenv) handler)

(** val follow_aliases_in_loop : typing_env -> continuation_handler ->
    continuation_handler **)

and follow_aliases_in_loop tenv = function
  | Handler (params, metadata, handler) ->
    Handler
      ( params,
        metadata,
        rewrite_code_body
          (follow_aliases (drop_vars params tenv))
          (follow_aliases_in_loops (drop_vars params tenv) handler) )
