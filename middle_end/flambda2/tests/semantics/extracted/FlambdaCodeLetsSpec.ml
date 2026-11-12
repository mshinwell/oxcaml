open FlambdaKindModel
open FlambdaLoopLetsSpec
open FlambdaModel
open FlambdaNormaliseSpec
open ListDef

(** val code_in_scope : variable list -> variable -> code_metadata ->
    kinds_in_scope **)

let code_in_scope params my_closure metadata =
  params_in_scope params
    (unarize metadata.cm_params_arity)
    ((my_closure, Value) :: [])

(** val remove_unused_defined_lets_in_binding : static_binding -> static_binding
    **)

let remove_unused_defined_lets_in_binding binding =
  match binding with
  | Bind_code (id, c) ->
    let (Code (params, my_closure, ret, exn, metadata, body)) = c in
    Bind_code
      ( id,
        Code
          ( params,
            my_closure,
            ret,
            exn,
            metadata,
            remove_unused_defined_lets_in_loops
              (code_in_scope params my_closure metadata)
              body ) )
  | _ -> binding

(** val remove_unused_defined_lets_in_code : expr -> expr **)

let rec remove_unused_defined_lets_in_code e =
  match e with
  | Let (x, kind, d, body) ->
    Let (x, kind, d, remove_unused_defined_lets_in_code body)
  | Let_static (bindings, body) ->
    Let_static
      ( map remove_unused_defined_lets_in_binding bindings,
        remove_unused_defined_lets_in_code body )
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        remove_unused_defined_lets_in_code_handler h,
        remove_unused_defined_lets_in_code body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, remove_unused_defined_lets_in_code_handler h)
          handlers,
        remove_unused_defined_lets_in_code body )
  | _ -> e

(** val remove_unused_defined_lets_in_code_handler : continuation_handler ->
    continuation_handler **)

and remove_unused_defined_lets_in_code_handler = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, remove_unused_defined_lets_in_code handler)
