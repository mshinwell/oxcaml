open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open ListDef

(** val remove_unused_defined_lets_in_loops : kinds_in_scope -> expr -> expr **)

let rec remove_unused_defined_lets_in_loops kinds e =
  match e with
  | Let (x, kind, d, body) ->
    let body' = remove_unused_defined_lets_in_loops ((x, kind) :: kinds) body in
    if named_defined kinds kind d && negb (var_free_b x body')
    then body'
    else Let (x, kind, d, body')
  | Let_static (bindings, body) ->
    Let_static (bindings, remove_unused_defined_lets_in_loops kinds body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        remove_unused_defined_lets_in_handler kinds h,
        remove_unused_defined_lets_in_loops kinds body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, remove_unused_defined_lets_in_handler kinds h)
          handlers,
        remove_unused_defined_lets_in_loops kinds body )
  | _ -> e

(** val remove_unused_defined_lets_in_handler : kinds_in_scope ->
    continuation_handler -> continuation_handler **)

and remove_unused_defined_lets_in_handler kinds = function
  | Handler (params, metadata, handler) ->
    Handler
      ( params,
        metadata,
        remove_unused_defined_lets_in_loops
          (params_in_scope params metadata.hm_params_kinds kinds)
          handler )
