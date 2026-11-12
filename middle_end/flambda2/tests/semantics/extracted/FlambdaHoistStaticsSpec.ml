open Datatypes
open FlambdaModel
open FlambdaSemanticsSpec
open FlambdaStaticsInScopeSpec
open FlambdaWellFormedSpec
open List

(** val is_hoisted : static_binding -> bool **)

let is_hoisted = function
  | Bind_code (_, _) -> true
  | Bind_deleted_code _ -> false
  | Bind_symbol (_, const) -> (
    match eval_static_const [] const with Some _ -> true | None -> false)

(** val hoisted_bindings : expr -> static_binding list **)

let rec hoisted_bindings = function
  | Let (_, _, _, body) -> hoisted_bindings body
  | Let_static (bindings, body) ->
    app (filter is_hoisted bindings) (hoisted_bindings body)
  | Let_cont_non_recursive (_, h, body) ->
    app (hoisted_bindings body) (handler_hoisted_bindings h)
  | Let_cont_recursive (_, body) -> hoisted_bindings body
  | _ -> []

(** val handler_hoisted_bindings : continuation_handler -> static_binding list **)

and handler_hoisted_bindings = function
  | Handler (_, _, handler) -> hoisted_bindings handler

(** val without_hoisted : expr -> expr **)

let rec without_hoisted e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, without_hoisted body)
  | Let_static (bindings, body) ->
    Let_static
      ( filter (fun binding -> negb (is_hoisted binding)) bindings,
        without_hoisted body )
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive (k, handler_without_hoisted h, without_hoisted body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, without_hoisted body)
  | _ -> e

(** val handler_without_hoisted : continuation_handler -> continuation_handler **)

and handler_without_hoisted = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, without_hoisted handler)

(** val hoist_statics : unit_interface -> expr -> expr option **)

let hoist_statics u e =
  if
    ((well_formed_unit u e && statics_in_scope [] e)
    && interface_conts_not_rebound u e)
    && static_names_apart [] e
  then Some (Let_static (hoisted_bindings e, without_hoisted e))
  else None
