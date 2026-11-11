open Datatypes
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

(** val keep_slots : value_slot list -> (value_slot * 'a1) list -> (value_slot *
    'a1) list **)

let keep_slots dropped slots =
  filter (fun slot -> negb (among (fst slot) dropped)) slots

(** val drop_slots_static_const : value_slot list -> static_const ->
    static_const **)

let drop_slots_static_const dropped const =
  match const with
  | Static_const_set_of_closures (code0, value_slots) ->
    Static_const_set_of_closures (code0, keep_slots dropped value_slots)
  | Static_const_closure_of_set
      (slot, closure_symbols, function_decls, value_slots) ->
    Static_const_closure_of_set
      (slot, closure_symbols, function_decls, keep_slots dropped value_slots)
  | _ -> const

(** val drop_slots : value_slot list -> expr -> expr **)

let rec drop_slots dropped e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, drop_slots dropped body)
  | Let_static (bindings, body) ->
    Let_static
      (map (drop_slots_binding dropped) bindings, drop_slots dropped body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, drop_slots_handler dropped h, drop_slots dropped body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, drop_slots_handler dropped h)
          handlers,
        drop_slots dropped body )
  | _ -> e

(** val drop_slots_handler : value_slot list -> continuation_handler ->
    continuation_handler **)

and drop_slots_handler dropped = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, drop_slots dropped handler)

(** val drop_slots_binding : value_slot list -> static_binding -> static_binding
    **)

and drop_slots_binding dropped binding =
  match binding with
  | Bind_code (id, c) -> Bind_code (id, drop_slots_code dropped c)
  | Bind_deleted_code _ -> binding
  | Bind_symbol (s, const) ->
    Bind_symbol (s, drop_slots_static_const dropped const)

(** val drop_slots_code : value_slot list -> code -> code **)

and drop_slots_code dropped = function
  | Code (params, my_closure, ret, exn, metadata, body) ->
    Code (params, my_closure, ret, exn, metadata, drop_slots dropped body)

(** val named_projects_none : value_slot list -> named -> bool **)

let named_projects_none dropped = function
  | Project_value_slot (slot, _) -> negb (among slot dropped)
  | Project_value_slot_from (_, slot, _) -> negb (among slot dropped)
  | _ -> true

(** val slots_unused : value_slot list -> expr -> bool **)

let rec slots_unused dropped = function
  | Let (_, _, d, body) ->
    named_projects_none dropped d && slots_unused dropped body
  | Let_static (bindings, body) ->
    forallb (binding_slots_unused dropped) bindings && slots_unused dropped body
  | Let_cont_non_recursive (_, h, body) ->
    handler_slots_unused dropped h && slots_unused dropped body
  | Let_cont_recursive (handlers, body) ->
    forallb
      (fun pat ->
        let _, h = pat in
        handler_slots_unused dropped h)
      handlers
    && slots_unused dropped body
  | _ -> true

(** val handler_slots_unused : value_slot list -> continuation_handler -> bool **)

and handler_slots_unused dropped = function
  | Handler (_, _, handler) -> slots_unused dropped handler

(** val binding_slots_unused : value_slot list -> static_binding -> bool **)

and binding_slots_unused dropped = function
  | Bind_code (_, c) -> code_slots_unused dropped c
  | _ -> true

(** val code_slots_unused : value_slot list -> code -> bool **)

and code_slots_unused dropped = function
  | Code (_, _, _, _, _, body) -> slots_unused dropped body

(** val drop_unused_slots : value_slot list -> expr -> expr option **)

let drop_unused_slots dropped e =
  if slots_unused dropped e then Some (drop_slots dropped e) else None
