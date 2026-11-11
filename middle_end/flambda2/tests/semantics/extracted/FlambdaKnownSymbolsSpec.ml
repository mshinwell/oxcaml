open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaSemanticsSpec
open FlambdaValueSpec
open List
open ListDef
open OxCamlOption

(** val closed_simple : simple -> bool **)

let closed_simple = function Var _ -> false | _ -> true

(** val closed_static_const : static_const -> bool **)

let closed_static_const = function
  | Static_const_set_of_closures (_, value_slots) ->
    forallb (fun slot -> closed_simple (snd slot)) value_slots
  | Static_const_closure_of_set (_, _, _, value_slots) ->
    forallb (fun slot -> closed_simple (snd slot)) value_slots
  | Static_const_block (_, fields) -> forallb closed_simple fields
  | Static_const_boxed_number contents -> closed_simple contents
  | Static_const_immutable_string _ -> true

(** val known_of_binding : static_binding -> (symbol * static_const) list **)

let known_of_binding = function
  | Bind_symbol (s, const) ->
    if closed_static_const const
    then
      match eval_static_const [] const with
      | Some _ -> (s, const) :: []
      | None -> []
    else []
  | _ -> []

(** val known_bindings : expr -> (symbol * static_const) list **)

let rec known_bindings = function
  | Let (_, _, _, body) -> known_bindings body
  | Let_static (bindings, body) ->
    app (flat_map known_of_binding bindings) (known_bindings body)
  | Let_cont_non_recursive (_, h, body) ->
    app (known_bindings_of_handler h) (known_bindings body)
  | Let_cont_recursive (handlers, body) ->
    app
      (flat_map
         (fun pat ->
           let _, h = pat in
           known_bindings_of_handler h)
         handlers)
      (known_bindings body)
  | _ -> []

(** val known_bindings_of_handler : continuation_handler -> (symbol *
    static_const) list **)

and known_bindings_of_handler = function
  | Handler (_, _, handler) -> known_bindings handler

(** val known_value : (symbol * static_const) -> (symbol *
    statically_allocated_value) list **)

let known_value binding =
  match eval_static_const [] (snd binding) with
  | Some allocated -> (fst binding, allocated) :: []
  | None -> []

(** val known_statics : (symbol * static_const) list -> static_env **)

let known_statics known =
  { static_code = []; static_values = flat_map known_value known }

(** val simple_known : static_env -> simple -> bool **)

let simple_known statics = function
  | Var _ -> false
  | Symbol sym -> is_some (lookup sym statics.static_values)
  | Const _ -> true

(** val named_known : static_env -> named -> bool **)

let named_known statics = function
  | Prim (p, args) -> prim_may_fold p && forallb (simple_known statics) args
  | Project_value_slot (_, closure) -> simple_known statics closure
  | Project_value_slot_from (_, _, closure) -> simple_known statics closure
  | Project_function_slot (_, _, closure) -> simple_known statics closure
  | _ -> false

(** val fold_known_named : static_env -> named -> named **)

let fold_known_named statics d =
  if named_known statics d
  then
    match eval_named statics [] d with
    | Some v -> (
      match v with
      | Value_const c -> Simple (Const c)
      | Value_symbol s -> Simple (Symbol s)
      | _ -> d)
    | None -> d
  else d

(** val fold_known : static_env -> expr -> expr **)

let rec fold_known statics e =
  match e with
  | Let (x, kind, d, body) ->
    Let (x, kind, fold_known_named statics d, fold_known statics body)
  | Let_static (bindings, body) ->
    Let_static
      (map (fold_known_binding statics) bindings, fold_known statics body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, fold_known_handler statics h, fold_known statics body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, fold_known_handler statics h)
          handlers,
        fold_known statics body )
  | _ -> e

(** val fold_known_handler : static_env -> continuation_handler ->
    continuation_handler **)

and fold_known_handler statics = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, fold_known statics handler)

(** val fold_known_binding : static_env -> static_binding -> static_binding **)

and fold_known_binding statics binding =
  match binding with
  | Bind_code (id, c) -> Bind_code (id, fold_known_code statics c)
  | _ -> binding

(** val fold_known_code : static_env -> code -> code **)

and fold_known_code statics = function
  | Code (params, my_closure, ret, exn, metadata, body) ->
    Code (params, my_closure, ret, exn, metadata, fold_known statics body)

(** val binding_bound_as : (symbol * static_const) list -> static_binding ->
    bool **)

let binding_bound_as known = function
  | Bind_symbol (s, const) -> (
    match lookup s known with
    | Some expected ->
      closed_static_const const
      && if static_const_eq_dec const expected then true else false
    | None -> true)
  | _ -> true

(** val bound_as : (symbol * static_const) list -> expr -> bool **)

let rec bound_as known = function
  | Let (_, _, _, body) -> bound_as known body
  | Let_static (bindings, body) ->
    (forallb (binding_bound_as known) bindings
    && forallb (code_of_binding_bound_as known) bindings)
    && bound_as known body
  | Let_cont_non_recursive (_, h, body) ->
    handler_bound_as known h && bound_as known body
  | Let_cont_recursive (handlers, body) ->
    forallb
      (fun pat ->
        let _, h = pat in
        handler_bound_as known h)
      handlers
    && bound_as known body
  | _ -> true

(** val handler_bound_as : (symbol * static_const) list -> continuation_handler
    -> bool **)

and handler_bound_as known = function
  | Handler (_, _, handler) -> bound_as known handler

(** val code_of_binding_bound_as : (symbol * static_const) list ->
    static_binding -> bool **)

and code_of_binding_bound_as known = function
  | Bind_code (_, c) -> code_bound_as known c
  | _ -> true

(** val code_bound_as : (symbol * static_const) list -> code -> bool **)

and code_bound_as known = function
  | Code (_, _, _, _, _, body) -> bound_as known body

(** val fold_known_unit : expr -> expr option **)

let fold_known_unit e =
  let known = known_bindings e in
  if bound_as known e then Some (fold_known (known_statics known) e) else None
