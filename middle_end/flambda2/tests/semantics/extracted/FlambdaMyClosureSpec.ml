open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

(** val bind_my_closures : (code_id * symbol) list -> expr -> expr **)

let rec bind_my_closures known e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, bind_my_closures known body)
  | Let_static (bindings, body) ->
    Let_static
      ( map (bind_my_closures_in_binding known) bindings,
        bind_my_closures known body )
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, bind_my_closures_in_handler known h, bind_my_closures known body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, bind_my_closures_in_handler known h)
          handlers,
        bind_my_closures known body )
  | _ -> e

(** val bind_my_closures_in_handler : (code_id * symbol) list ->
    continuation_handler -> continuation_handler **)

and bind_my_closures_in_handler known = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, bind_my_closures known handler)

(** val bind_my_closures_in_binding : (code_id * symbol) list -> static_binding
    -> static_binding **)

and bind_my_closures_in_binding known binding =
  match binding with
  | Bind_code (id, c) -> Bind_code (id, bind_my_closure known id c)
  | _ -> binding

(** val bind_my_closure : (code_id * symbol) list -> code_id -> code -> code **)

and bind_my_closure known id = function
  | Code (params, my_closure, ret, exn, metadata, body) -> (
    let body0 = bind_my_closures known body in
    match lookup id known with
    | Some s ->
      if among my_closure params
      then Code (params, my_closure, ret, exn, metadata, body0)
      else
        Code
          ( params,
            my_closure,
            ret,
            exn,
            metadata,
            Let (my_closure, Value, Simple (Symbol s), body0) )
    | None -> Code (params, my_closure, ret, exn, metadata, body0))

(** val named_makes_no_closure_of : code_id -> named -> bool **)

let named_makes_no_closure_of id = function
  | Set_of_closures (code0, _) -> negb (Pos.eqb code0 id)
  | Closure_of_set (_, function_decls, _) ->
    negb (among id (map snd function_decls))
  | _ -> true

(** val static_closure_of_is : code_id -> symbol -> symbol -> static_const ->
    bool **)

let static_closure_of_is id s sym = function
  | Static_const_set_of_closures (code0, _) ->
    negb (Pos.eqb code0 id) || Pos.eqb sym s
  | Static_const_closure_of_set (slot, _, function_decls, _) -> (
    match lookup slot function_decls with
    | Some code0 -> negb (Pos.eqb code0 id) || Pos.eqb sym s
    | None -> true)
  | _ -> true

(** val only_closure_of : code_id -> symbol -> expr -> bool **)

let rec only_closure_of id s = function
  | Let (_, _, d, body) ->
    named_makes_no_closure_of id d && only_closure_of id s body
  | Let_static (bindings, body) ->
    forallb (binding_only_closure_of id s) bindings && only_closure_of id s body
  | Let_cont_non_recursive (_, h, body) ->
    handler_only_closure_of id s h && only_closure_of id s body
  | Let_cont_recursive (handlers, body) ->
    forallb
      (fun pat ->
        let _, h = pat in
        handler_only_closure_of id s h)
      handlers
    && only_closure_of id s body
  | _ -> true

(** val handler_only_closure_of : code_id -> symbol -> continuation_handler ->
    bool **)

and handler_only_closure_of id s = function
  | Handler (_, _, handler) -> only_closure_of id s handler

(** val binding_only_closure_of : code_id -> symbol -> static_binding -> bool **)

and binding_only_closure_of id s = function
  | Bind_code (_, c) -> code_only_closure_of id s c
  | Bind_deleted_code _ -> true
  | Bind_symbol (sym, const) -> static_closure_of_is id s sym const

(** val code_only_closure_of : code_id -> symbol -> code -> bool **)

and code_only_closure_of id s = function
  | Code (_, _, _, _, _, body) -> only_closure_of id s body

(** val only_closures_of : (code_id * symbol) list -> expr -> bool **)

let only_closures_of known e =
  forallb
    (fun pat ->
      let id, s = pat in
      only_closure_of id s e)
    known
