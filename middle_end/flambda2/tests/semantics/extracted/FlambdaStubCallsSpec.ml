open Datatypes
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

(** val binding_non_stub_code : static_binding -> code_id list **)

let binding_non_stub_code = function
  | Bind_code (id, c) -> if code_is_stub c then [] else id :: []
  | _ -> []

(** val non_stub_code : expr -> code_id list **)

let rec non_stub_code = function
  | Let (_, _, _, body) -> non_stub_code body
  | Let_static (bindings, body) ->
    app (flat_map binding_non_stub_code bindings) (non_stub_code body)
  | Let_cont_non_recursive (_, h, body) ->
    app (handler_non_stub_code h) (non_stub_code body)
  | Let_cont_recursive (handlers, body) ->
    app
      (flat_map
         (fun pat ->
           let _, h = pat in
           handler_non_stub_code h)
         handlers)
      (non_stub_code body)
  | _ -> []

(** val handler_non_stub_code : continuation_handler -> code_id list **)

and handler_non_stub_code = function
  | Handler (_, _, handler) -> non_stub_code handler

(** val demote_call : code_id list -> apply_expr -> apply_expr **)

let demote_call ids ap =
  match ap.ap_call_kind with
  | Direct code0 ->
    if among code0 ids
    then
      { ap_callee = ap.ap_callee;
        ap_call_kind = Indirect;
        ap_args = ap.ap_args;
        ap_continuation = ap.ap_continuation;
        ap_exn_continuation = ap.ap_exn_continuation;
        ap_exn_extra_args = ap.ap_exn_extra_args;
        ap_args_arity = ap.ap_args_arity;
        ap_return_arity = ap.ap_return_arity
      }
    else ap
  | Indirect -> ap

(** val demote_calls : code_id list -> expr -> expr **)

let rec demote_calls ids e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, demote_calls ids body)
  | Let_static (bindings, body) -> Let_static (bindings, demote_calls ids body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, demote_calls_in_handler ids h, demote_calls ids body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, demote_calls_in_handler ids h)
          handlers,
        demote_calls ids body )
  | Apply ap -> Apply (demote_call ids ap)
  | _ -> e

(** val demote_calls_in_handler : code_id list -> continuation_handler ->
    continuation_handler **)

and demote_calls_in_handler ids = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, demote_calls ids handler)

(** val demote_calls_in_code : code_id list -> code -> code **)

let demote_calls_in_code ids = function
  | Code (params, my_closure, ret, exn, metadata, body) ->
    Code (params, my_closure, ret, exn, metadata, demote_calls ids body)

(** val demote_in_stub_binding : code_id list -> static_binding ->
    static_binding **)

let demote_in_stub_binding ids binding =
  match binding with
  | Bind_code (id, c) ->
    if code_is_stub c
    then Bind_code (id, demote_calls_in_code ids c)
    else binding
  | _ -> binding

(** val demote_in_stubs : code_id list -> expr -> expr **)

let rec demote_in_stubs ids e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, demote_in_stubs ids body)
  | Let_static (bindings, body) ->
    Let_static
      (map (demote_in_stub_binding ids) bindings, demote_in_stubs ids body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, demote_in_stubs_of_handler ids h, demote_in_stubs ids body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, demote_in_stubs_of_handler ids h)
          handlers,
        demote_in_stubs ids body )
  | _ -> e

(** val demote_in_stubs_of_handler : code_id list -> continuation_handler ->
    continuation_handler **)

and demote_in_stubs_of_handler ids = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, demote_in_stubs ids handler)

(** val demote_stub_calls : expr -> expr **)

let demote_stub_calls e = demote_in_stubs (non_stub_code e) e
