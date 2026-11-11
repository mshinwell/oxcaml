open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

(** val free_variables_of_simple : simple -> variable list **)

let free_variables_of_simple = function Var x -> x :: [] | _ -> []

(** val free_variables_of_simples : simple list -> variable list **)

let free_variables_of_simples args = flat_map free_variables_of_simple args

(** val free_variables_of_value_slots : (value_slot * simple) list -> variable
    list **)

let free_variables_of_value_slots value_slots =
  flat_map (fun slot -> free_variables_of_simple (snd slot)) value_slots

(** val free_variables_of_named : named -> variable list **)

let free_variables_of_named = function
  | Simple s -> free_variables_of_simple s
  | Prim (_, args) -> free_variables_of_simples args
  | Set_of_closures (_, value_slots) ->
    free_variables_of_value_slots value_slots
  | Closure_of_set (_, _, value_slots) ->
    free_variables_of_value_slots value_slots
  | Project_value_slot (_, closure) -> free_variables_of_simple closure
  | Project_value_slot_from (_, _, closure) -> free_variables_of_simple closure
  | Project_function_slot (_, _, closure) -> free_variables_of_simple closure

(** val free_variables_of_static_const : static_const -> variable list **)

let free_variables_of_static_const = function
  | Static_const_set_of_closures (_, value_slots) ->
    free_variables_of_value_slots value_slots
  | Static_const_closure_of_set (_, _, _, value_slots) ->
    free_variables_of_value_slots value_slots
  | Static_const_block (_, fields) -> free_variables_of_simples fields
  | Static_const_boxed_number contents -> free_variables_of_simple contents
  | Static_const_immutable_string _ -> []

(** val free_variables_of_apply_cont : apply_cont -> variable list **)

let free_variables_of_apply_cont ac = free_variables_of_simples ac.ac_args

(** val free_variables_of_apply : apply_expr -> variable list **)

let free_variables_of_apply ap =
  app
    (free_variables_of_simple ap.ap_callee)
    (free_variables_of_simples ap.ap_args)

(** val free_variables_of_expr : expr -> variable list **)

let rec free_variables_of_expr = function
  | Let (x, _, defining_expr, body) ->
    app
      (free_variables_of_named defining_expr)
      (without (x :: []) (free_variables_of_expr body))
  | Let_static (bindings, body) ->
    app
      (flat_map free_variables_of_binding bindings)
      (free_variables_of_expr body)
  | Let_cont_non_recursive (_, h, body) ->
    app (free_variables_of_handler h) (free_variables_of_expr body)
  | Let_cont_recursive (handlers, body) ->
    app
      (flat_map
         (fun pat ->
           let _, h = pat in
           free_variables_of_handler h)
         handlers)
      (free_variables_of_expr body)
  | Apply ap -> free_variables_of_apply ap
  | Apply_cont ac -> free_variables_of_apply_cont ac
  | Switch (scrutinee, arms) ->
    app
      (free_variables_of_simple scrutinee)
      (flat_map (fun arm -> free_variables_of_apply_cont (snd arm)) arms)
  | Invalid -> []

(** val free_variables_of_handler : continuation_handler -> variable list **)

and free_variables_of_handler = function
  | Handler (params, _, handler) ->
    without params (free_variables_of_expr handler)

(** val free_variables_of_binding : static_binding -> variable list **)

and free_variables_of_binding = function
  | Bind_code (_, c) -> free_variables_of_code c
  | Bind_deleted_code _ -> []
  | Bind_symbol (_, const) -> free_variables_of_static_const const

(** val free_variables_of_code : code -> variable list **)

and free_variables_of_code = function
  | Code (params, my_closure, _, _, _, body) ->
    without (my_closure :: params) (free_variables_of_expr body)

(** val free_continuations_of_expr : expr -> continuation list **)

let rec free_continuations_of_expr = function
  | Let (_, _, _, body) -> free_continuations_of_expr body
  | Let_static (bindings, body) ->
    app
      (flat_map free_continuations_of_binding bindings)
      (free_continuations_of_expr body)
  | Let_cont_non_recursive (k, h, body) ->
    app
      (free_continuations_of_handler h)
      (without (k :: []) (free_continuations_of_expr body))
  | Let_cont_recursive (handlers, body) ->
    without (map fst handlers)
      (app
         (flat_map
            (fun pat ->
              let _, h = pat in
              free_continuations_of_handler h)
            handlers)
         (free_continuations_of_expr body))
  | Apply ap -> [ap.ap_continuation; ap.ap_exn_continuation]
  | Apply_cont ac -> ac.ac_continuation :: []
  | Switch (_, arms) -> map (fun arm -> (snd arm).ac_continuation) arms
  | Invalid -> []

(** val free_continuations_of_handler : continuation_handler -> continuation
    list **)

and free_continuations_of_handler = function
  | Handler (_, _, handler) -> free_continuations_of_expr handler

(** val free_continuations_of_binding : static_binding -> continuation list **)

and free_continuations_of_binding = function
  | Bind_code (_, c) -> free_continuations_of_code c
  | _ -> []

(** val free_continuations_of_code : code -> continuation list **)

and free_continuations_of_code = function
  | Code (_, _, return_continuation, exn_continuation, _, body) ->
    without
      [return_continuation; exn_continuation]
      (free_continuations_of_expr body)

(** val names_among : variable list -> continuation list -> expr -> bool **)

let names_among vs ks e =
  all_among (free_variables_of_expr e) vs
  && all_among (free_continuations_of_expr e) ks

(** val names_in_scope : continuation -> continuation -> expr -> bool **)

let names_in_scope unit_return unit_exn e =
  names_among [] [unit_return; unit_exn] e

(** val binders_distinct : expr -> bool **)

let rec binders_distinct = function
  | Let (_, _, _, body) -> binders_distinct body
  | Let_static (bindings, body) ->
    forallb binding_binders_distinct bindings && binders_distinct body
  | Let_cont_non_recursive (_, h, body) ->
    handler_binders_distinct h && binders_distinct body
  | Let_cont_recursive (handlers, body) ->
    ((negb (Keyed.is_empty handlers) && distinct (map fst handlers))
    && forallb
         (fun pat ->
           let _, h = pat in
           handler_binders_distinct h)
         handlers)
    && binders_distinct body
  | _ -> true

(** val handler_binders_distinct : continuation_handler -> bool **)

and handler_binders_distinct = function
  | Handler (params, _, handler) -> distinct params && binders_distinct handler

(** val binding_binders_distinct : static_binding -> bool **)

and binding_binders_distinct = function
  | Bind_code (_, c) -> code_binders_distinct c
  | _ -> true

(** val code_binders_distinct : code -> bool **)

and code_binders_distinct = function
  | Code (params, my_closure, return_continuation, exn_continuation, _, body) ->
    (distinct (my_closure :: params)
    && negb (Pos.eqb return_continuation exn_continuation))
    && binders_distinct body

(** val code_closed : expr -> bool **)

let rec code_closed = function
  | Let (_, _, _, body) -> code_closed body
  | Let_static (bindings, body) ->
    forallb binding_code_closed bindings && code_closed body
  | Let_cont_non_recursive (_, h, body) ->
    handler_code_closed h && code_closed body
  | Let_cont_recursive (handlers, body) ->
    forallb
      (fun pat ->
        let _, h = pat in
        handler_code_closed h)
      handlers
    && code_closed body
  | _ -> true

(** val handler_code_closed : continuation_handler -> bool **)

and handler_code_closed = function
  | Handler (_, _, handler) -> code_closed handler

(** val binding_code_closed : static_binding -> bool **)

and binding_code_closed = function
  | Bind_code (_, c) -> code_is_closed c
  | _ -> true

(** val code_is_closed : code -> bool **)

and code_is_closed c =
  match c with
  | Code (_, _, _, _, _, body) ->
    (Keyed.is_empty (free_variables_of_code c)
    && Keyed.is_empty (free_continuations_of_code c))
    && code_closed body
