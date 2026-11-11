open BinNums
open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

(** val free_continuations : expr -> continuation list **)

let rec free_continuations = function
  | Let (_, _, body) -> free_continuations body
  | Let_static (_, body) -> free_continuations body
  | Let_cont_non_recursive (k, h, body) ->
    app
      (handler_free_continuations h)
      (without (k :: []) (free_continuations body))
  | Let_cont_recursive (handlers, body) ->
    without (map fst handlers)
      (app
         (flat_map
            (fun pat ->
              let _, h = pat in
              handler_free_continuations h)
            handlers)
         (free_continuations body))
  | Apply ap -> [ap.ap_continuation; ap.ap_exn_continuation]
  | Apply_cont ac -> ac.ac_continuation :: []
  | Switch (_, arms) -> map (fun arm -> (snd arm).ac_continuation) arms
  | Invalid -> []

(** val handler_free_continuations : continuation_handler -> continuation list **)

and handler_free_continuations = function
  | Handler (_, handler) -> free_continuations handler

(** val raises_to : continuation -> expr -> bool **)

let rec raises_to k = function
  | Let (_, _, body) -> raises_to k body
  | Let_static (_, body) -> raises_to k body
  | Let_cont_non_recursive (_, h, body) ->
    handler_raises_to k h || raises_to k body
  | Let_cont_recursive (handlers, body) ->
    existsb
      (fun pat ->
        let _, h = pat in
        handler_raises_to k h)
      handlers
    || raises_to k body
  | Apply ap -> Pos.eqb k ap.ap_exn_continuation
  | _ -> false

(** val handler_raises_to : continuation -> continuation_handler -> bool **)

and handler_raises_to k = function Handler (_, handler) -> raises_to k handler

(** val handler_at_toplevel : continuation -> continuation -> expr -> bool **)

let handler_at_toplevel unit_exn k body =
  negb (raises_to k body) && all_among (free_continuations body) [k; unit_exn]

(** val statics_at_toplevel : continuation -> bool -> expr -> bool **)

let rec statics_at_toplevel unit_exn toplevel = function
  | Let (_, _, body) -> statics_at_toplevel unit_exn toplevel body
  | Let_static (bindings, body) ->
    (toplevel && forallb (binding_statics_at_toplevel unit_exn) bindings)
    && statics_at_toplevel unit_exn toplevel body
  | Let_cont_non_recursive (k, h, body) ->
    handler_statics_at_toplevel unit_exn
      (toplevel && handler_at_toplevel unit_exn k body)
      h
    && statics_at_toplevel unit_exn toplevel body
  | Let_cont_recursive (handlers, body) ->
    forallb
      (fun pat ->
        let _, h = pat in
        handler_statics_at_toplevel unit_exn false h)
      handlers
    && statics_at_toplevel unit_exn toplevel body
  | _ -> true

(** val handler_statics_at_toplevel : continuation -> bool ->
    continuation_handler -> bool **)

and handler_statics_at_toplevel unit_exn toplevel = function
  | Handler (_, handler) -> statics_at_toplevel unit_exn toplevel handler

(** val binding_statics_at_toplevel : continuation -> static_binding -> bool **)

and binding_statics_at_toplevel unit_exn = function
  | Bind_code (_, c) -> code_statics_at_toplevel unit_exn c
  | _ -> true

(** val code_statics_at_toplevel : continuation -> code -> bool **)

and code_statics_at_toplevel unit_exn = function
  | Code (_, _, _, _, body) -> statics_at_toplevel unit_exn false body

(** val code_ids_of_binding : static_binding -> code_id list **)

let code_ids_of_binding = function Bind_code (id, _) -> id :: [] | _ -> []

(** val symbols_of_binding : static_binding -> symbol list **)

let symbols_of_binding = function Bind_symbol (s, _) -> s :: [] | _ -> []

(** val static_names : (static_binding -> positive list) -> expr -> positive
    list **)

let rec static_names names_of = function
  | Let (_, _, body) -> static_names names_of body
  | Let_static (bindings, body) ->
    app (flat_map names_of bindings) (static_names names_of body)
  | Let_cont_non_recursive (_, h, body) ->
    app (handler_static_names names_of h) (static_names names_of body)
  | Let_cont_recursive (handlers, body) ->
    app
      (flat_map
         (fun pat ->
           let _, h = pat in
           handler_static_names names_of h)
         handlers)
      (static_names names_of body)
  | _ -> []

(** val handler_static_names : (static_binding -> positive list) ->
    continuation_handler -> positive list **)

and handler_static_names names_of = function
  | Handler (_, handler) -> static_names names_of handler

(** val well_formed_unit : continuation -> expr -> bool **)

let well_formed_unit unit_exn e =
  (statics_at_toplevel unit_exn true e
  && distinct (static_names code_ids_of_binding e))
  && distinct (static_names symbols_of_binding e)
