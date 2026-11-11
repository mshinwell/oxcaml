open BinPos
open Datatypes
open FlambdaModel
open List

(** val cont_free_b : continuation -> expr -> bool **)

let rec cont_free_b k = function
  | Let (_, _, _, body) -> cont_free_b k body
  | Let_static (_, body) -> cont_free_b k body
  | Let_cont_non_recursive (bound, h, body) ->
    cont_free_in_handler_b k h || (negb (Pos.eqb k bound) && cont_free_b k body)
  | Let_cont_recursive (handlers, body) ->
    existsb
      (fun pat ->
        let _, h = pat in
        cont_free_in_handler_b k h)
      handlers
    || cont_free_b k body
  | Apply ap -> Pos.eqb k ap.ap_continuation || Pos.eqb k ap.ap_exn_continuation
  | Apply_cont ac -> Pos.eqb k ac.ac_continuation
  | Switch (_, arms) ->
    existsb (fun arm -> Pos.eqb k (snd arm).ac_continuation) arms
  | Invalid -> false

(** val cont_free_in_handler_b : continuation -> continuation_handler -> bool **)

and cont_free_in_handler_b k = function
  | Handler (_, _, handler) -> cont_free_b k handler

(** val remove_unused_conts : expr -> expr **)

let rec remove_unused_conts e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, remove_unused_conts body)
  | Let_static (bindings, body) ->
    Let_static (bindings, remove_unused_conts body)
  | Let_cont_non_recursive (k, h, body) ->
    let body' = remove_unused_conts body in
    if cont_free_b k body'
    then Let_cont_non_recursive (k, remove_unused_conts_in_handler h, body')
    else body'
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, remove_unused_conts body)
  | _ -> e

(** val remove_unused_conts_in_handler : continuation_handler ->
    continuation_handler **)

and remove_unused_conts_in_handler = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, remove_unused_conts handler)
