open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUntagParamsSpec
open List
open ListDef

(** val shadow_lets : nat list -> nat -> variable list -> flambda_kind list ->
    expr -> expr **)

let rec shadow_lets us i params kinds e =
  match params with
  | [] -> e
  | p :: params0 -> (
    match kinds with
    | [] -> e
    | kind :: kinds0 ->
      if at_position us i
      then Let (p, kind, Simple (Var p), shadow_lets us (S i) params0 kinds0 e)
      else shadow_lets us (S i) params0 kinds0 e)

(** val shadow_expr : positions -> expr -> expr **)

let rec shadow_expr sites e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, shadow_expr sites body)
  | Let_static (bindings, body) -> Let_static (bindings, shadow_expr sites body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      (k, shadow_handler sites (positions_of sites k) h, shadow_expr sites body)
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, shadow_handler sites (positions_of sites k) h)
          handlers,
        shadow_expr sites body )
  | _ -> e

(** val shadow_handler : positions -> nat list -> continuation_handler ->
    continuation_handler **)

and shadow_handler sites us = function
  | Handler (params, metadata, handler) ->
    Handler
      ( params,
        metadata,
        if distinct params
        then
          shadow_lets us O params metadata.hm_params_kinds
            (shadow_expr sites handler)
        else shadow_expr sites handler )

(** val handlers_of : expr -> (continuation * continuation_handler) list **)

let rec handlers_of = function
  | Let (_, _, _, body) -> handlers_of body
  | Let_static (_, body) -> handlers_of body
  | Let_cont_non_recursive (k, h, body) ->
    (k, h) :: app (handlers_in_handler h) (handlers_of body)
  | Let_cont_recursive (handlers, body) ->
    app
      (flat_map
         (fun pat ->
           let k, h = pat in
           (k, h) :: handlers_in_handler h)
         handlers)
      (handlers_of body)
  | _ -> []

(** val handlers_in_handler : continuation_handler -> (continuation *
    continuation_handler) list **)

and handlers_in_handler = function
  | Handler (_, _, handler) -> handlers_of handler

(** val untagged_in : variable -> expr -> bool **)

let rec untagged_in p = function
  | Let (_, _, d, body) ->
    (match untag_of d with Some q -> Pos.eqb q p | None -> false)
    || untagged_in p body
  | Let_static (_, body) -> untagged_in p body
  | Let_cont_non_recursive (_, h, body) ->
    untagged_in_handler p h || untagged_in p body
  | Let_cont_recursive (handlers, body) ->
    existsb
      (fun pat ->
        let _, h = pat in
        untagged_in_handler p h)
      handlers
    || untagged_in p body
  | _ -> false

(** val untagged_in_handler : variable -> continuation_handler -> bool **)

and untagged_in_handler p = function
  | Handler (_, _, handler) -> untagged_in p handler

(** val gives_needed : positions -> variable -> apply_cont -> bool **)

let gives_needed needed p ac =
  var_in_simples p
    (moved_from (positions_of needed ac.ac_continuation) O ac.ac_args)

(** val given_needed : positions -> variable -> expr -> bool **)

let rec given_needed needed p = function
  | Let (_, _, _, body) -> given_needed needed p body
  | Let_static (_, body) -> given_needed needed p body
  | Let_cont_non_recursive (_, h, body) ->
    given_needed_in_handler needed p h || given_needed needed p body
  | Let_cont_recursive (handlers, body) ->
    existsb
      (fun pat ->
        let _, h = pat in
        given_needed_in_handler needed p h)
      handlers
    || given_needed needed p body
  | Apply_cont ac -> gives_needed needed p ac
  | Switch (_, arms) ->
    existsb
      (fun pat ->
        let _, ac = pat in
        gives_needed needed p ac)
      arms
  | _ -> false

(** val given_needed_in_handler : positions -> variable -> continuation_handler
    -> bool **)

and given_needed_in_handler needed p = function
  | Handler (_, _, handler) -> given_needed needed p handler

(** val needed_from : positions -> nat -> variable list -> flambda_kind list ->
    expr -> nat list **)

let rec needed_from needed i params kinds handler =
  match params with
  | [] -> []
  | p :: params0 -> (
    match kinds with
    | [] -> []
    | kind :: kinds0 ->
      if
        kind_eqb kind Value
        && (untagged_in p handler || given_needed needed p handler)
      then i :: needed_from needed (S i) params0 kinds0 handler
      else needed_from needed (S i) params0 kinds0 handler)

(** val needed_of : positions -> continuation_handler -> nat list **)

let needed_of needed = function
  | Handler (params, metadata, handler) ->
    if metadata.hm_is_exn_handler
    then []
    else needed_from needed O params metadata.hm_params_kinds handler

(** val needed_round : (continuation * continuation_handler) list -> positions
    -> positions **)

let needed_round hs needed =
  map
    (fun pat ->
      let k, h = pat in
      k, needed_of needed h)
    hs

(** val needed_positions : nat -> (continuation * continuation_handler) list ->
    positions -> positions **)

let rec needed_positions rounds hs needed =
  match rounds with
  | O -> needed
  | S rounds0 -> needed_positions rounds0 hs (needed_round hs needed)

(** val shadow_positions : expr -> positions **)

let shadow_positions e =
  needed_positions (S (S (S (S (S (S O)))))) (handlers_of e) []

(** val shadow_params : expr -> expr **)

let shadow_params e =
  match count_positions (shadow_positions e) with
  | O -> e
  | S _ -> shadow_expr (shadow_positions e) e
