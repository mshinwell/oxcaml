open BinPos
open Datatypes
open FlambdaCseSpec
open FlambdaModel
open FlambdaNormaliseSpec
open List

(** val is_projection : named -> bool **)

let is_projection = function
  | Project_value_slot (_, _) -> true
  | Project_value_slot_from (_, _, _) -> true
  | _ -> false

(** val projected_from : named -> simple list **)

let projected_from = function
  | Project_value_slot (_, closure) -> closure :: []
  | Project_value_slot_from (_, _, closure) -> closure :: []
  | _ -> []

type projected = (variable * named) list

(** val forget_projected : variable -> projected -> projected **)

let forget_projected x known =
  filter
    (fun entry ->
      negb (Pos.eqb x (fst entry))
      && negb (var_in_simples x (projected_from (snd entry))))
    known

(** val forget_projected_vars : variable list -> projected -> projected **)

let rec forget_projected_vars xs known =
  match xs with
  | [] -> known
  | x :: xs0 -> forget_projected_vars xs0 (forget_projected x known)

(** val projected_under_let : projected -> variable -> named -> projected **)

let projected_under_let known x d =
  let known0 = forget_projected x known in
  if is_projection d && negb (var_in_simples x (projected_from d))
  then (x, d) :: known0
  else known0

(** val same_projection : named -> named -> bool **)

let same_projection d d' =
  match d with
  | Project_value_slot (slot, closure) -> (
    match d' with
    | Project_value_slot (slot', closure') ->
      Pos.eqb slot slot' && same_simples (closure :: []) (closure' :: [])
    | _ -> false)
  | Project_value_slot_from (project_from, slot, closure) -> (
    match d' with
    | Project_value_slot_from (project_from', slot', closure') ->
      (Pos.eqb project_from project_from' && Pos.eqb slot slot')
      && same_simples (closure :: []) (closure' :: [])
    | _ -> false)
  | _ -> false

(** val projected_by : projected -> named -> variable option **)

let rec projected_by known d =
  match known with
  | [] -> None
  | p :: known0 ->
    let x, d' = p in
    if same_projection d d' then Some x else projected_by known0 d

(** val share_projection : projected -> named -> named **)

let share_projection known d =
  match projected_by known d with Some x -> Simple (Var x) | None -> d

(** val share_projections_knowing : projected -> expr -> expr **)

let rec share_projections_knowing known e =
  match e with
  | Let (x, kind, d, body) ->
    Let
      ( x,
        kind,
        share_projection known d,
        share_projections_knowing (projected_under_let known x d) body )
  | Let_static (bindings, body) ->
    Let_static (bindings, share_projections_knowing known body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        share_projections_in_handler known h,
        share_projections_knowing known body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, share_projections_knowing known body)
  | _ -> e

(** val share_projections_in_handler : projected -> continuation_handler ->
    continuation_handler **)

and share_projections_in_handler known = function
  | Handler (params, metadata, handler) ->
    Handler
      ( params,
        metadata,
        share_projections_knowing (forget_projected_vars params known) handler
      )

(** val share_known_projections : expr -> expr **)

let share_known_projections e = share_projections_knowing [] e
