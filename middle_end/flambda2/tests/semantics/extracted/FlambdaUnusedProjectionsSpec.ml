open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open List

type known_sets =
  (variable * (function_slot * (function_slot * code_id) list)) list

(** val forget_set : variable -> known_sets -> known_sets **)

let forget_set x known =
  filter (fun entry -> negb (Pos.eqb x (fst entry))) known

(** val forget_sets : variable list -> known_sets -> known_sets **)

let rec forget_sets xs known =
  match xs with [] -> known | x :: xs0 -> forget_sets xs0 (forget_set x known)

(** val sets_under_let : known_sets -> variable -> named -> known_sets **)

let sets_under_let known x d =
  let known0 = forget_set x known in
  match d with
  | Closure_of_set (slot, function_decls, _) ->
    (x, (slot, function_decls)) :: known0
  | _ -> known0

(** val projection_defined : known_sets -> named -> bool **)

let projection_defined known = function
  | Project_function_slot (move_from, move_to, closure0) -> (
    match closure0 with
    | Var closure -> (
      match lookup closure known with
      | Some p ->
        let slot, function_decls = p in
        (Pos.eqb slot move_from && is_bound move_from function_decls)
        && is_bound move_to function_decls
      | None -> false)
    | _ -> false)
  | _ -> false

(** val remove_projections_knowing : known_sets -> expr -> expr **)

let rec remove_projections_knowing known e =
  match e with
  | Let (x, kind, d, body) ->
    let body' = remove_projections_knowing (sets_under_let known x d) body in
    if
      (kind_eqb kind Value && projection_defined known d)
      && negb (var_free_b x body')
    then body'
    else Let (x, kind, d, body')
  | Let_static (bindings, body) ->
    Let_static (bindings, remove_projections_knowing known body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler
          ( params,
            metadata,
            remove_projections_knowing (forget_sets params known) handler ),
        remove_projections_knowing known body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, remove_projections_knowing known body)
  | _ -> e

(** val remove_unused_projections : expr -> expr **)

let remove_unused_projections e = remove_projections_knowing [] e
