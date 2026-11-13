open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaNormaliseSpec

(** val merge_alias_lets : expr -> expr **)

let rec merge_alias_lets e =
  match e with
  | Let (x, kind, d, body) -> (
    match merge_alias_lets body with
    | Let (y, kind', defining_expr, body') -> (
      match defining_expr with
      | Simple s -> (
        match s with
        | Var x' ->
          if (Pos.eqb x' x && kind_eqb kind' kind) && negb (var_free_b x body')
          then Let (y, kind, d, body')
          else Let (x, kind, d, Let (y, kind', Simple (Var x'), body'))
        | x0 -> Let (x, kind, d, Let (y, kind', Simple x0, body')))
      | x0 -> Let (x, kind, d, Let (y, kind', x0, body')))
    | x0 -> Let (x, kind, d, x0))
  | Let_static (bindings, body) -> Let_static (bindings, merge_alias_lets body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler (params, metadata, merge_alias_lets handler),
        merge_alias_lets body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, merge_alias_lets body)
  | _ -> e
