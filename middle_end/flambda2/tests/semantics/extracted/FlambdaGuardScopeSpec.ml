open Datatypes
open FlambdaBindersSpec
open FlambdaMapSpec
open FlambdaModel

(** val scope_kept : expr -> expr -> bool **)

let scope_kept e e' =
  (code_closed e'
  && all_among (free_variables_of_expr e') (free_variables_of_expr e))
  && all_among (free_continuations_of_expr e') (free_continuations_of_expr e)

(** val guard_scope : (expr -> expr) -> expr -> expr **)

let guard_scope f e =
  let e' = f e in
  if negb (code_closed e) || scope_kept e e' then e' else e
