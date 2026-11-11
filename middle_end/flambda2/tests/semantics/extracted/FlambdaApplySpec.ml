open FlambdaKindModel
open FlambdaModel
open FlambdaNominalSpec
open List

(** val let_params : variable list -> flambda_kind list -> simple list -> expr
    -> expr **)

let rec let_params params kinds args body =
  match params with
  | [] -> body
  | param :: params0 -> (
    match args with
    | [] -> body
    | arg :: args0 ->
      Let
        ( param,
          hd Value kinds,
          Simple arg,
          let_params params0 (tl kinds) args0 body ))

(** val inlined_body : code -> renaming -> apply_expr -> expr **)

let inlined_body c r ap =
  Let
    ( code_my_closure c,
      Value,
      Simple ap.ap_callee,
      let_params (code_params c) (code_params_kinds c) ap.ap_args
        (rename_expr r (code_body c)) )
