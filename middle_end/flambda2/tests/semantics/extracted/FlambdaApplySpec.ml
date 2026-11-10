open FlambdaModel
open FlambdaNominalSpec

(** val let_params : variable list -> simple list -> expr -> expr **)

let rec let_params params args body =
  match params with
  | [] -> body
  | param :: params0 -> (
    match args with
    | [] -> body
    | arg :: args0 -> Let (param, Simple arg, let_params params0 args0 body))

(** val inlined_body : code -> renaming -> apply_expr -> expr **)

let inlined_body c r ap =
  Let
    ( code_my_closure c,
      Simple ap.ap_callee,
      let_params (code_params c) ap.ap_args (rename_expr r (code_body c)) )
