open FlambdaModel
open FlambdaNominalSpec

val let_params : variable list -> simple list -> expr -> expr

val inlined_body : code -> renaming -> apply_expr -> expr
