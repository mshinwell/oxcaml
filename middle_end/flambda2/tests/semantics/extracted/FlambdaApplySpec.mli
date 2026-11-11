open FlambdaKindModel
open FlambdaModel
open FlambdaNominalSpec
open List

val let_params :
  variable list -> flambda_kind list -> simple list -> expr -> expr

val inlined_body : code -> renaming -> apply_expr -> expr
