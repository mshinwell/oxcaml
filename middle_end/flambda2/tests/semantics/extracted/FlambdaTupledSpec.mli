open BinInt
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaNominalSpec
open FlambdaPrimitiveModel
open FlambdaSemanticsSpec

val let_tuple_fields : variable list -> nat -> nat -> simple -> expr -> expr

val inlined_tupled_body : code -> renaming -> apply_expr -> simple -> expr

val inlined_tupled_call : code -> renaming -> apply_expr -> expr
