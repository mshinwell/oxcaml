open Datatypes
open FlambdaModel
open FlambdaUnusedHeadStaticsSpec
open FlambdaValidateSpec
open FlambdaValueSpec

val holds_from : static_env -> nat -> code_id list -> expr -> validation -> bool
