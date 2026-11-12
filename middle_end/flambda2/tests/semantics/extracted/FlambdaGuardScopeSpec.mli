open Datatypes
open FlambdaBindersSpec
open FlambdaMapSpec
open FlambdaModel

val scope_kept : expr -> expr -> bool

val guard_scope : (expr -> expr) -> expr -> expr
