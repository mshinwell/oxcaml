open BinPos
open FlambdaModel

type flambda_type =
  | Unknown
  | Bottom
  | Equals of simple
  | Closure_of of code_id * (value_slot * simple) list

type typing_env = (variable * flambda_type) list

val find_alias : typing_env -> variable -> simple option

val canonical_simple : typing_env -> simple -> simple
