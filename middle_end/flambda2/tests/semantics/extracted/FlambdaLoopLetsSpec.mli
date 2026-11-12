open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open ListDef

val remove_unused_defined_lets_in_loops : kinds_in_scope -> expr -> expr

val remove_unused_defined_lets_in_handler :
  kinds_in_scope -> continuation_handler -> continuation_handler
