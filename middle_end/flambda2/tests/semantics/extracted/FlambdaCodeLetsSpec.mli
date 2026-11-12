open FlambdaKindModel
open FlambdaLoopLetsSpec
open FlambdaModel
open FlambdaNormaliseSpec
open ListDef

val code_in_scope : variable list -> variable -> code_metadata -> kinds_in_scope

val remove_unused_defined_lets_in_binding : static_binding -> static_binding

val remove_unused_defined_lets_in_code : expr -> expr

val remove_unused_defined_lets_in_code_handler :
  continuation_handler -> continuation_handler
