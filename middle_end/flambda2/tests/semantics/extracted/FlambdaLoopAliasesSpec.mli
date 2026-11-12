open FlambdaAliasesSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaTypesSpec
open ListDef

val follow_aliases_in_loops : typing_env -> expr -> expr

val follow_aliases_in_loops_in_handler :
  typing_env -> continuation_handler -> continuation_handler

val follow_aliases_in_loop :
  typing_env -> continuation_handler -> continuation_handler
