open FlambdaBindingTime
open FlambdaKindModel
open FlambdaModel
open FlambdaProvers
open FlambdaTypeGrammar
open FlambdaTypingEnv

val simplify_project_value_slot :
  Typing_env.t -> flambda_kind -> value_slot -> flambda_type -> simple option
