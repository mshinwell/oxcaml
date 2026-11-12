open FlambdaBindingTime
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypingEnv

val simplify_simple : Typing_env.t -> simple -> (flambda_type * simple) option

val simplify_simples :
  Typing_env.t -> simple list -> (flambda_type * simple) list option
