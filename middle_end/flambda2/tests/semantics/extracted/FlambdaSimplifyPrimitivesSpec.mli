open FlambdaBindingTime
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypeWellFormedSpec
open FlambdaTypingEnv
open FlambdaTypingEnvInvariantSpec

val simplify_simple : Typing_env.t -> simple -> (flambda_type * simple) option

val simplify_simples :
  Typing_env.t -> simple list -> (flambda_type * simple) list option

val well_formed_input_b : Typing_env.t -> flambda_type -> bool
