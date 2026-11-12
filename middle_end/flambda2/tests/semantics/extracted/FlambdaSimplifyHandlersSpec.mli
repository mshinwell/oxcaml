open Datatypes
open FlambdaModel
open FlambdaSimplifyCodeEnvSpec
open FlambdaTypingEnv
open List
open PeanoNat

val handler_env :
  Typing_env.t -> variable list -> handler_metadata -> Typing_env.t option
