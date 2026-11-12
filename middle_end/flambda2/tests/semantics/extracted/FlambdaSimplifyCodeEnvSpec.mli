open Datatypes
open FlambdaBindingTime
open FlambdaKindModel
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypingEnv
open FlambdaTypingEnvInvariantSpec
open List
open PeanoNat

val define_variables_checked :
  Typing_env.t -> (variable * flambda_kind) list -> Typing_env.t option

val code_env_in :
  Typing_env.t ->
  variable list ->
  variable ->
  code_metadata ->
  Typing_env.t option
