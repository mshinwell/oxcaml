open Datatypes
open FlambdaModel
open FlambdaSimplifyCodeEnvSpec
open FlambdaTypingEnv
open List
open PeanoNat

(** val handler_env : Typing_env.t -> variable list -> handler_metadata ->
    Typing_env.t option **)

let handler_env tenv params metadata =
  let kinds = metadata.hm_params_kinds in
  if Nat.eqb (length kinds) (length params)
  then define_variables_checked tenv (combine params kinds)
  else None
