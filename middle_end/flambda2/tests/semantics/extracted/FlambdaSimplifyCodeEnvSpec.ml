open Datatypes
open FlambdaBindingTime
open FlambdaKindModel
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypingEnv
open FlambdaTypingEnvInvariantSpec
open List
open PeanoNat

(** val define_variables_checked : Typing_env.t -> (variable * flambda_kind)
    list -> Typing_env.t option **)

let rec define_variables_checked tenv = function
  | [] -> Some tenv
  | p :: definitions0 ->
    let x, kind = p in
    if
      typing_env_well_formed tenv
      && negb (Typing_env.mem None tenv (Name_var x))
    then
      define_variables_checked
        (Typing_env.add_variable_definition tenv x kind Name_mode.normal)
        definitions0
    else None

(** val code_env_in : Typing_env.t -> variable list -> variable -> code_metadata
    -> Typing_env.t option **)

let code_env_in tenv params my_closure metadata =
  let kinds = unarize metadata.cm_params_arity in
  if Nat.eqb (length kinds) (length params)
  then
    define_variables_checked
      (Typing_env.closure_env tenv)
      ((my_closure, Value) :: combine params kinds)
  else None
