open Datatypes
open FlambdaExpandHead
open FlambdaJoinEnv
open FlambdaJoinEnvSpec
open FlambdaJoinSpec
open FlambdaJoinTypes
open FlambdaJoinTypesWithEnvSpec
open FlambdaMeet
open FlambdaMeetEnv
open FlambdaMeetSpec
open FlambdaNameAbstractionSpec
open FlambdaTypeEqualSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv

val meet_env_functions :
  (Meet_env.t, meet_expanded_head) Join_env.meet_env_functions

val join_parameters : nat -> Join_env.parameters

val join_expanded : FlambdaExpandHead.Expanded_type.t -> Expanded_type.t

val expand_head_for_join :
  Typing_env.t -> flambda_type -> Expanded_type.t option

type fuels =
  { fuel_of_env : nat;
    fuel_of_types : nat;
    fuel_of_meet : nat
  }

val model_join_of_types : nat -> fuels -> Join_env.n_way_join_type

val model_join_scoped_envs :
  Join_env.choices -> nat -> fuels -> join_scoped_envs

val model_meet_expanded_head :
  Join_env.choices -> meet_choices -> nat -> fuels -> meet_expanded_head

val model_meet :
  Join_env.choices -> meet_choices -> nat -> fuels -> meet_function

val model_add_equation :
  Join_env.choices -> meet_choices -> nat -> fuels -> add_equation_function

val model_join :
  Join_env.choices -> meet_choices -> nat -> fuels -> 'a1 join_of_environments
