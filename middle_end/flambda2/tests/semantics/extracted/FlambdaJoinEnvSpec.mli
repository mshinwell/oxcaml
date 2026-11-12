open Datatypes
open FlambdaJoinEnv
open FlambdaJoinSpec

val join_with :
  Join_env.choices ->
  ('a2, 'a3) Join_env.meet_env_functions ->
  Join_env.parameters ->
  nat ->
  Join_env.n_way_join_type ->
  'a3 ->
  'a1 join_of_environments
