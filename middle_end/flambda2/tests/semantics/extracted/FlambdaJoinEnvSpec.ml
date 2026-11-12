open Datatypes
open FlambdaJoinEnv
open FlambdaJoinSpec

(** val join_with : Join_env.choices -> ('a2, 'a3) Join_env.meet_env_functions
    -> Join_env.parameters -> nat -> Join_env.n_way_join_type -> 'a3 -> 'a1
    join_of_environments **)

let join_with choices0 ops p fuel n_way_join_type0 meet_expanded_head_fn avoid
    inputs =
  cut_and_n_way_join_with_analysis ops p fuel choices0 n_way_join_type0
    meet_expanded_head_fn avoid inputs.cut_after inputs.source inputs.uses
