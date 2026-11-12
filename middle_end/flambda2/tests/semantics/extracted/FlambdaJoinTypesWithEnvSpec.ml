open Datatypes
open FlambdaJoinEnv
open FlambdaJoinTypes
open FlambdaTypeEqualSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv

(** val n_way_join_of_types : Join_env.parameters -> nat -> (Typing_env.t ->
    flambda_type -> Expanded_type.t option) -> (Typing_env.t ->
    head_of_kind_naked_immediate -> head_of_kind_naked_immediate Or_bottom.t) ->
    nat -> Join_env.n_way_join_type **)

let n_way_join_of_types p fuel_of_env expand_head
    reduce_head_of_kind_naked_immediate fuel =
  n_way_join Join_env.joined_env
    (Join_env.n_way_join_simples p fuel_of_env)
    (Join_env.import_type p fuel_of_env)
    (Join_env.n_way_join_env_extension p fuel_of_env)
    expand_head reduce_head_of_kind_naked_immediate type_eqb block_shape_eqb
    fuel
