open Datatypes
open FlambdaJoinEnv
open FlambdaJoinTypes
open FlambdaTypeEqualSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv

val n_way_join_of_types :
  Join_env.parameters ->
  nat ->
  (Typing_env.t -> flambda_type -> Expanded_type.t option) ->
  (Typing_env.t ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate Or_bottom.t) ->
  nat ->
  Join_env.n_way_join_type
