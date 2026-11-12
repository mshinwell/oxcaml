open FlambdaMeetEnv
open FlambdaTypeGrammar
open FlambdaTypingEnv

type meet_function =
  Typing_env.t ->
  flambda_type ->
  flambda_type ->
  (flambda_type * Typing_env.t) Or_bottom.t option

type add_equation_function =
  Typing_env.t -> name -> flambda_type -> Typing_env.t option

type join_scoped_envs =
  meet_expanded_head ->
  Scope.t ->
  Meet_env.t ->
  Typing_env.t ->
  Typing_env.t list ->
  Meet_env.t option
