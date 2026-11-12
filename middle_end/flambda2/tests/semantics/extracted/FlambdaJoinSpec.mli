open FlambdaJoinEnv
open FlambdaModel
open FlambdaTypingEnv

type 'a join_inputs =
  { source : Typing_env.t;
    cut_after : Scope.t;
    uses : ('a * Typing_env.t) list
  }

type 'a join_of_environments =
  variable list -> 'a join_inputs -> (Typing_env.t * 'a Analysis.t) option
