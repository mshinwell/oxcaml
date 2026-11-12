open FlambdaBindingTime
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypingEnv

(** val simplify_simple : Typing_env.t -> simple -> (flambda_type * simple)
    option **)

let simplify_simple tenv s =
  if Typing_env.mem_simple (Some Name_mode.normal) tenv s
  then
    match Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal) s with
    | Some o -> o
    | None -> None
  else None

(** val simplify_simples : Typing_env.t -> simple list -> (flambda_type *
    simple) list option **)

let rec simplify_simples tenv = function
  | [] -> Some []
  | arg :: args0 -> (
    match simplify_simple tenv arg with
    | Some answer -> (
      match simplify_simples tenv args0 with
      | Some answers -> Some (answer :: answers)
      | None -> None)
    | None -> None)
