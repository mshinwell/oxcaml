open FlambdaBindingTime
open FlambdaKindModel
open FlambdaModel
open FlambdaProvers
open FlambdaTypeGrammar
open FlambdaTypingEnv

(** val simplify_project_value_slot : Typing_env.t -> flambda_kind -> value_slot
    -> flambda_type -> simple option **)

let simplify_project_value_slot tenv value_slot_kind slot ty =
  match
    Provers.meet_project_value_slot_simple tenv Name_mode.normal ty slot
      value_slot_kind
  with
  | Some t0 -> (
    match t0 with Meet_shortcut.Known_result s -> Some s | _ -> None)
  | None -> None
