(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Guillaume Bury, Pierre Chambart and Nathanaëlle Courant, OCamlPro    *)
(*                                                                        *)
(*   Copyright 2013--2024 OCamlPro SAS                                    *)
(*   Copyright 2014--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/env/Replay_history.v, which follows
   middle_end/flambda2/simplify/env/replay_history.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Port_monad

module Action = struct
  type t =
    | Bound_variable of Variable.t
    | Bound_continuations of Continuation.t list
    | Inlining_decision of Call_site_inlining_decision_type.t * Apply_expr.t

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf = function
    | Bound_variable v -> Variable.print ppf v
    | Bound_continuations l ->
      (fun x__1 x__2 x__3 x__4 ->
        Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
        (Some Format.pp_print_space) Continuation.print ppf l
    | Inlining_decision (decision, apply) ->
      Format.fprintf ppf
        "@[<hov 1>(inlining_decision@ @[<hov 1>(decision@ %a)@]@ @[<hov \
         1>(apply@ %a)@])@]"
        Call_site_inlining_decision_type.print decision Apply_expr.print apply
end

type t =
  | First_pass of { history : Action.t list }
  | Replaying of
      { always_inline : bool;
        previous_history : Action.t list;
        variables : Variable.t Variable.Map.t;
        continuations : Continuation.t Continuation.Map.t
      }

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | First_pass { history = x__1 } -> f__1 x__1
    | Replaying
        { always_inline = x__1;
          previous_history = x__2;
          variables = x__3;
          continuations = x__4
        } ->
      f__2 x__1 x__2 x__3 x__4)
    (fun history ->
      Format.fprintf ppf "@[<hov 1>(first_pass@ @[<hov 1>(history@ %a)@])@]"
        ((fun x__1 x__2 x__3 x__4 ->
           Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
           (Some Format.pp_print_space) Action.print)
        history)
    (fun always_inline previous_history variables continuations ->
      Format.fprintf ppf
        "@[<hov 1>(replaying@ @[<hov 1>(always_inline@ %b)@]@ @[<hov \
         1>(previous_history@ %a)@]@ @[<hov 1>(variables@ %a)@]@ @[<hov \
         1>(continuations@ %a)@])@]"
        always_inline
        ((fun x__1 x__2 x__3 x__4 ->
           Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
           (Some Format.pp_print_space) Action.print)
        previous_history
        (Variable.Map.print Variable.print)
        variables
        (Continuation.Map.print Continuation.print)
        continuations)
    t0

(** val first_pass : t **)

let first_pass = (fun x__1 -> First_pass { history = x__1 }) []

(** val replay : bool -> t -> t coq_M **)

let replay always_inline t0 =
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | First_pass { history = x__1 } -> f__1 x__1
    | Replaying
        { always_inline = x__1;
          previous_history = x__2;
          variables = x__3;
          continuations = x__4
        } ->
      f__2 x__1 x__2 x__3 x__4)
    (fun history ->
      let previous_history = List.rev history in
      (fun (x__1, x__2, x__3, x__4) ->
        Replaying
          { always_inline = x__1;
            previous_history = x__2;
            variables = x__3;
            continuations = x__4
          })
        ( always_inline,
          previous_history,
          Variable.Map.empty,
          Continuation.Map.empty ))
    (fun _ _ _ _ ->
      Misc.fatal_errorf "Cannot replay an already replayed binding history")
    t0

(** val error_empty_history : t -> Action.t -> 'a1 coq_M **)

let error_empty_history replay0 action =
  Misc.fatal_errorf
    "@[<v>@[<hov>Found an empty replay history when replaying action:@ %a.@]@ \
     Replay: %a@]"
    Action.print action print replay0

(** val error_mismatched_action : t -> Action.t -> Action.t -> 'a1 coq_M **)

let error_mismatched_action replay0 old_action new_action =
  Misc.fatal_errorf
    "@[<v>Action mismatch when replaying history:@ old action: %a@ new action: \
     %a@ replay: %a"
    Action.print old_action Action.print new_action print replay0

(** val error_not_renamed_version_of : t -> Action.t -> Action.t -> 'a1 coq_M **)

let error_not_renamed_version_of replay0 old_action new_action =
  Misc.fatal_errorf
    "@[<v>Actions are not renamed versions when replaying history:@ old \
     action: %a@ new action: %a@ replay: %a"
    Action.print old_action Action.print new_action print replay0

(** val check_coherent_inlining_decisions : 'a1 -> 'a2 -> unit coq_M **)

let check_coherent_inlining_decisions _ _ = ()

(** val define_variable : Variable.t -> t -> t coq_M **)

let define_variable var replay0 =
  let action = Action.Bound_variable var in
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | First_pass { history = x__1 } -> f__1 x__1
    | Replaying
        { always_inline = x__1;
          previous_history = x__2;
          variables = x__3;
          continuations = x__4
        } ->
      f__2 x__1 x__2 x__3 x__4)
    (fun history ->
      (fun x__1 -> First_pass { history = x__1 }) (action :: history))
    (fun always_inline l variables continuations ->
      match l with
      | [] -> error_empty_history replay0 action
      | prev_bound :: previous_history -> (
        match prev_bound with
        | Action.Bound_variable prev_var ->
          if not (Variable.is_renamed_version_of prev_var var)
          then error_not_renamed_version_of replay0 prev_bound action
          else
            let variables0 = Variable.Map.add var prev_var variables in
            (fun (x__1, x__2, x__3, x__4) ->
              Replaying
                { always_inline = x__1;
                  previous_history = x__2;
                  variables = x__3;
                  continuations = x__4
                })
              (always_inline, previous_history, variables0, continuations)
        | Action.Bound_continuations _ ->
          error_mismatched_action replay0 prev_bound action
        | Action.Inlining_decision (_, _) ->
          error_mismatched_action replay0 prev_bound action))
    replay0

(** val define_continuations : bool -> Continuation.t list -> t -> t coq_M **)

let define_continuations can_be_lifted conts replay0 =
  let action = Action.Bound_continuations conts in
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | First_pass { history = x__1 } -> f__1 x__1
    | Replaying
        { always_inline = x__1;
          previous_history = x__2;
          variables = x__3;
          continuations = x__4
        } ->
      f__2 x__1 x__2 x__3 x__4)
    (fun history ->
      (fun x__1 -> First_pass { history = x__1 }) (action :: history))
    (fun always_inline l variables continuations ->
      match l with
      | [] -> error_empty_history replay0 action
      | prev_bound :: previous_history -> (
        match prev_bound with
        | Action.Bound_variable _ ->
          error_mismatched_action replay0 prev_bound action
        | Action.Bound_continuations prev_conts ->
          if
            can_be_lifted
            && not
                 (List.compare_lengths prev_conts conts = 0
                 && Misc.Stdlib.List.equal Continuation.is_renamed_version_of
                      prev_conts conts)
          then error_not_renamed_version_of replay0 prev_bound action
          else
            let continuations0 =
              List.fold_left2
                (fun acc prev_cont cont ->
                  Continuation.Map.add cont prev_cont acc)
                continuations prev_conts conts
            in
            (fun (x__1, x__2, x__3, x__4) ->
              Replaying
                { always_inline = x__1;
                  previous_history = x__2;
                  variables = x__3;
                  continuations = x__4
                })
              (always_inline, previous_history, variables, continuations0)
        | Action.Inlining_decision (_, _) ->
          error_mismatched_action replay0 prev_bound action))
    replay0

(** val record_inlining_decision : Apply_expr.t ->
    Call_site_inlining_decision_type.t -> t -> t coq_M **)

let record_inlining_decision apply decision replay0 =
  let action = Action.Inlining_decision (decision, apply) in
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | First_pass { history = x__1 } -> f__1 x__1
    | Replaying
        { always_inline = x__1;
          previous_history = x__2;
          variables = x__3;
          continuations = x__4
        } ->
      f__2 x__1 x__2 x__3 x__4)
    (fun history ->
      (fun x__1 -> First_pass { history = x__1 }) (action :: history))
    (fun always_inline l variables continuations ->
      match l with
      | [] -> error_empty_history replay0 action
      | prev_bound :: previous_history -> (
        match prev_bound with
        | Action.Bound_variable _ ->
          error_mismatched_action replay0 prev_bound action
        | Action.Bound_continuations _ ->
          error_mismatched_action replay0 prev_bound action
        | Action.Inlining_decision (prev_decision, _) ->
          let () = check_coherent_inlining_decisions prev_decision decision in
          (fun (x__1, x__2, x__3, x__4) ->
            Replaying
              { always_inline = x__1;
                previous_history = x__2;
                variables = x__3;
                continuations = x__4
              })
            (always_inline, previous_history, variables, continuations)))
    replay0

(** val must_inline : t -> bool coq_M **)

let must_inline t0 =
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | First_pass { history = x__1 } -> f__1 x__1
    | Replaying
        { always_inline = x__1;
          previous_history = x__2;
          variables = x__3;
          continuations = x__4
        } ->
      f__2 x__1 x__2 x__3 x__4)
    (fun _ -> false)
    (fun always_inline _ _ _ -> always_inline)
    t0

type 'a replay_result =
  | Still_recording
  | Replayed of 'a

(** val replay_variable_mapping : t -> Variable.t Variable_.Map.t replay_result
    coq_M **)

let replay_variable_mapping t0 =
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | First_pass { history = x__1 } -> f__1 x__1
    | Replaying
        { always_inline = x__1;
          previous_history = x__2;
          variables = x__3;
          continuations = x__4
        } ->
      f__2 x__1 x__2 x__3 x__4)
    (fun _ -> Still_recording)
    (fun _ _ variables _ -> Replayed variables)
    t0

(** val replay_continuation_mapping : t -> Continuation.t Continuation.Map.t
    replay_result coq_M **)

let replay_continuation_mapping t0 =
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | First_pass { history = x__1 } -> f__1 x__1
    | Replaying
        { always_inline = x__1;
          previous_history = x__2;
          variables = x__3;
          continuations = x__4
        } ->
      f__2 x__1 x__2 x__3 x__4)
    (fun _ -> Still_recording)
    (fun _ _ _ continuations -> Replayed continuations)
    t0

(** val replay_inlining_decision : t -> Call_site_inlining_decision_type.t
    replay_result coq_M **)

let replay_inlining_decision t0 =
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | First_pass { history = x__1 } -> f__1 x__1
    | Replaying
        { always_inline = x__1;
          previous_history = x__2;
          variables = x__3;
          continuations = x__4
        } ->
      f__2 x__1 x__2 x__3 x__4)
    (fun _ -> Still_recording)
    (fun _ l _ _ ->
      match l with
      | [] ->
        Misc.fatal_errorf
          "Cannot replay: the last action was not an inlining decision"
      | t2 :: _ -> (
        match t2 with
        | Action.Bound_variable _ ->
          Misc.fatal_errorf
            "Cannot replay: the last action was not an inlining decision"
        | Action.Bound_continuations _ ->
          Misc.fatal_errorf
            "Cannot replay: the last action was not an inlining decision"
        | Action.Inlining_decision (decision, _) -> Replayed decision))
    t0
