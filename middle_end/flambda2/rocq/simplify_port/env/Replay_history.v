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

(* This file follows middle_end/flambda2/simplify/env/replay_history.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the arguments by place, the type [t]
   kept as OCaml text) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_expr Call_site_inlining_decision_type
  Continuation Format List Misc Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* List of actions that should be replayed, currently only cares about bound
   variables and continuations. In the future, we may want to also store
   inlining decisions.

   CR gbury: move to a [Replay_action.ml] file ? *)
(* 21-39 *)
Module Action.
  (* 22-25 *)
  Inductive t : Type :=
  | Bound_variable : Variable_.t -> t
  | Bound_continuations : list Continuation.t -> t
  | Inlining_decision :
      Call_site_inlining_decision_type.t -> Apply_expr.t -> t.
  (* the apply is here for debug pruposes *)

  (* 28-38 *)
  (* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept,
     here and at the [print] of line 65. *)
  Definition print (ppf : Format.formatter) (a : t) : M unit :=
    match a with
    | Bound_variable v => Variable_.print ppf v
    | Bound_continuations l =>
      Format.pp_print_list (Some Format.pp_print_space) Continuation.print
        ppf l
    | Inlining_decision decision apply =>
      Format.fprintf4 ppf
        "@[<hov 1>(inlining_decision@ @[<hov 1>(decision@ %a)@]@ @[<hov 1>(apply@ %a)@])@]"
        Call_site_inlining_decision_type.print decision Apply_expr.print
        apply
    end.
End Action.

(* Type def *)
(* ******** *)

(* 44-63. The constructors of [t] have inline records, which Rocq cannot
   print, and the type must stand after the module [Action]: in Rocq it is
   [t_], with the fields by place (a constructor is built by a function of the
   tuple of its fields, and the type is matched by one function for each
   constructor), and [t] is that type, printed as the compiler's definition.
   The compiler's comment on each field stands after the type of that field:
   [history] (47); [always_inline] (52), [previous_history] (55), [variables]
   (58), [continuations] (61). *)
Inductive t_ : Type :=
| First_pass :
    list Action.t
    (* Bindables opened, with the head of the list being the
       innermost/last binder opened *) ->
    t_
| Replaying :
    bool
    (* Force inlining of all function calls during replay. This is for
       instance set by the match-in-match specialization. *) ->
    list Action.t
    (* Bindables opened during the first pass, with the head of the list
       being the outermost/first one opened. *) ->
    Variable_.Map.t Variable_.t
    (* Map from the variables of the current pass to the corresponding
       variable from the first pass. *) ->
    Continuation.Map.t Continuation.t
    (* Map from the continuations of the current pass to the
       corresponding variable from the first pass. *) ->
    t_.
Extract Inductive t_ => "t" [ "(fun x__1 -> First_pass { history = x__1 })" "(fun (x__1, x__2, x__3, x__4) -> Replaying { always_inline = x__1; previous_history = x__2; variables = x__3; continuations = x__4 })" ] "(fun f__1 f__2 x__0 -> match x__0 with First_pass { history = x__1 } -> f__1 x__1 | Replaying { always_inline = x__1; previous_history = x__2; variables = x__3; continuations = x__4 } -> f__2 x__1 x__2 x__3 x__4)".
Definition t : Type := t_.
Extract Constant t => "| First_pass of { history : Action.t list } | Replaying of { always_inline : bool; previous_history : Action.t list; variables : Variable.t Variable.Map.t; continuations : Continuation.t Continuation.Map.t }".

(* 65-81 *)
Definition print (ppf : Format.formatter) (t : Replay_history.t) : M unit :=
  match t with
  | First_pass history =>
    let! tmp1 :=
      papp2 Format.pp_print_list (Some Format.pp_print_space) Action.print
    in
    Format.fprintf2 ppf "@[<hov 1>(first_pass@ @[<hov 1>(history@ %a)@])@]"
      tmp1 history
  | Replaying always_inline previous_history variables continuations =>
    let! tmp1 := papp1 Continuation.Map.print Continuation.print in
    let! tmp2 := papp1 Variable_.Map.print Variable_.print in
    let! tmp3 :=
      papp2 Format.pp_print_list (Some Format.pp_print_space) Action.print
    in
    Format.fprintf7 ppf
      "@[<hov 1>(replaying@ @[<hov 1>(always_inline@ %b)@]@ @[<hov 1>(previous_history@ %a)@]@ @[<hov 1>(variables@ %a)@]@ @[<hov 1>(continuations@ %a)@])@]"
      always_inline tmp3 previous_history tmp2 variables tmp1 continuations
  end.

(* Creating API *)
(* ************ *)

(* 86 *)
Definition first_pass : t := First_pass [].

(* 88-101 *)
Definition replay (always_inline : bool) (t : Replay_history.t)
    : M Replay_history.t :=
  match t with
  | First_pass history =>
    let* previous_history := List.rev history in
    ret
      (Replaying always_inline previous_history Variable_.Map.empty
         Continuation.Map.empty)
  | Replaying _ _ _ _ =>
    fatal_errorf0 "Cannot replay an already replayed binding history"
  end.

(* 103-107 *)
Definition error_empty_history {A : Type} (replay : Replay_history.t)
    (action : Action.t) : M A :=
  fatal_errorf4
    "@[<v>@[<hov>Found an empty replay history when replaying action:@ %a.@]@ Replay: %a@]"
    Action.print action print replay.

(* 109-113 *)
Definition error_mismatched_action {A : Type} (replay : Replay_history.t)
    (old_action new_action : Action.t) : M A :=
  fatal_errorf6
    "@[<v>Action mismatch when replaying history:@ old action: %a@ new action: %a@ replay: %a"
    Action.print old_action Action.print new_action print replay.

(* 115-119 *)
Definition error_not_renamed_version_of {A : Type}
    (replay : Replay_history.t) (old_action new_action : Action.t) : M A :=
  fatal_errorf6
    "@[<v>Actions are not renamed versions when replaying history:@ old action: %a@ new action: %a@ replay: %a"
    Action.print old_action Action.print new_action print replay.

(* 121 *)
Definition check_coherent_inlining_decisions {A B : Type} (_old_decision : A)
    (_new_decision : B) : M unit :=
  ret tt.

(* 123-142 *)
Definition define_variable (var : Variable_.t) (replay : Replay_history.t)
    : M Replay_history.t :=
  let& action := Action.Bound_variable var in
  match replay with
  | First_pass history => ret (First_pass (action :: history))
  | Replaying always_inline (prev_bound :: previous_history) variables
      continuations =>
    match prev_bound with
    | Action.Bound_variable prev_var =>
      let! tmp1 := Variable_.is_renamed_version_of prev_var var in
      if negb tmp1
      then error_not_renamed_version_of replay prev_bound action
      else
        let* variables := Variable_.Map.add var prev_var variables in
        ret (Replaying always_inline previous_history variables continuations)
    | Action.Bound_continuations _ | Action.Inlining_decision _ _ =>
      error_mismatched_action replay prev_bound action
    end
  | Replaying _ [] _ _ => error_empty_history replay action
  end.

(* 144-175 *)
Definition define_continuations (can_be_lifted : bool)
    (conts : list Continuation.t) (replay : Replay_history.t)
    : M Replay_history.t :=
  let& action := Action.Bound_continuations conts in
  match replay with
  | First_pass history => ret (First_pass (action :: history))
  | Replaying always_inline (prev_bound :: previous_history) variables
      continuations =>
    match prev_bound with
    | Action.Bound_continuations prev_conts =>
      (* Continuations that are created during the downwards pass (e.g.
         wrapper continuations for over-applications) cannot be renamed
         versions of each other, so the check does not make sense. *)
      let! tmp1 :=
        and_then can_be_lifted
          (let! tmp2 := List.compare_lengths prev_conts conts in
           let! tmp3 :=
             and_then (tmp2 =? 0)
               (Misc.Stdlib.List.equal Continuation.is_renamed_version_of
                  prev_conts conts)
           in
           ret (negb tmp3))
      in
      if tmp1
      then error_not_renamed_version_of replay prev_bound action
      else
        let* continuations :=
          List.fold_left2
            (fun acc prev_cont cont => Continuation.Map.add cont prev_cont acc)
            continuations prev_conts conts
        in
        ret (Replaying always_inline previous_history variables continuations)
    | Action.Bound_variable _ | Action.Inlining_decision _ _ =>
      error_mismatched_action replay prev_bound action
    end
  | Replaying _ [] _ _ => error_empty_history replay action
  end.

(* 177-193 *)
Definition record_inlining_decision (apply : Apply_expr.t)
    (decision : Call_site_inlining_decision_type.t)
    (replay : Replay_history.t) : M Replay_history.t :=
  let& action := Action.Inlining_decision decision apply in
  match replay with
  | First_pass history => ret (First_pass (action :: history))
  | Replaying always_inline (prev_bound :: previous_history) variables
      continuations =>
    match prev_bound with
    | Action.Inlining_decision prev_decision _apply =>
      check_coherent_inlining_decisions prev_decision decision ;;
      ret (Replaying always_inline previous_history variables continuations)
    | Action.Bound_variable _ | Action.Bound_continuations _ =>
      error_mismatched_action replay prev_bound action
    end
  | Replaying _ [] _ _ => error_empty_history replay action
  end.

(* Inspection API *)
(* ************** *)

(* 198-200 *)
Definition must_inline (t : Replay_history.t) : M bool :=
  match t with
  | First_pass _ => ret false
  | Replaying always_inline _ _ _ => ret always_inline
  end.

(* 202-204 *)
Inductive replay_result (A : Type) : Type :=
| Still_recording : replay_result A
| Replayed : A -> replay_result A.
Arguments Still_recording {A}.
Arguments Replayed {A}.

(* 206-211 *)
Definition replay_variable_mapping (t : Replay_history.t)
    : M (replay_result (Variable_.Map.t Variable_.t)) :=
  match t with
  | First_pass _ => ret Still_recording
  | Replaying _ _ variables _ => ret (Replayed variables)
  end.

(* 213-218 *)
Definition replay_continuation_mapping (t : Replay_history.t)
    : M (replay_result (Continuation.Map.t Continuation.t)) :=
  match t with
  | First_pass _ => ret Still_recording
  | Replaying _ _ _ continuations => ret (Replayed continuations)
  end.

(* 220-230 *)
Definition replay_inlining_decision (t : Replay_history.t)
    : M (replay_result Call_site_inlining_decision_type.t) :=
  match t with
  | First_pass _ => ret Still_recording
  | Replaying _ (Action.Inlining_decision decision _apply :: _) _ _ =>
    ret (Replayed decision)
  | Replaying _
      ([] | (Action.Bound_variable _ | Action.Bound_continuations _) :: _) _ _
    =>
    fatal_errorf0 "Cannot replay: the last action was not an inlining decision"
  end.
