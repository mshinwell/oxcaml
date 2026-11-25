(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows
   middle_end/flambda2/simplify/unboxing/unbox_continuation_params.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter
  Bound_parameters Build_unboxing_denv Continuation_extra_params_and_args
  Continuation_uses Downwards_env Flambda2_types Is_unboxing_beneficial List
  Name_mode Optimistic_unboxing_decision Profile Stdlib_ Target_system
  Unboxing_epa Unboxing_types.
(* CONSTRUCTORS-WITHOUT-MODULE: Unboxing_types.do_not_unbox_reason
   Unboxing_types.pass *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
(*OCAML
open! Simplify_import
OCAML*)

(* 18-19 *)
From SimplifyPort.abbrev.unbox_continuation_params Require Import Port_abbreviations.
(*OCAML
module U = Unboxing_types
module Decisions = U.Decisions
OCAML*)

(* 21-57. The labelled arguments are in the order of the definition. *)
Definition refine_decision_based_on_arg_types_at_uses (pass : U.pass)
    (rewrite_ids_seen rewrites_ids_known_as_invalid
       : Apply_cont_rewrite_id.Set_.t)
    (machine_width : Target_system.Machine_width.t) (nth_arg : int)
    (arg_type_by_use_id :
      Apply_cont_rewrite_id.Map.t Continuation_uses.arg_at_use)
    (decision : U.decision_)
    : M (U.decision_ * Apply_cont_rewrite_id.Set_.t) :=
  match decision with
  | U.Do_not_unbox _ => ret (decision, rewrites_ids_known_as_invalid)
  | U.Unbox _ =>
    (* 27-57 *)
    Apply_cont_rewrite_id.Map.fold
      (fun rewrite_id (arg_at_use : Continuation_uses.arg_at_use)
           '(decision, invalids) =>
        let! tmp1 :=
          Apply_cont_rewrite_id.Set_.mem rewrite_id rewrite_ids_seen
        in
        let! tmp2 :=
          or_else tmp1
            (Apply_cont_rewrite_id.Set_.mem rewrite_id
               rewrites_ids_known_as_invalid)
        in
        if tmp2
        then ret (decision, invalids)
        else
          let& typing_env_at_use :=
            arg_at_use.(Continuation_uses.typing_env)
          in
          let& arg_type_at_use := arg_at_use.(Continuation_uses.arg_type) in
          (* 38-46 *)
          let* unboxed_arg :=
            match_exn
              (fun _ =>
                TE.get_alias_then_canonical_simple_exn typing_env_at_use
                  (Some Name_mode.normal) None arg_type_at_use)
              Not_found
              (fun _ =>
                ret (Unboxing_epa.Added_by_wrapper_at_rewrite_use nth_arg))
              (fun simple => ret (Unboxing_epa.Available simple))
          in
          (* 47-55 *)
          try_with
            (fun _ =>
              let* decision :=
                Unboxing_epa.compute_extra_args_for_one_decision_and_use pass
                  rewrite_id typing_env_at_use machine_width unboxed_arg
                  decision
              in
              ret (decision, invalids))
            Unboxing_epa.Invalid_apply_cont
            (fun _ =>
              let! tmp1 := Apply_cont_rewrite_id.Set_.add rewrite_id invalids in
              ret (decision, tmp1)))
      arg_type_by_use_id
      (decision, rewrites_ids_known_as_invalid)
  end.

(* 59-68 *)
(* PORT-GAP(loose): the compiler's module is [List]: Stdlib's [List],
   included, and [fold_left3]. Here the module is [List_] and has
   [fold_left3] only; the other functions of [List] are those of decl/. *)
Module List_.
  (* 62-66 *)
  Fixpoint fold_left3 {A B C D : Type} (f : A -> B -> C -> D -> M A)
      (accu : A) (l1 : list B) (l2 : list C) (l3 : list D) {struct l1}
      : M A :=
    match l1, l2, l3 with
    | [], [], [] => ret accu
    | a1 :: l1, a2 :: l2, a3 :: l3 =>
      let! tmp1 := f accu a1 a2 a3 in
      fold_left3 f tmp1 l1 l2 l3
    | _, _, _ => Stdlib_.invalid_arg "List.fold_left3"
    end.
End List_.

(* 69-78 *)
Definition make_do_not_unbox_decisions (params : Bound_parameters.t)
    : M Decisions.t :=
  let* decisions :=
    let! tmp1 := Bound_parameters.to_list params in
    List.map
      (fun param => ret (param, U.Do_not_unbox U.Unboxing_not_requested))
      tmp1
  in
  ret
    {| Unboxing_types.Decisions.decisions := decisions;
       Unboxing_types.Decisions.rewrite_ids_seen :=
         Apply_cont_rewrite_id.Set_.empty;
       Unboxing_types.Decisions.rewrites_ids_known_as_invalid :=
         Apply_cont_rewrite_id.Set_.empty
    |}.

(* 80-82 *)
Inductive continuation_arg_types : Type :=
| Recursive
| Non_recursive (arg_types_by_use_id : Continuation_uses.arg_types_by_use_id).

(* 84-155 *)
(* PORT-GAP(loose): the compiler defines [make_decisions] twice, the second
   time (154-177) by the first; here the first is [make_decisions_]. *)
Definition make_decisions_ (continuation_arg_types : continuation_arg_types)
    (denv : DE.t) (params : Bound_parameters.t) (params_types : list T.t)
    : M (DE.t * Decisions.t) :=
  let* params := Bound_parameters.to_list params in
  (* 87-92 *)
  let* '(continuation_is_recursive, arg_types_by_use_id) :=
    match continuation_arg_types with
    | Recursive =>
      let! tmp1 :=
        List.map (fun _ => ret Apply_cont_rewrite_id.Map.empty) params
      in
      ret (true, tmp1)
    | Non_recursive arg_types_by_use_id => ret (false, arg_types_by_use_id)
    end
  in
  let& empty := Apply_cont_rewrite_id.Set_.empty in
  (* 94-151 *)
  let* '(T5 _ denv rev_decisions seen invalids) :=
    List_.fold_left3
      (fun '(T5 nth denv rev_decisions seen invalids) param param_type
           arg_type_by_use_id =>
        (* Make an optimistic decision, filter it based on the arg types at
           the use sites (to prevent decisions that would be detrimental),
           and compute the necessary denv. *)
        let* decision :=
          let! tmp1 := DE.typing_env denv in
          Optimistic_unboxing_decision.make_optimistic_decision 0
            continuation_is_recursive tmp1 param_type
        in
        (* 106-127 *)
        let* '(decision, invalids) :=
          if continuation_is_recursive
          then
            (* For recursive continuation whether unboxing is beneficial or
               not does not really depends on the external use site: the body
               of the loop matters more than the entry. In the worst case,
               unboxing for recursive continuation risk introducing an
               allocation when leaving the loop if the value is unused, while
               the benefit might be great most of the time. *)
            ret (decision, invalids)
          else
            let* machine_width := DE.machine_width denv in
            let* '(decision, invalids) :=
              refine_decision_based_on_arg_types_at_uses U.Filter empty
                invalids machine_width nth arg_type_by_use_id decision
            in
            let* decision :=
              Is_unboxing_beneficial.filter_non_beneficial_decisions decision
            in
            ret (decision, invalids)
        in
        (* 128-131 *)
        let* denv :=
          let! tmp1 := BP.var param in
          Build_unboxing_denv.denv_of_decision denv tmp1 decision
        in
        (* 132-147. Compute the set of rewrite ids that have been considered
           when updating decisions, and check that all [arg_type_by_use_id]s
           cover the same set of rewrite ids. *)
        let* seen :=
          match seen with
          | Some s =>
            (let! tmp1 :=
               Apply_cont_rewrite_id.Map.for_all
                 (fun id _ => Apply_cont_rewrite_id.Set_.mem id s)
                 arg_type_by_use_id
             in
             assert_ tmp1) ;;
            ret s
          | None =>
            Apply_cont_rewrite_id.Map.fold
              (fun id _ acc => Apply_cont_rewrite_id.Set_.add id acc)
              arg_type_by_use_id empty
          end
        in
        ret (T5 (nth + 1) denv (decision :: rev_decisions) (Some seen) invalids))
      (T5 0 denv [] None Apply_cont_rewrite_id.Set_.empty)
      params params_types arg_types_by_use_id
  in
  (* 152-155 *)
  let& rewrite_ids_seen := match seen with None => empty | Some s => s end in
  let* decisions :=
    let! tmp1 := List.rev rev_decisions in
    List.combine params tmp1
  in
  ret
    (denv,
     {| Unboxing_types.Decisions.decisions := decisions;
        Unboxing_types.Decisions.rewrite_ids_seen := rewrite_ids_seen;
        Unboxing_types.Decisions.rewrites_ids_known_as_invalid := invalids
     |}).

(* 157-180 *)
Definition make_decisions (continuation_arg_types : continuation_arg_types)
    (denv : DE.t) (params : Bound_parameters.t) (params_types : list T.t)
    : M (DE.t * Decisions.t) :=
  Profile.record_call_with_counters (Some true)
    (fun '((_, {| Unboxing_types.Decisions.decisions := decisions |})
           : DE.t * Decisions.t) =>
      let* counters := Profile.Counters.create tt in
      List.fold_left
        (fun counters '((_, decision) : BP.t * U.decision_) =>
          match decision with
          | U.Unbox _ =>
            (* For reference: how many times did we suceed? *)
            Profile.Counters.incr "unbox" counters
          | U.Do_not_unbox
              (U.Not_beneficial | U.Incomplete_parameter_type
              | U.Not_enough_information_at_use | U.All_fields_invalid) =>
            Profile.Counters.incr "do_not_unbox" counters
          | U.Do_not_unbox U.Max_depth_exceeded =>
            (* Should be rare, but interesting to know if it's not. *)
            Profile.Counters.incr "max_depth_exceeded" counters
          | U.Do_not_unbox (U.Not_of_kind_value | U.Unboxing_not_requested) =>
            (* Not interesting to count these -- we can't do better and we
               probably didn't even try. *)
            ret counters
          end)
        counters decisions)
    "make_unboxing_decisions"
    (fun _ => make_decisions_ continuation_arg_types denv params params_types).

(* 182-203. In the compiler: [~machine_width decisions ~arg_types_by_use_id
   existing_extra_params_and_args]. *)
Definition compute_extra_params_and_args
    (machine_width : Target_system.Machine_width.t)
    '({| Unboxing_types.Decisions.decisions := decisions;
         Unboxing_types.Decisions.rewrite_ids_seen := rewrite_ids_seen;
         Unboxing_types.Decisions.rewrites_ids_known_as_invalid :=
           rewrites_ids_known_as_invalid
      |}
      : Decisions.t)
    (arg_types_by_use_id : Continuation_uses.arg_types_by_use_id)
    (existing_extra_params_and_args : EPA.t) : M EPA.t :=
  let* '(T3 _ extra_params_and_args _) :=
    List.fold_left2
      (fun '(T3 nth extra_params_and_args invalids) arg_type_by_use_id
           '((_, decision) : BP.t * U.decision_) =>
        let* '(decision, invalids) :=
          refine_decision_based_on_arg_types_at_uses U.Compute_all_extra_args
            rewrite_ids_seen invalids machine_width nth arg_type_by_use_id
            decision
        in
        let* extra_params_and_args :=
          Unboxing_epa.add_extra_params_and_args extra_params_and_args invalids
            decision
        in
        ret (T3 (nth + 1) extra_params_and_args invalids))
      (T3 0 existing_extra_params_and_args rewrites_ids_known_as_invalid)
      arg_types_by_use_id decisions
  in
  ret extra_params_and_args.
