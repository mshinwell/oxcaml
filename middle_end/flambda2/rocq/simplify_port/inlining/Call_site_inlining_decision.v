(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows
   middle_end/flambda2/simplify/inlining/call_site_inlining_decision.ml
   (Git blob 3035e3840781d8b06f8c64bcec35c09f897bc3e1), definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. The compiler's
   file does not open [Simplify_import], and neither does this one. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_expr Bound_parameters
  Call_site_inlining_decision_type Clflags Code_id Code_metadata
  Code_or_metadata Code_size Continuation Cost_metrics Downwards_acc
  Downwards_env Exn_continuation Flambda Flambda2_types Flambda_arity
  Flambda_features Flambda_kind Float Flow Function_decl_inlining_decision_type
  Inlined_attribute Inlining_arguments Inlining_state Inlining_transforms
  Lifted_constant Lifted_constant_state List Or_unknown Oxcaml_args Profile
  Rebuilt_static_const Rec_info_expr Recursive Reg_width_const Replay_history
  Simple Simplified_expr Simplify_common Simplify_rec_info_expr Tag
  Target_ocaml_int Upwards_acc Upwards_env.
Import Flambda.Import_.
(* CONSTRUCTORS-WITHOUT-MODULE: Apply_expr.Result_continuation.t
   Downwards_env.Disable_inlining.t Downwards_env.Disable_inlining_reason.t
   Flambda2_types.meet_shortcut Flambda2_types.reification_result
   Flambda_features.Inlining.round_or_default
   Flambda_kind.With_subkind.Nullable.t Inlined_attribute.t Or_unknown.t
   Recursive.t Replay_history.replay_result *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
(*OCAML
open! Flambda.Import
OCAML*)

(* 18-23 and 43 *)
From SimplifyPort.abbrev.call_site_inlining_decision Require Import Port_abbreviations.
(*OCAML
module DE = Downwards_env
module DA = Downwards_acc
module T = Flambda2_types
module TE = T.Typing_env
module UA = Upwards_acc
module UE = Upwards_env
module FT = Flambda2_types.Function_type
OCAML*)

(* 43 *)

(* 45-158. In the compiler: [dacc ~apply ~function_type ~simplify_expr
   ~rebuild_expr ~return_arity]. *)
Definition speculative_inlining (dacc : DA.t) (apply : Apply.t)
    (function_type : FT.t)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (rebuild_expr : Simplify_common.rebuild Simplified_expr.t)
    (return_arity : Flambda_arity.t_Complex) : M Cost_metrics.t :=
  let* dacc := DA.prepare_for_speculative_inlining dacc in
  (* 52-61. The only way for [unroll_to] not to be None is when an explicit
     Unroll annotation is provided by the user. If this is the case then
     inliner will always inline the function and will not call
     [speculative_inlining]. Thus inside of [speculative_inlining] we will
     always have [unroll_to] = None. We are not disabling unrolling when
     speculating, it just happens that no unrolling can happen while
     speculating right now. *)
  let* '(dacc, expr) :=
    Inlining_transforms.inline dacc apply None false function_type
  in
  (* 62-64 *)
  let* dummy_toplevel_cont :=
    Continuation.create None
      (Some "speculative_inlining_toplevel_continuation") tt
  in
  (* 65-69 *)
  let* dacc :=
    let! tmp1 :=
      Flow.Acc.init_toplevel dummy_toplevel_cont Bound_parameters.empty
    in
    DA.with_flow_acc tmp1 dacc
  in
  (* 70-72 *)
  let* '(expr, dacc) :=
    simplify_expr dacc expr (fun dacc expr => ret (expr, dacc))
  in
  (* 73-123 *)
  let* '(_, uacc) :=
    let* exn_continuation := Apply.exn_continuation apply in
    let* dacc :=
      let! tmp1 := papp1 Flow.Acc.exit_continuation dummy_toplevel_cont in
      DA.map_flow_acc dacc tmp1
    in
    let* data_flow := DA.flow_acc dacc in
    (* 80-84. The dataflow analysis *)
    let* function_return_cont :=
      let! tmp1 := Apply.continuation apply in
      match tmp1 with
      | Apply_expr.Result_continuation.Never_returns =>
        Continuation.create None None tt
      | Apply_expr.Result_continuation.Return cont => ret cont
      end
    in
    (* 85-101. When doing the speculative analysis, in order to not blow up,
       the data_flow analysis is only done on the speculatively inlined body;
       however the reachable code_ids part of the data flow analysis is only
       correct at toplevel when all information about the code_age relation
       and used_value slots is available (for the whole compilation unit).
       Thus we here provide empty/dummy values for the used_value_slots and
       code_age_relation, and ignore the reachable_code_id part of the
       data_flow analysis. [Flow.Analysis.analyze]: the arguments are in the
       order of the interface. *)
    let* flow_result :=
      let! tmp1 := DA.specialization_map dacc in
      let! tmp2 := Exn_continuation.exn_handler exn_continuation in
      let! tmp3 := DA.denv dacc in
      let! tmp4 := DE.machine_width tmp3 in
      Flow.Analysis.analyze (Some true) (Some "speculative") tmp4
        function_return_cont tmp2 T.Code_age_relation.empty Or_unknown.Unknown
        Code_id.Set_.empty tmp1 data_flow
    in
    (* 102-112. Note that we don't need to do anything special if the
       exception continuation takes extra arguments, since we are only
       simplifying the body of the function in question, not substituting it
       into an existing context. *)
    let* uenv :=
      let* machine_width :=
        let! tmp1 := DA.denv dacc in
        DE.machine_width tmp1
      in
      let! tmp1 :=
        Flambda_arity.create_singletons [Flambda_kind.With_subkind.any_value]
      in
      let! tmp2 := Exn_continuation.exn_handler exn_continuation in
      let! tmp3 := DA.are_rebuilding_terms dacc in
      let! tmp4 := UE.create tmp3 machine_width in
      UE.add_function_return_or_exn_continuation tmp4 tmp2 false tmp1
    in
    (* 113-120 *)
    let* uenv :=
      let! tmp1 := Apply.continuation apply in
      match tmp1 with
      | Apply_expr.Result_continuation.Never_returns => ret uenv
      | Apply_expr.Result_continuation.Return return_continuation =>
        let! tmp1 := Flambda_arity.unarize_t return_arity in
        UE.add_function_return_or_exn_continuation uenv return_continuation
          false tmp1
      end
    in
    let* uacc := UA.create flow_result false uenv dacc in
    rebuild_expr expr uacc (fun expr uacc => ret (expr, uacc))
  in
  (* 124-157 *)
  let* cost_metrics_of_lifted_constants :=
    let! tmp1 :=
      Flambda_features.Inlining.speculative_inlining_track_lifted_constants tt
    in
    if tmp1
    then
      (* If we are not at toplevel, there might still be lifted constants to
         be placed in the accumulator whose size must be taken into account
         for speculative inlining. *)
      let* lifted_constants := UA.lifted_constants uacc in
      Lifted_constant_state.fold lifted_constants Cost_metrics.zero
        (fun cost_metrics lifted_constant =>
          let! tmp3 := Lifted_constant.definitions lifted_constant in
          List.fold_left
            (fun cost_metrics definition =>
              let! tmp1 :=
                Lifted_constant.Definition_.defining_expr definition
              in
              let! tmp2 := Rebuilt_static_const.cost_metrics tmp1 in
              Cost_metrics.op_plus cost_metrics tmp2)
            cost_metrics tmp3)
    else ret Cost_metrics.zero
  in
  (* 158 *)
  let! tmp1 := UA.cost_metrics uacc in
  Cost_metrics.op_plus tmp1 cost_metrics_of_lifted_constants.

(* 160-162 *)
(* PORT-GAP(loose): the compiler gives the name [argument_types_useful] to
   this type, to the value of 164-166 and to the function of 168-209. Here
   the type is [argument_types_useful_], the value [argument_types_useful__],
   and the function keeps the name. *)
Inductive argument_types_useful_ : Type :=
| Coarse
| Fine.

(* 164-166 *)
(* PORT-GAP(init): the compiler computes this value when the module starts:
   [Oxcaml_args.Extra_options.symbol], given four of its five arguments,
   declares the option [-X argument-types-useful] and returns the function
   that reads it. A parameter here; its OCaml text is that of the directive,
   which Rocq prints at this place. In the extracted file [__LOC__] is a
   place of that file, not of the compiler's. *)
Parameter argument_types_useful__ : unit -> M argument_types_useful_.
Extract Constant argument_types_useful__ =>
  "
  Oxcaml_args.Extra_options.symbol __LOC__ ""argument-types-useful"" Coarse
    [""coarse"", Coarse; ""fine"", Fine]".

(* 168-209. In the compiler: [dacc ~apply ~code_metadata]. *)
Definition argument_types_useful (dacc : DA.t) (apply : Apply.t)
    (code_metadata : Code_metadata.t) : M bool :=
  let! tmp1 :=
    Flambda_features.Inlining.speculative_inlining_only_if_arguments_useful tt
  in
  if negb tmp1
  then ret true
  else
    let* typing_env :=
      let! tmp1 := DA.denv dacc in
      DE.typing_env tmp1
    in
    (* 176: [argument_types_useful ()] is the value of 164. *)
    let! tmp1 := argument_types_useful__ tt in
    match tmp1 with
    | Coarse =>
      (* 177-185 *)
      let! tmp2 := Apply.args apply in
      List.exists_
        (fun simple =>
          Simple.pattern_match simple
            (fun name _ =>
              let* ty := TE.find typing_env name None in
              let! tmp1 := T.is_unknown_maybe_null typing_env ty in
              ret (negb tmp1))
            (fun _ => ret true))
        tmp2
    | Fine =>
      (* 186-209 *)
      let* arity := Code_metadata.params_arity code_metadata in
      let! tmp3 := Apply.args apply in
      let! tmp4 := Flambda_arity.unarize arity in
      List.exists2_
        (fun full_kind simple =>
          Simple.pattern_match simple
            (fun name _ => T.type_is_useful full_kind typing_env name)
            (fun const =>
              (* If the kind already restricts the possible values to a
                 single constant (e.g. unit type), even a constant can be
                 not useful. *)
              let! tmp1 := Reg_width_const.is_tagged_immediate const in
              match tmp1 with
              | None => ret true
              | Some const =>
                let! tmp1 := Target_ocaml_int.Set_.singleton const in
                let! tmp2 :=
                  Flambda_kind.With_subkind.create Flambda_kind.value
                    (Flambda_kind.With_subkind.Non_null_value_subkind.Variant
                       tmp1 Tag.Scannable.Map.empty)
                    Flambda_kind.With_subkind.Nullable.Non_nullable
                in
                let! tmp5 := Flambda_kind.With_subkind.equal full_kind tmp2 in
                ret (negb tmp5)
              end))
        tmp4 tmp3
    end.

(* 211-216. In the compiler: [~code_metadata cost_metrics]. The attribute
   of 212 is for ocamlformat. *)
Definition inlining_does_decrease_code_size (code_metadata : Code_metadata.t)
    (cost_metrics : Cost_metrics.t) : M bool :=
  let* original_code_size :=
    let! tmp1 := Code_metadata.cost_metrics code_metadata in
    Cost_metrics.size tmp1
  in
  let* inlined_code_size := Cost_metrics.size cost_metrics in
  let! tmp1 := Code_size.op_lt_eq original_code_size inlined_code_size in
  ret (negb tmp1).

(* 218-309. In the compiler: [dacc ~apply ~code_metadata ~function_type
   ~simplify_expr ~rebuild_expr ~return_arity]. *)
Definition might_inline (dacc : DA.t) (apply : Apply.t)
    (code_metadata : Code_metadata.t) (function_type : FT.t)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (rebuild_expr : Simplify_common.rebuild Simplified_expr.t)
    (return_arity : Flambda_arity.t_Complex)
    : M Call_site_inlining_decision_type.t :=
  (* 220-225 *)
  let& code_present :=
    fun (_ : unit) =>
    let* code_or_metadata :=
      let! tmp1 := Code_metadata.code_id code_metadata in
      let! tmp2 := DA.denv dacc in
      DE.find_code_exn tmp2 tmp1
    in
    Code_or_metadata.code_present code_or_metadata
  in
  let* denv := DA.denv dacc in
  let* disable_inlining := DE.disable_inlining denv in
  let* decision := Code_metadata.inlining_decision code_metadata in
  let* is_a_functor := Code_metadata.is_a_functor code_metadata in
  (* 230-235 *)
  let* '(in_a_stub, doing_speculative_inlining) :=
    match disable_inlining with
    | DE.Disable_inlining.Disable_inlining DE.Disable_inlining_reason.Stub =>
      ret (true, false)
    | DE.Disable_inlining.Disable_inlining
        DE.Disable_inlining_reason.Speculative_inlining =>
      ret (false, true)
    | DE.Disable_inlining.Do_not_disable_inlining => ret (false, false)
    end
  in
  (* 236-309 *)
  if in_a_stub
  then ret Call_site_inlining_decision_type.In_a_stub
  else
    let! tmp1 :=
      Function_decl_inlining_decision_type.must_be_inlined decision
    in
    if tmp1
    then
      let! tmp1 := code_present tt in
      if tmp1
      then
        let! tmp1 :=
          Function_decl_inlining_decision_type.has_attribute_inline decision
        in
        ret (Call_site_inlining_decision_type.Definition_says_inline tmp1)
      else ret Call_site_inlining_decision_type.Missing_code
    else
      let! tmp1 :=
        Function_decl_inlining_decision_type.cannot_be_inlined decision
      in
      if tmp1
      then ret Call_site_inlining_decision_type.Definition_says_not_to_inline
      else
        if doing_speculative_inlining
        then ret Call_site_inlining_decision_type.Doing_speculative_inlining
        else
          (* 252-309. [Profile.record_call_with_counters ~accumulate:true
             "speculative_inlining" ~counter_f (fun () -> ..)]: the arguments
             are in the order of the interface. *)
          Profile.record_call_with_counters (Some true)
            (fun (decision : Call_site_inlining_decision_type.t) =>
              let* counters := Profile.Counters.create tt in
              match decision with
              | Call_site_inlining_decision_type.Argument_types_not_useful =>
                Profile.Counters.incr "argument_types_not_useful" counters
              | Call_site_inlining_decision_type.Speculatively_inline
                  cost_metrics _ _ _ =>
                let* counters :=
                  Profile.Counters.incr "speculatively_inline" counters
                in
                let! tmp1 :=
                  inlining_does_decrease_code_size code_metadata cost_metrics
                in
                if tmp1
                then ret counters
                else Profile.Counters.incr "same_code_size" counters
              | Call_site_inlining_decision_type.Speculatively_not_inline _ _ _
                  _ =>
                Profile.Counters.incr "speculatively_not_inline" counters
              | Call_site_inlining_decision_type.Missing_code
              | Call_site_inlining_decision_type.Definition_says_not_to_inline
              | Call_site_inlining_decision_type.In_a_stub
              | Call_site_inlining_decision_type.Doing_speculative_inlining
              | Call_site_inlining_decision_type.Unrolling_depth_exceeded
              | Call_site_inlining_decision_type.Max_inlining_depth_exceeded
              | Call_site_inlining_decision_type.Recursion_depth_exceeded
              | Call_site_inlining_decision_type.Never_inlined_attribute
              | Call_site_inlining_decision_type.Forward_inlined_attribute_but_nothing_to_forward
              | Call_site_inlining_decision_type.Attribute_always
              | Call_site_inlining_decision_type.Replay_history_says_must_inline
                  _
              | Call_site_inlining_decision_type.Begin_unrolling _
              | Call_site_inlining_decision_type.Continue_unrolling
              | Call_site_inlining_decision_type.Definition_says_inline _
              | Call_site_inlining_decision_type.Jsir_inlining_disabled =>
                (* These can't be returned by the speculative inlining cases
                   below. *)
                (let! tmp1 := Flambda_features.check_light_invariants tt in
                 if tmp1
                 then
                   fatal_error
                     "Unexpected call site inlinine decision for speculative inlining"
                 else ret tt) ;;
                ret counters
              end)
            "speculative_inlining"
            (fun _ =>
              let! tmp1 := argument_types_useful dacc apply code_metadata in
              if negb tmp1
              then ret Call_site_inlining_decision_type.Argument_types_not_useful
              else
                let! tmp1 := code_present tt in
                if negb tmp1
                then ret Call_site_inlining_decision_type.Missing_code
                else
                  let* cost_metrics :=
                    speculative_inlining dacc apply function_type simplify_expr
                      rebuild_expr return_arity
                  in
                  let* inlining_args :=
                    let! tmp1 := Apply.inlining_arguments apply in
                    let! tmp2 := DE.inlining_arguments denv in
                    Inlining_arguments.combine tmp2 tmp1
                  in
                  let* evaluated_to :=
                    Cost_metrics.evaluate inlining_args cost_metrics
                  in
                  let* threshold := Inlining_arguments.threshold inlining_args in
                  let* is_under_inline_threshold :=
                    let! tmp1 := Float.compare evaluated_to threshold in
                    ret (tmp1 <=? 0)
                  in
                  if is_under_inline_threshold
                  then
                    ret
                      (Call_site_inlining_decision_type.Speculatively_inline
                         cost_metrics evaluated_to threshold is_a_functor)
                  else
                    ret
                      (Call_site_inlining_decision_type.Speculatively_not_inline
                         cost_metrics evaluated_to threshold is_a_functor)).

(* 311-316. In the compiler: [dacc ~function_type]. *)
Definition get_rec_info (dacc : DA.t) (function_type : FT.t)
    : M Rec_info_expr.t :=
  let* rec_info := FT.rec_info function_type in
  let! tmp1 := DA.typing_env dacc in
  let! tmp2 := Flambda2_types.meet_rec_info tmp1 rec_info in
  match tmp2 with
  | T.Known_result rec_info => ret rec_info
  | T.Need_meet => ret Rec_info_expr.unknown
  | T.Invalid => ret Rec_info_expr.do_not_inline
  end.

(* PORT-GAP(type): 400-414, the compiler's variable [policy] has the type of
   a polymorphic variant that has no definition, [`Heuristic | `Unroll of
   int | `Always]; the Rocq type [policy_] is realised by it. *)
Inductive policy_ : Type :=
| Heuristic
| Unroll (to_ : int)
| Always.
Extract Inductive policy_ => "[ `Heuristic | `Unroll of int | `Always ]" [ "`Heuristic" "`Unroll" "`Always" ].

(* 318-456. In the compiler: [dacc ~simplify_expr ~rebuild_expr
   ~function_type ~apply ~return_arity]. *)
Definition make_decision0 (dacc : DA.t)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (rebuild_expr : Simplify_common.rebuild Simplified_expr.t)
    (function_type : FT.t) (apply : Apply.t)
    (return_arity : Flambda_arity.t_Complex)
    : M Call_site_inlining_decision_type.t :=
  let* must_inline :=
    let! tmp1 := DA.denv dacc in
    DE.must_inline tmp1
  in
  (* 321-329 *)
  let& fail_if_must_inline :=
    fun (_ : unit) =>
    if must_inline
    then
      let! tmp1 := DA.denv dacc in
      let! tmp2 := DE.replay_history tmp1 in
      fatal_errorf2
        "Deciding not to inline an [Apply], but the replay_history says we should inline.@ Replay_history: %a"
        Replay_history.print tmp2
    else ret tt
  in
  (* 330-333 *)
  (* PORT-GAP(loose): 330, the attribute [@local] is not kept. *)
  let& do_not_inline :=
    fun (decision : Call_site_inlining_decision_type.t) =>
    fail_if_must_inline tt ;;
    ret decision
  in
  let* rec_info := get_rec_info dacc function_type in
  let* inlined := Apply.inlined apply in
  (* 336-456 *)
  match inlined with
  | Inlined_attribute.Never_inlined =>
    do_not_inline Call_site_inlining_decision_type.Never_inlined_attribute
  | Inlined_attribute.Forward_inlined =>
    do_not_inline
      Call_site_inlining_decision_type.Forward_inlined_attribute_but_nothing_to_forward
  | Inlined_attribute.Default_inlined | Inlined_attribute.Unroll _ _
  | Inlined_attribute.Always_inlined _ | Inlined_attribute.Hint_inlined =>
    (* 341-456 *)
    match_exn
      (fun _ =>
        let! tmp1 := FT.code_id function_type in
        let! tmp2 := DA.denv dacc in
        DE.find_code_metadata_exn tmp2 tmp1)
      Not_found
      (fun _ => do_not_inline Call_site_inlining_decision_type.Missing_code)
      (fun code_metadata =>
        (* 346-357 *)
        let& code_present :=
          fun (_ : unit) =>
          match_exn
            (fun _ =>
              let! tmp1 := Code_metadata.code_id code_metadata in
              let! tmp2 := DA.denv dacc in
              DE.find_code_exn tmp2 tmp1)
            Not_found
            (fun _ =>
              let! tmp1 := Code_metadata.code_id code_metadata in
              fatal_errorf2
                "[DE.find_code_metadata_exn] found a code metadata, but [DE.find_code_exn] returns Not_found for code_id %a"
                Code_id.print tmp1)
            (fun code_or_metadata =>
              Code_or_metadata.code_present code_or_metadata)
        in
        (* 358-360 *)
        (* PORT-GAP(loose): 358, the attribute [@local] is not kept. *)
        let& inline_if_code_present :=
          fun (decision : Call_site_inlining_decision_type.t) =>
          let! tmp1 := code_present tt in
          if tmp1
          then ret decision
          else do_not_inline Call_site_inlining_decision_type.Missing_code
        in
        (* 361-377. The unrolling process is rather subtle, but it boils
           down to two steps:

           1. We see an [@unrolled n] annotation (with n > 0) on an apply
           expression whose [rec_info] has the unrolling state
           [Not_unrolling]. When we inline the body, we bind [my_depth] to a
           rec_info whose unrolling state is [Unrolling { remaining_depth =
           n }].

           2. When we see that application again, its rec_info will have the
           unrolling state [Unrolling { remaining_depth = n - 1 }] (because
           its depth is [succ my_depth]). At that point, we short-circuit
           most of the inlining logic and inline if and only if n > 0.

           Here we're performing step _2_ (but only, of course, if we
           performed step 1 in a previous call to this function). *)
        let* unrolling_depth :=
          Simplify_rec_info_expr.known_remaining_unrolling_depth dacc rec_info
        in
        (* 378-456 *)
        (* PORT-GAP(loose): 379-380, the compiler's cases are [Some 0] and
           [Some _]; here one case [Some n] and a test of [n]. *)
        match unrolling_depth with
        | Some n =>
          if n =? 0
          then
            do_not_inline
              Call_site_inlining_decision_type.Unrolling_depth_exceeded
          else
            inline_if_code_present
              Call_site_inlining_decision_type.Continue_unrolling
        | None =>
          (* 381-456 *)
          (* lmaurer: This seems semantically dodgy: If we really think of a
             free depth variable as [Unknown], then we shouldn't be
             considering inlining here, because we don't _know_ that we're
             not unrolling. The behavior is what we want, though (and is
             consistent with FLambda 1): If there's a free depth variable,
             that means this is an internal recursive call, which means we
             consider unrolling if [@unrolled] appears. If it's known that
             the unrolling depth is zero, that means we're inlining into
             another function and we're done unrolling, so we immediately
             stop inlining.

             So this seems to be working for the moment, but I wonder what
             are the ramifications of treating unknown-ness as an observable
             property this way. Are we relying on monotonicity somewhere? *)
          let* apply_inlining_state := Apply.inlining_state apply in
          let* recursive := Code_metadata.recursive code_metadata in
          let! tmp1 := Inlining_state.is_depth_exceeded apply_inlining_state in
          if tmp1
          then
            do_not_inline
              Call_site_inlining_decision_type.Max_inlining_depth_exceeded
          else
            (* 400-414 *)
            let* policy :=
              match inlined with
              | Inlined_attribute.Never_inlined
              | Inlined_attribute.Forward_inlined => assert_false
              | Inlined_attribute.Default_inlined => ret Heuristic
              | Inlined_attribute.Unroll to_ _ => ret (Unroll to_)
              | Inlined_attribute.Always_inlined _
              | Inlined_attribute.Hint_inlined =>
                (* Treat [@inlined] and [@inlined hint] the same as
                   [@unrolled 1] whenever the function is recursive. This is
                   particularly important when the annotation is on a
                   parameter and the function is _usually_ non-recursive:
                   we'd rather behave well in the odd case where it isn't. *)
                match recursive with
                | Recursive.Recursive => ret (Unroll 1)
                | Recursive.Non_recursive => ret Always
                end
              end
            in
            (* 415-456 *)
            match policy with
            | Heuristic =>
              let* max_rec_depth :=
                let! tmp1 := DA.denv dacc in
                let! tmp2 := DE.round tmp1 in
                Flambda_features.Inlining.max_rec_depth
                  (Flambda_features.Inlining.Round tmp2)
              in
              let! tmp1 :=
                Simplify_rec_info_expr.depth_may_exceed dacc rec_info
                  max_rec_depth
              in
              if tmp1
              then
                do_not_inline
                  Call_site_inlining_decision_type.Recursion_depth_exceeded
              else
                if must_inline
                then
                  let! tmp1 := DA.denv dacc in
                  let! tmp2 := DE.replay_history tmp1 in
                  let! tmp3 := Replay_history.replay_inlining_decision tmp2 in
                  match tmp3 with
                  | Replay_history.Still_recording =>
                    fatal_errorf0
                      "Internal assumption broken: DE.says must_inline
                  (presumably because of the replay history), but the replay history is still recoding."
                  | Replay_history.Replayed decision =>
                    let! tmp1 := code_present tt in
                    if tmp1
                    then
                      ret
                        (Call_site_inlining_decision_type.Replay_history_says_must_inline
                           decision)
                    else
                      let! tmp1 := Code_metadata.code_id code_metadata in
                      fatal_errorf2
                        "Replay history says we should inline %a, but its code is not present"
                        Code_id.print tmp1
                  end
                else
                  might_inline dacc apply code_metadata function_type
                    simplify_expr rebuild_expr return_arity
            | Unroll unroll_to =>
              let! tmp1 := Simplify_rec_info_expr.can_unroll dacc rec_info in
              if tmp1
              then
                (* This sets off step 1 in the comment above; see
                   [Inlining_transforms] for how [unroll_to] is ultimately
                   handled. *)
                inline_if_code_present
                  (Call_site_inlining_decision_type.Begin_unrolling unroll_to)
              else
                do_not_inline
                  Call_site_inlining_decision_type.Unrolling_depth_exceeded
            | Always =>
              inline_if_code_present
                Call_site_inlining_decision_type.Attribute_always
            end
        end)
  end.

(* 458-464. In the compiler: [dacc ~simplify_expr ~rebuild_expr
   ~function_type ~apply ~return_arity]. *)
Definition make_decision (dacc : DA.t)
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (rebuild_expr : Simplify_common.rebuild Simplified_expr.t)
    (function_type : FT.t) (apply : Apply.t)
    (return_arity : Flambda_arity.t_Complex)
    : M Call_site_inlining_decision_type.t :=
  let! tmp1 := Clflags.target_is_jsir tt in
  if tmp1
  then ret Call_site_inlining_decision_type.Jsir_inlining_disabled
  else
    make_decision0 dacc simplify_expr rebuild_expr function_type apply
      return_arity.
