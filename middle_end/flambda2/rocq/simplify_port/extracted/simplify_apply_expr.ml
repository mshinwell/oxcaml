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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Simplify_apply_expr.v, which follows
   middle_end/flambda2/simplify/simplify_apply_expr.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Flambda.Import
open! Simplify_import
open Port_monad
open Simplify_common
open Simplify_import

(** val fail_if_probe : Flambda.Apply.t -> unit coq_M **)

let fail_if_probe apply0 =
  match Flambda.Apply.probe apply0 with
  | Some _ ->
    Misc.fatal_errorf
      "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
       always be direct applications of an OCaml function:@ %a"
      Flambda.Apply.print apply0
  | None -> ()

(** val record_free_names_of_apply_as_used0 : Flambda.Apply.t ->
    Apply_cont_rewrite_id.t option -> Apply_cont_rewrite_id.t -> Flow.Acc.t ->
    Flow.Acc.t coq_M **)

let record_free_names_of_apply_as_used0 apply0 use_id0 exn_cont_use_id0
    data_flow =
  let data_flow0 =
    Flow.Acc.add_used_in_current_handler
      (Flambda.Apply.free_names_without_exn_continuation apply0)
      data_flow
  in
  let exn_cont = Flambda.Apply.exn_continuation apply0 in
  let result_cont =
    let continuation = Flambda.Apply.continuation apply0 in
    match continuation with
    | Apply_expr.Result_continuation.Return k -> (
      match use_id0 with
      | Some use_id1 -> Some (use_id1, k)
      | None -> assert false)
    | Apply_expr.Result_continuation.Never_returns -> (
      match use_id0 with Some _ -> assert false | None -> None)
  in
  Flow.Acc.add_apply_conts result_cont
    (exn_cont_use_id0, exn_cont)
    (Flambda.Apply.return_arity apply0)
    data_flow0

(** val record_free_names_of_apply_as_used : Downwards_acc.t ->
    Apply_cont_rewrite_id.t option -> Apply_cont_rewrite_id.t -> Flambda.Apply.t
    -> Downwards_acc.t coq_M **)

let record_free_names_of_apply_as_used dacc use_id0 exn_cont_use_id0 apply0 =
  Downwards_acc.map_flow_acc dacc
    (record_free_names_of_apply_as_used0 apply0 use_id0 exn_cont_use_id0)

(** val loopify_decision_for_call : Downwards_acc.t -> Flambda.Apply.t ->
    Loopify_state.t coq_M **)

let loopify_decision_for_call dacc apply0 =
  let denv = Downwards_acc.denv dacc in
  if
    Are_rebuilding_terms.do_not_rebuild_terms
      (Downwards_env.are_rebuilding_terms denv)
  then Loopify_state.do_not_loopify
  else
    (fun f__1 f__2 f__3 x__0 ->
      match (x__0 : Closure_info.t) with
      | Closure_info.Not_in_a_closure -> f__1 ()
      | Closure_info.In_a_set_of_closures_but_not_yet_in_a_specific_closure ->
        f__2 ()
      | Closure_info.Closure
          { code_id = x__1;
            return_continuation = x__2;
            exn_continuation = x__3;
            my_closure = x__4;
            my_alloc_region = x__5
          } ->
        f__3 x__1 x__2 x__3 x__4 x__5)
      (fun _ -> Loopify_state.do_not_loopify)
      (fun _ -> Loopify_state.do_not_loopify)
      (fun _ return_continuation exn_continuation my_closure _ ->
        let tenv = Downwards_env.typing_env denv in
        let canon =
         fun simple ->
          Simple.without_coercion
            ((fun x__1 x__2 x__3 x__4 ->
               Flambda2_types.Typing_env.get_canonical_simple_exn x__1
                 ?min_name_mode:x__2 ?name_mode_of_existing_simple:x__3 x__4)
               tenv None None simple)
        in
        match Flambda.Apply.callee apply0 with
        | Some callee ->
          if
            Simple.equal (canon (Simple.var my_closure)) (canon callee)
            && (match Flambda.Apply.continuation apply0 with
              | Apply_expr.Result_continuation.Return apply_return_continuation
                ->
                Continuation.equal apply_return_continuation return_continuation
              | Apply_expr.Result_continuation.Never_returns -> true)
            && Exn_continuation.equal
                 (Flambda.Apply.exn_continuation apply0)
                 (Exn_continuation.create exn_continuation [])
          then Downwards_env.loopify_state denv
          else Loopify_state.do_not_loopify
        | None -> Loopify_state.do_not_loopify)
      (Downwards_env.closure_info denv)

(** val simplify_self_tail_call : Downwards_acc.t -> Flambda.Apply.t ->
    Continuation.t -> Simplified_expr.t down_to_up -> (Simplified_expr.t *
    Downwards_acc.t) coq_M **)

let simplify_self_tail_call dacc apply0 self_cont down_to_up0 =
  Simplify_apply_cont_expr.simplify_apply_cont dacc
    ((fun x__1 x__2 x__3 x__4 ->
       Apply_cont_expr.create ?trap_action:x__1 x__2 x__3 x__4)
       None self_cont
       (Flambda.Apply.args apply0)
       (Flambda.Apply.dbg apply0))
    down_to_up0

(** val simplify_direct_tuple_application : Flambda.Expr.t expr_simplifier ->
    Downwards_acc.t -> Flambda.Apply.t -> Code_id.t -> Code_metadata.t ->
    Simplified_expr.t down_to_up -> (Simplified_expr.t * Downwards_acc.t) coq_M
    **)

let simplify_direct_tuple_application simplify_expr dacc apply0 callee's_code_id
    callee's_code_metadata down_to_up0 =
  let dbg = Flambda.Apply.dbg apply0 in
  let tuple_size =
    Flambda_arity.cardinal_unarized
      (Code_metadata.params_arity callee's_code_metadata)
  in
  let tuple_arg, over_application_args =
    match Flambda.Apply.args apply0 with
    | [] ->
      Misc.fatal_errorf "Empty argument list for direct tuple application:@ %a"
        Flambda.Apply.print apply0
    | tuple :: others -> tuple, others
  in
  let vars_and_fields =
    List.init tuple_size (fun field ->
        ( (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
            None "tuple_field" Flambda_kind.value,
          Flambda_debug_uid.none,
          Simplify_common.project_tuple
            (Downwards_env.machine_width (Downwards_acc.denv dacc))
            dbg tuple_size field tuple_arg ))
  in
  let args_arity =
    let tuple_arity =
      Flambda_arity.create_singletons
        (List.init tuple_size (fun _ -> Flambda_kind.With_subkind.any_value))
    in
    let over_application_arity =
      Flambda_arity.partially_apply (Flambda.Apply.args_arity apply0) 1
    in
    Flambda_arity.concat tuple_arity over_application_arity
  in
  let apply1 =
    Flambda.Apply.with_args apply0
      (List.map
         (fun pat ->
           let v, _, _ = pat in
           Simple.var v)
         vars_and_fields
      @ over_application_args)
      args_arity
  in
  let apply_expr =
    match over_application_args with
    | [] -> Flambda.Expr.create_apply apply1
    | _ :: _ ->
      Simplify_common.split_direct_over_application apply1 callee's_code_id
        callee's_code_metadata
  in
  let expr =
    List.fold_right
      (fun var_and_field body ->
        let v, v_duid, defining_expr = var_and_field in
        let var_bind = Bound_var.create v v_duid Name_mode.normal in
        Flambda.Expr.create_let
          (Flambda.Let.create
             (Bound_pattern.singleton var_bind)
             defining_expr body Or_unknown.Unknown))
      vars_and_fields apply_expr
  in
  simplify_expr dacc expr down_to_up0

(** val update_direct_call_benefit : Simplified_expr.t ->
    Call_kind.Function_call.t -> Code_metadata.t -> Simplified_expr.t coq_M **)

let update_direct_call_benefit expr original_call callee's_code_metadata =
  match original_call with
  | Call_kind.Function_call.Direct old_code_id ->
    let code_id = Code_metadata.code_id callee's_code_metadata in
    if Code_id.equal code_id old_code_id
    then expr
    else
      Simplified_expr.notify_removed Removed_operations.updated_direct_call expr
  | Call_kind.Function_call.Indirect_unknown_arity ->
    Simplified_expr.notify_removed Removed_operations.direct_call_of_indirect
      expr
  | Call_kind.Function_call.Indirect_known_arity _ ->
    Simplified_expr.notify_removed Removed_operations.direct_call_of_indirect
      expr

(** val rebuild_apply : SE.simplified_apply_ -> Upwards_acc.t ->
    Simplify_common.after_rebuild -> (Rebuilt_expr.t * Upwards_acc.t) coq_M **)

let rebuild_apply simplified_apply uacc after_rebuild =
  let { SE.apply = apply0;
        SE.use_id = use_id0;
        SE.exn_cont_use_id = exn_cont_use_id0;
        SE.result_arity = result_arity0;
        SE.is_cold = is_cold0
      } =
    simplified_apply
  in
  let apply1 =
    Simplify_common.update_exn_continuation_extra_args uacc exn_cont_use_id0
      apply0
  in
  let erase_callee = false in
  let apply2 =
    if erase_callee then Flambda.Apply.erase_callee apply1 else apply1
  in
  let uacc0, expr =
    Expr_builder.rewrite_fixed_arity_apply uacc use_id0 is_cold0
      (Flambda_arity.unarize_t result_arity0)
      apply2
  in
  after_rebuild expr uacc0

type inlining_decision =
  | Do_not_inline of { erase_attribute : bool }
  | Inline of DA.t * Expr.t

(** val simplify_direct_full_application : Flambda.Expr.t expr_simplifier ->
    Simplified_expr.t rebuild -> Downwards_acc.t -> Flambda.Apply.t ->
    Flambda2_types.Function_type.t option -> [ `Complex ] Flambda_arity.t ->
    [ `Complex ] Flambda_arity.t -> Result_types.t Or_unknown_or_bottom.t ->
    Simplified_expr.t down_to_up -> Call_kind.Function_call.t -> Code_metadata.t
    -> Inlined_debuginfo.t option -> (Simplified_expr.t * Downwards_acc.t) coq_M
    **)

let simplify_direct_full_application simplify_expr rebuild_expr dacc apply0
    function_type params_arity result_arity0 result_types down_to_up0
    original_call callee's_code_metadata inlined_forwarded_from =
  let inlined =
    match function_type with
    | Some function_type0 ->
      let decision =
        Call_site_inlining_decision.make_decision dacc simplify_expr
          rebuild_expr function_type0 apply0 result_arity0
      in
      let unrolling_depth =
        Simplify_rec_info_expr.known_remaining_unrolling_depth dacc
          (Call_site_inlining_decision.get_rec_info dacc function_type0)
      in
      let () =
        if
          Are_rebuilding_terms.do_rebuild_terms
            (Downwards_env.are_rebuilding_terms (Downwards_acc.denv dacc))
        then
          Inlining_report.record_decision_at_call_site_for_known_function
            (Downwards_env.inlining_history_tracker (Downwards_acc.denv dacc))
            unrolling_depth apply0 Inlining_report.Pass.Before_simplify
            (Code_metadata.absolute_history callee's_code_metadata)
            (Downwards_acc.are_rebuilding_terms dacc)
            inlined_forwarded_from decision
        else ()
      in
      (fun f__1 f__2 x__0 ->
        match (x__0 : Call_site_inlining_decision_type.can_inline) with
        | Call_site_inlining_decision_type.Do_not_inline
            { erase_attribute_if_ignored = x__1 } ->
          f__1 x__1
        | Call_site_inlining_decision_type.Inline
            { unroll_to = x__1; was_inline_always = x__2 } ->
          f__2 x__1 x__2)
        (fun erase_attribute_if_ignored ->
          (fun x__1 -> Do_not_inline { erase_attribute = x__1 })
            erase_attribute_if_ignored)
        (fun unroll_to was_inline_always ->
          let dacc0 =
            Downwards_acc.map_denv dacc
              (Downwards_env.record_inlining_decision apply0 decision)
          in
          let dacc1, inlined =
            Inlining_transforms.inline dacc0 apply0 unroll_to was_inline_always
              function_type0
          in
          Inline (dacc1, inlined))
        (Call_site_inlining_decision_type.can_inline decision)
    | None -> (fun x__1 -> Do_not_inline { erase_attribute = x__1 }) false
  in
  (fun f__1 f__2 x__0 ->
    match x__0 with
    | Do_not_inline { erase_attribute = x__1 } -> f__1 x__1
    | Inline (x__1, x__2) -> f__2 x__1 x__2)
    (fun erase_attribute ->
      let apply1 =
        let inlined0 =
          if erase_attribute
          then Inlined_attribute.Default_inlined
          else
            Inlined_attribute.with_use_info
              (Flambda.Apply.inlined apply0)
              Inlined_attribute.Use_info.Unused_because_of_call_site_decision
        in
        Flambda.Apply.with_inlined_attribute apply0 inlined0
      in
      match loopify_decision_for_call dacc apply1 with
      | Loopify_state.Do_not_loopify ->
        let dacc0, use_id0, result_continuation =
          let result_continuation = Flambda.Apply.continuation apply1 in
          match result_continuation with
          | Apply_expr.Result_continuation.Return apply_return_continuation -> (
            match result_types with
            | Or_unknown_or_bottom.Unknown ->
              let env_at_use = Downwards_acc.denv dacc in
              let env_at_use0 =
                if Code_metadata.cold callee's_code_metadata
                then Downwards_env.mark_as_cold env_at_use
                else env_at_use
              in
              let dacc0, use_id0 =
                Downwards_acc.record_continuation_use dacc
                  apply_return_continuation
                  ((fun x__1 ->
                     (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                       : Continuation_use_kind.t))
                     true)
                  env_at_use0
                  ((fun x__1 x__2 x__3 ->
                     Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1
                       x__2 x__3)
                     (Some
                        (Alloc_mode.For_applications.as_type
                           (Flambda.Apply.return_mode apply1)))
                     (Downwards_env.machine_width (Downwards_acc.denv dacc))
                     result_arity0)
              in
              dacc0, Some use_id0, result_continuation
            | Or_unknown_or_bottom.Ok result_types0 ->
              Result_types.pattern_match result_types0
                (fun params results env_extension ->
                  let () =
                    if
                      Flambda_arity.cardinal_unarized params_arity
                      <> Bound_parameters.cardinal params
                    then
                      Misc.fatal_errorf
                        "Params arity %a does not match up with params in the \
                         result types structure:@ %a@ for application:@ %a"
                        Flambda_arity.print params_arity Result_types.print
                        result_types0 Flambda.Apply.print apply1
                    else ()
                  in
                  let () =
                    if
                      Flambda_arity.cardinal_unarized result_arity0
                      <> Bound_parameters.cardinal results
                    then
                      Misc.fatal_errorf
                        "Result arity %a does not match up with the result \
                         types structure:@ %a@ for application:@ %a"
                        Flambda_arity.print params_arity Result_types.print
                        result_types0 Flambda.Apply.print apply1
                    else ()
                  in
                  let denv = Downwards_acc.denv dacc in
                  let denv0 =
                    (fun x__1 x__2 x__3 x__4 x__5 ->
                      Downwards_env.add_parameters_with_unknown_types x__1
                        ?alloc_modes:x__2 ?name_mode:x__3 x__4 x__5)
                      false None (Some Name_mode.in_types) denv params
                  in
                  let params0 = Bound_parameters.to_list params in
                  let results0 = Bound_parameters.to_list results in
                  let denv1 =
                    let args = Flambda.Apply.args apply1 in
                    let () = assert (List.compare_lengths params0 args = 0) in
                    List.fold_left2
                      (fun denv1 param arg ->
                        Downwards_env.add_equation_on_variable denv1
                          (Bound_parameter.var param)
                          (Flambda2_types.alias_type_of
                             (Flambda_kind.With_subkind.kind
                                (Bound_parameter.kind param))
                             arg))
                      denv0 params0 args
                  in
                  let result_arity1 = Flambda_arity.unarize result_arity0 in
                  let denv2 =
                    List.fold_left2
                      (fun denv2 kind result ->
                        let result_var, result_uid =
                          Bound_parameter.var_and_uid result
                        in
                        Downwards_env.add_variable denv2
                          (Bound_var.create result_var result_uid
                             Name_mode.in_types)
                          ((fun x__1 x__2 x__3 ->
                             Flambda2_types.unknown_with_subkind
                               ?alloc_mode:x__1 x__2 x__3)
                             (Some
                                (Alloc_mode.For_applications.as_type
                                   (Flambda.Apply.return_mode apply1)))
                             (Downwards_env.machine_width denv2)
                             kind))
                      denv1 result_arity1 results0
                  in
                  let denv3 =
                    Downwards_env.extend_typing_environment denv2 env_extension
                  in
                  let arg_types =
                    List.map2
                      (fun kind result_var ->
                        Flambda2_types.alias_type_of
                          (Flambda_kind.With_subkind.kind kind)
                          (Bound_parameter.simple result_var))
                      result_arity1 results0
                  in
                  let env_at_use =
                    if Code_metadata.cold callee's_code_metadata
                    then Downwards_env.mark_as_cold denv3
                    else denv3
                  in
                  let dacc0, use_id0 =
                    Downwards_acc.record_continuation_use dacc
                      apply_return_continuation
                      ((fun x__1 ->
                         (Continuation_use_kind.Non_inlinable
                            { escaping = x__1 }
                           : Continuation_use_kind.t))
                         true)
                      env_at_use arg_types
                  in
                  dacc0, Some use_id0, result_continuation)
            | Or_unknown_or_bottom.Bottom ->
              dacc, None, Apply_expr.Result_continuation.Never_returns)
          | Apply_expr.Result_continuation.Never_returns -> (
            match result_types with
            | Or_unknown_or_bottom.Unknown ->
              dacc, None, Apply_expr.Result_continuation.Never_returns
            | Or_unknown_or_bottom.Ok _ ->
              dacc, None, Apply_expr.Result_continuation.Never_returns
            | Or_unknown_or_bottom.Bottom ->
              dacc, None, Apply_expr.Result_continuation.Never_returns)
        in
        let env_at_use = Downwards_acc.denv dacc0 in
        let env_at_use0 =
          if Code_metadata.cold callee's_code_metadata
          then Downwards_env.mark_as_cold env_at_use
          else env_at_use
        in
        let dacc1, exn_cont_use_id0 =
          Downwards_acc.record_continuation_use dacc0
            (Exn_continuation.exn_handler
               (Flambda.Apply.exn_continuation apply1))
            ((fun x__1 ->
               (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                 : Continuation_use_kind.t))
               true)
            env_at_use0
            ((fun x__1 x__2 x__3 ->
               Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2
                 x__3)
               None
               (Downwards_env.machine_width (Downwards_acc.denv dacc0))
               (Exn_continuation.arity (Flambda.Apply.exn_continuation apply1)))
        in
        let apply2 =
          Flambda.Apply.with_continuation apply1 result_continuation
        in
        let dacc2 =
          record_free_names_of_apply_as_used dacc1 use_id0 exn_cont_use_id0
            apply2
        in
        let expr =
          (fun x__1 x__2 x__3 x__4 x__5 ->
            Simplified_expr.simplified_apply ?result_arity:x__1 x__2 x__3 x__4
              x__5)
            (Some result_arity0) apply2 use_id0 exn_cont_use_id0
            (Code_metadata.cold callee's_code_metadata)
        in
        let expr0 =
          update_direct_call_benefit expr original_call callee's_code_metadata
        in
        down_to_up0 dacc2 expr0
      | Loopify_state.Loopify self_cont ->
        simplify_self_tail_call dacc apply1 self_cont down_to_up0)
    (fun dacc0 inlined0 ->
      let is_cold0 = Code_metadata.cold callee's_code_metadata in
      let down_to_up1 =
       fun dacc1 simplified_body ->
        let simplified_body0 =
          update_direct_call_benefit simplified_body original_call
            callee's_code_metadata
        in
        let simplified_body1 =
          Simplified_expr.notify_removed Removed_operations.call
            simplified_body0
        in
        let simplified_body2 =
          if is_cold0
          then Simplified_expr.mark_as_cold simplified_body1
          else simplified_body1
        in
        down_to_up0 dacc1 simplified_body2
      in
      simplify_expr dacc0 inlined0 down_to_up1)
    inlined

(** val simplify_direct_partial_application : Flambda.Expr.t expr_simplifier ->
    Downwards_acc.t -> Flambda.Apply.t -> Code_id.t -> Code_metadata.t ->
    Function_slot.t -> [ `Complex ] Flambda_arity.t -> Alloc_mode.For_types.t
    list -> [ `Complex ] Flambda_arity.t -> [ `Complex ] Flambda_arity.t ->
    Recursive.t -> Simplified_expr.t down_to_up -> Call_kind.Function_call.t ->
    Alloc_mode.For_types.t -> First_complex_local_param.t -> (Simplified_expr.t
    * Downwards_acc.t) coq_M **)

let simplify_direct_partial_application =
 fun _ ->
  Misc.fatal_error "PORT-GAP(unported): simplify_direct_partial_application"

(** val simplify_direct_over_application : Flambda.Expr.t expr_simplifier ->
    Downwards_acc.t -> Flambda.Apply.t -> Simplified_expr.t down_to_up ->
    Call_kind.Function_call.t -> Code_id.t -> Code_metadata.t ->
    (Simplified_expr.t * Downwards_acc.t) coq_M **)

let simplify_direct_over_application simplify_expr dacc apply0 down_to_up0
    original_call callee's_code_id callee's_code_metadata =
  let () = fail_if_probe apply0 in
  let expr =
    Simplify_common.split_direct_over_application apply0 callee's_code_id
      callee's_code_metadata
  in
  let down_to_up1 =
   fun dacc0 expr0 ->
    let expr1 =
      match original_call with
      | Call_kind.Function_call.Direct _ -> expr0
      | Call_kind.Function_call.Indirect_unknown_arity ->
        Simplified_expr.notify_removed
          Removed_operations.direct_call_of_indirect expr0
      | Call_kind.Function_call.Indirect_known_arity _ ->
        Simplified_expr.notify_removed
          Removed_operations.direct_call_of_indirect expr0
    in
    down_to_up0 dacc0 expr1
  in
  simplify_expr dacc expr down_to_up1

(** val replace_apply_by_invalid : Downwards_acc.t -> Simplified_expr.t
    down_to_up -> Flambda.Invalid.t -> (Simplified_expr.t * Downwards_acc.t)
    coq_M **)

let replace_apply_by_invalid dacc down_to_up0 reason =
  down_to_up0 dacc (Simplified_expr.simplified_invalid reason)

(** val arity_mismatch : [ `Complex ] Flambda_arity.t -> [ `Complex ]
    Flambda_arity.t -> bool coq_M **)

let arity_mismatch params_arity args_arity =
  let params = Flambda_arity.unarize_per_parameter params_arity in
  let args = Flambda_arity.unarize_per_parameter args_arity in
  let rec has_mismatch params0 args0 =
    match params0 with
    | [] -> false
    | param :: params1 -> (
      match args0 with
      | [] -> false
      | arg :: args1 ->
        let c = List.compare_lengths param arg in
        if c = 0
        then
          List.exists2
            (fun param_component arg_component ->
              not
                (Flambda_kind.equal
                   (Flambda_kind.With_subkind.kind param_component)
                   (Flambda_kind.With_subkind.kind arg_component)))
            param arg
          || has_mismatch params1 args1
        else true)
  in
  has_mismatch params args

(** val simplify_function_call_where_callee's_type_unavailable : Downwards_acc.t
    -> Flambda.Apply.t -> Call_kind.Function_call.t -> Simplified_expr.t
    down_to_up -> (Simplified_expr.t * Downwards_acc.t) coq_M **)

let simplify_function_call_where_callee's_type_unavailable dacc apply0 call
    down_to_up0 =
  let () = fail_if_probe apply0 in
  let denv = Downwards_acc.denv dacc in
  let () =
    if
      Are_rebuilding_terms.do_rebuild_terms
        (Downwards_env.are_rebuilding_terms denv)
    then
      Inlining_report.record_decision_at_call_site_for_unknown_function
        (Downwards_env.inlining_history_tracker denv)
        apply0 Inlining_report.Pass.Before_simplify ()
    else ()
  in
  let env_at_use = denv in
  let dacc0, use_id0 =
    match Flambda.Apply.continuation apply0 with
    | Apply_expr.Result_continuation.Return continuation ->
      let dacc0, use_id0 =
        Downwards_acc.record_continuation_use dacc continuation
          ((fun x__1 ->
             (Continuation_use_kind.Non_inlinable { escaping = x__1 }
               : Continuation_use_kind.t))
             true)
          env_at_use
          ((fun x__1 x__2 x__3 ->
             Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
             (Some
                (Alloc_mode.For_applications.as_type
                   (Flambda.Apply.return_mode apply0)))
             (Downwards_env.machine_width denv)
             (Flambda.Apply.return_arity apply0))
      in
      dacc0, Some use_id0
    | Apply_expr.Result_continuation.Never_returns -> dacc, None
  in
  let dacc1, exn_cont_use_id0 =
    Downwards_acc.record_continuation_use dacc0
      (Exn_continuation.exn_handler (Flambda.Apply.exn_continuation apply0))
      ((fun x__1 ->
         (Continuation_use_kind.Non_inlinable { escaping = x__1 }
           : Continuation_use_kind.t))
         true)
      (Downwards_acc.denv dacc0)
      ((fun x__1 x__2 x__3 ->
         Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
         None
         (Downwards_env.machine_width (Downwards_acc.denv dacc0))
         (Exn_continuation.arity (Flambda.Apply.exn_continuation apply0)))
  in
  let call_kind =
    match call with
    | Call_kind.Function_call.Direct code_id ->
      if Code_id.Set.mem code_id (Downwards_acc.code_ids_never_simplified dacc1)
      then Call_kind.indirect_function_call_known_arity Or_unknown.Unknown
      else Call_kind.direct_function_call code_id
    | Call_kind.Function_call.Indirect_unknown_arity ->
      Call_kind.indirect_function_call_unknown_arity
    | Call_kind.Function_call.Indirect_known_arity t -> (
      match t with
      | Or_unknown.Known code_ids ->
        if
          Code_id.Set.disjoint code_ids
            (Downwards_acc.code_ids_never_simplified dacc1)
        then
          Call_kind.indirect_function_call_known_arity
            (Or_unknown.Known code_ids)
        else Call_kind.indirect_function_call_known_arity Or_unknown.Unknown
      | Or_unknown.Unknown ->
        Call_kind.indirect_function_call_known_arity Or_unknown.Unknown)
  in
  let apply1 = Apply_expr.with_call_kind apply0 call_kind in
  let apply2 =
    Apply_expr.with_inlined_attribute apply1
      (Inlined_attribute.with_use_info
         (Flambda.Apply.inlined apply1)
         Inlined_attribute.Use_info.Unused_because_function_unknown)
  in
  let dacc2 =
    record_free_names_of_apply_as_used dacc1 use_id0 exn_cont_use_id0 apply2
  in
  down_to_up0 dacc2
    ((fun x__1 x__2 x__3 x__4 x__5 ->
       Simplified_expr.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)
       None apply2 use_id0 exn_cont_use_id0 false)

(** val simplify_direct_function_call : Flambda.Expr.t expr_simplifier ->
    Simplified_expr.t rebuild -> Downwards_acc.t -> Flambda.Apply.t -> Code_id.t
    -> Code_metadata.t -> Code_id.Set.t Or_unknown.t -> Function_slot.t ->
    Call_kind.Function_call.t -> [ `Complex ] Flambda_arity.t -> Result_types.t
    Or_unknown_or_bottom.t -> Recursive.t -> bool -> Alloc_mode.For_types.t ->
    Flambda2_types.Function_type.t -> Simplified_expr.t down_to_up ->
    Call_kind.Function_call.t -> Inlined_debuginfo.t option ->
    (Simplified_expr.t * Downwards_acc.t) coq_M **)

let simplify_direct_function_call simplify_expr rebuild_expr dacc apply0
    callee's_code_id_from_type callee's_code_metadata_from_type
    callee's_code_ids_from_call_kind callee's_function_slot original_call
    result_arity0 result_types recursive must_be_detupled
    closure_alloc_mode_from_type function_decl down_to_up0 call
    inlined_forwarded_from =
  let result_types0 =
    let inlined = Flambda.Apply.inlined apply0 in
    let probe = Flambda.Apply.probe apply0 in
    match probe with
    | Some _ -> (
      match inlined with
      | Inlined_attribute.Always_inlined _ ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Flambda.Apply.print apply0
      | Inlined_attribute.Hint_inlined ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Flambda.Apply.print apply0
      | Inlined_attribute.Forward_inlined ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Flambda.Apply.print apply0
      | Inlined_attribute.Never_inlined -> Or_unknown_or_bottom.Unknown
      | Inlined_attribute.Unroll (_, _) ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Flambda.Apply.print apply0
      | Inlined_attribute.Default_inlined ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Flambda.Apply.print apply0)
    | None -> result_types
  in
  let callee's_code_ids =
    match callee's_code_ids_from_call_kind with
    | Or_unknown.Known callee's_code_ids_from_call_kind0 ->
      let typing_env = Downwards_acc.typing_env dacc in
      Flambda2_types.Code_age_relation.meet_set
        (Flambda2_types.Typing_env.code_age_relation typing_env)
        (Flambda2_types.Typing_env.code_age_relation_resolver typing_env)
        callee's_code_ids_from_call_kind0
        (Code_id.Set.singleton callee's_code_id_from_type)
    | Or_unknown.Unknown ->
      Or_bottom.Ok (Code_id.Set.singleton callee's_code_id_from_type)
  in
  match callee's_code_ids with
  | Or_bottom.Ok callee's_code_ids0 ->
    let callee's_code_id, callee's_code_metadata =
      match Code_id.Set.get_singleton callee's_code_ids0 with
      | Some callee's_code_id ->
        Port_monad.match_exn
          (fun _ ->
            Downwards_env.find_code_metadata_exn (Downwards_acc.denv dacc)
              callee's_code_id)
          Port_monad.not_found
          (fun _ ->
            callee's_code_id_from_type, callee's_code_metadata_from_type)
          (fun callee's_code_metadata ->
            callee's_code_id, callee's_code_metadata)
      | None -> callee's_code_id_from_type, callee's_code_metadata_from_type
    in
    let call_kind = Call_kind.direct_function_call callee's_code_id in
    let apply1 = Flambda.Apply.with_call_kind apply0 call_kind in
    let params_arity = Code_metadata.params_arity callee's_code_metadata in
    let args_arity = Flambda.Apply.args_arity apply1 in
    if must_be_detupled
    then
      simplify_direct_tuple_application simplify_expr dacc apply1
        callee's_code_id callee's_code_metadata down_to_up0
    else if arity_mismatch params_arity args_arity
    then
      if Flambda_features.kind_checks ()
      then
        Misc.fatal_errorf
          "Mismatched arities for arguments to direct OCaml function call@ \
           (expected %a, found %a):@ %a"
          Flambda_arity.print params_arity Flambda_arity.print args_arity
          Flambda.Apply.print apply1
      else
        replace_apply_by_invalid dacc down_to_up0
          ((fun (x__1, x__2, x__3) ->
             (Flambda.Invalid.Direct_application_parameter_kind_mismatch
                { params_arity = x__1; args_arity = x__2; apply = x__3 }
               : Flambda.Invalid.t))
             (params_arity, args_arity, apply1))
    else
      let args_arity0 = Flambda.Apply.args_arity apply1 in
      let provided_num_args = Flambda_arity.num_params args_arity0 in
      let num_params = Flambda_arity.num_params params_arity in
      let result_arity_of_application = Flambda.Apply.return_arity apply1 in
      if provided_num_args = num_params
      then
        if
          not
            (Flambda_arity.equal_ignoring_subkinds result_arity0
               result_arity_of_application)
        then
          if Flambda_features.kind_checks ()
          then
            Misc.fatal_errorf
              "Wrong return arity for direct OCaml function call@ (expected \
               %a, found %a):@ %a"
              Flambda_arity.print result_arity0 Flambda_arity.print
              result_arity_of_application Flambda.Apply.print apply1
          else
            replace_apply_by_invalid dacc down_to_up0
              (Flambda.Invalid.Application_result_kind_mismatch
                 (result_arity0, apply1))
        else
          simplify_direct_full_application simplify_expr rebuild_expr dacc
            apply1 (Some function_decl) params_arity result_arity0 result_types0
            down_to_up0 original_call callee's_code_metadata
            inlined_forwarded_from
      else if provided_num_args > num_params
      then
        if not (Flambda_arity.is_one_param_of_kind_value result_arity0)
        then
          if Flambda_features.kind_checks ()
          then
            Misc.fatal_errorf
              "Non-singleton-value return arity for overapplied OCaml \
               function:@ %a"
              Flambda.Apply.print apply1
          else
            replace_apply_by_invalid dacc down_to_up0
              (Flambda.Invalid.Application_result_kind_mismatch
                 (result_arity0, apply1))
        else
          simplify_direct_over_application simplify_expr dacc apply1 down_to_up0
            original_call callee's_code_id callee's_code_metadata
      else if provided_num_args > 0 && provided_num_args < num_params
      then
        if
          not
            (Flambda_arity.is_one_param_of_kind_value
               result_arity_of_application)
        then
          if Flambda_features.kind_checks ()
          then
            Misc.fatal_errorf
              "Non-singleton-value return arity for partially-applied OCaml \
               function:@ %a"
              Flambda.Apply.print apply1
          else
            replace_apply_by_invalid dacc down_to_up0
              (Flambda.Invalid.Application_result_kind_mismatch
                 ( Flambda_arity.create_singletons
                     (Flambda_kind.With_subkind.any_value :: []),
                   apply1 ))
        else if
          Downwards_env.disable_partial_application_stub_generation
            (Downwards_acc.denv dacc)
        then
          simplify_function_call_where_callee's_type_unavailable dacc apply1
            call down_to_up0
        else
          simplify_direct_partial_application simplify_expr dacc apply1
            callee's_code_id callee's_code_metadata callee's_function_slot
            params_arity
            (Code_metadata.param_modes callee's_code_metadata)
            args_arity0 result_arity0 recursive down_to_up0 original_call
            closure_alloc_mode_from_type
            (Code_metadata.first_complex_local_param callee's_code_metadata)
      else
        Misc.fatal_errorf
          "Function with %d params when simplifying direct OCaml function call \
           with %d arguments: %a"
          num_params provided_num_args Flambda.Apply.print apply1
  | Or_bottom.Bottom ->
    replace_apply_by_invalid dacc down_to_up0
      (Flambda.Invalid.Closure_type_was_invalid apply0)

(** val simplify_function_call : Flambda.Expr.t expr_simplifier ->
    Simplified_expr.t rebuild -> Downwards_acc.t -> Flambda.Apply.t ->
    Flambda2_types.t option -> Call_kind.Function_call.t -> Simplified_expr.t
    down_to_up -> Inlined_debuginfo.t option -> (Simplified_expr.t *
    Downwards_acc.t) coq_M **)

let simplify_function_call simplify_expr rebuild_expr dacc apply0 callee_ty call
    down_to_up0 inlined_forwarded_from =
  let call_must_be_detupled =
   fun is_function_decl_tupled ->
    match call with
    | Call_kind.Function_call.Direct _ -> false
    | Call_kind.Function_call.Indirect_unknown_arity -> is_function_decl_tupled
    | Call_kind.Function_call.Indirect_known_arity _ -> false
  in
  let type_unavailable =
   fun call0 ->
    simplify_function_call_where_callee's_type_unavailable dacc apply0 call0
      down_to_up0
  in
  let not_a_closure =
   fun _ ->
    down_to_up0 dacc
      (Simplified_expr.simplified_invalid
         (Flambda.Invalid.Closure_type_was_invalid apply0))
  in
  let denv = Downwards_acc.denv dacc in
  match callee_ty with
  | Some callee_ty0 ->
    (fun f__1 f__2 f__3 x__0 ->
      match (x__0 : _ Flambda2_types.meet_shortcut) with
      | Flambda2_types.Known_result x__1 -> f__1 x__1
      | Flambda2_types.Need_meet -> f__2 ()
      | Flambda2_types.Invalid -> f__3 ())
      (fun t ->
        let ( callee's_function_slot,
              closure_alloc_mode_from_type,
              _,
              func_decl_type ) =
          t
        in
        let callee's_code_ids_from_call_kind =
          match call with
          | Call_kind.Function_call.Direct code_id ->
            Or_unknown.Known (Code_id.Set.singleton code_id)
          | Call_kind.Function_call.Indirect_unknown_arity -> Or_unknown.Unknown
          | Call_kind.Function_call.Indirect_known_arity code_ids -> code_ids
        in
        let callee's_code_id_from_type =
          Flambda2_types.Function_type.code_id func_decl_type
        in
        Port_monad.match_exn
          (fun _ ->
            Downwards_env.find_code_metadata_exn denv callee's_code_id_from_type)
          Port_monad.not_found
          (fun _ -> type_unavailable call)
          (fun callee's_code_metadata_from_type ->
            let must_be_detupled =
              call_must_be_detupled
                (Code_metadata.is_tupled callee's_code_metadata_from_type)
            in
            simplify_direct_function_call simplify_expr rebuild_expr dacc apply0
              callee's_code_id_from_type callee's_code_metadata_from_type
              callee's_code_ids_from_call_kind callee's_function_slot call
              (Code_metadata.result_arity callee's_code_metadata_from_type)
              (Code_metadata.result_types callee's_code_metadata_from_type)
              (Code_metadata.recursive callee's_code_metadata_from_type)
              must_be_detupled closure_alloc_mode_from_type func_decl_type
              down_to_up0 call inlined_forwarded_from))
      (fun _ ->
        match call with
        | Call_kind.Function_call.Direct _ -> type_unavailable call
        | Call_kind.Function_call.Indirect_unknown_arity ->
          (fun f__1 f__2 f__3 x__0 ->
            match (x__0 : _ Flambda2_types.meet_shortcut) with
            | Flambda2_types.Known_result x__1 -> f__1 x__1
            | Flambda2_types.Need_meet -> f__2 ()
            | Flambda2_types.Invalid -> f__3 ())
            (fun code_ids ->
              let args_arity = Flambda.Apply.args_arity apply0 in
              if
                Code_id.Set.for_all
                  (fun code_id ->
                    Port_monad.match_exn
                      (fun _ ->
                        Downwards_env.find_code_metadata_exn denv code_id)
                      Port_monad.not_found
                      (fun _ -> false)
                      (fun code_metadata ->
                        let params_arity =
                          Code_metadata.params_arity code_metadata
                        in
                        let is_tupled = Code_metadata.is_tupled code_metadata in
                        (not is_tupled)
                        && Flambda_arity.equal_ignoring_subkinds args_arity
                             params_arity))
                  code_ids
              then
                type_unavailable
                  (Call_kind.Function_call.indirect_known_arity
                     (Or_unknown.Known code_ids))
              else type_unavailable call)
            (fun _ -> type_unavailable call)
            (fun _ -> not_a_closure ())
            (Flambda2_types.meet_code_ids
               (Downwards_env.typing_env denv)
               callee_ty0)
        | Call_kind.Function_call.Indirect_known_arity _ ->
          type_unavailable call)
      (fun _ -> not_a_closure ())
      (Flambda2_types.meet_single_closures_entry
         (Downwards_env.typing_env denv)
         callee_ty0)
  | None -> (
    match call with
    | Call_kind.Function_call.Direct callee's_code_id ->
      Port_monad.match_exn
        (fun _ -> Downwards_env.find_code_metadata_exn denv callee's_code_id)
        Port_monad.not_found
        (fun _ -> type_unavailable call)
        (fun callee's_code_metadata ->
          simplify_direct_full_application simplify_expr rebuild_expr dacc
            apply0 None
            (Code_metadata.params_arity callee's_code_metadata)
            (Code_metadata.result_arity callee's_code_metadata)
            (Code_metadata.result_types callee's_code_metadata)
            down_to_up0 call callee's_code_metadata inlined_forwarded_from)
    | Call_kind.Function_call.Indirect_unknown_arity ->
      Misc.fatal_errorf
        "No callee provided for non-direct OCaml function call:@ %a"
        Flambda.Apply.print apply0
    | Call_kind.Function_call.Indirect_known_arity _ ->
      Misc.fatal_errorf
        "No callee provided for non-direct OCaml function call:@ %a"
        Flambda.Apply.print apply0)

type ('a, 'b) simplify_apply_shared_result =
  | Ok of 'a
  | Invalid of 'b

(** val simplify_apply_shared : Downwards_acc.t -> Flambda.Apply.t ->
    ((Downwards_acc.t, Flambda2_types.t option, Flambda.Apply.t,
    Flambda2_types.t list, Inlined_debuginfo.t option) Port_monad.tuple5,
    [ `Unarized ] Flambda_arity.t) simplify_apply_shared_result coq_M **)

let simplify_apply_shared dacc apply0 =
  let callee_ty, simplified_callee =
    match Flambda.Apply.callee apply0 with
    | Some callee ->
      let callee_ty, simplified_callee =
        Simplify_simple.simplify_simple dacc callee Name_mode.normal
      in
      Some callee_ty, Some simplified_callee
    | None -> None, None
  in
  let { S.simples = args; S.simple_tys = arg_types } =
    Simplify_simple.simplify_simples dacc (Flambda.Apply.args apply0)
  in
  let kind_mismatch = ref false in
  let () =
    List.iter2
      (fun kind_with_subkind arg_type ->
        let kind = Flambda_kind.With_subkind.kind kind_with_subkind in
        if not (Flambda_kind.equal kind (Flambda2_types.kind arg_type))
        then
          if not (Flambda_features.kind_checks ())
          then kind_mismatch := true
          else
            Misc.fatal_errorf
              "Argument kind %a from arity does not match kind from type %a \
               for application:@ %a"
              Flambda_kind.print kind Flambda2_types.print arg_type
              Flambda.Apply.print apply0
        else ())
      (Flambda_arity.unarize (Flambda.Apply.args_arity apply0))
      arg_types
  in
  if !kind_mismatch
  then
    Invalid
      (Flambda_arity.create_singletons
         (List.map Flambda_kind.With_subkind.anything
            (List.map Flambda2_types.kind arg_types)))
  else
    let inlining_state =
      Inlining_state.combine
        (Downwards_env.get_inlining_state (Downwards_acc.denv dacc))
        (Flambda.Apply.inlining_state apply0)
    in
    let inlined, inlined_forwarded_from =
      let inlined = Flambda.Apply.inlined apply0 in
      match inlined with
      | Inlined_attribute.Always_inlined _ -> inlined, None
      | Inlined_attribute.Hint_inlined -> inlined, None
      | Inlined_attribute.Forward_inlined -> (
        match
          Downwards_env.inlined_attribute_to_forward (Downwards_acc.denv dacc)
        with
        | Some labelled ->
          (fun x__0 f__1 ->
            let x__1, ~forwarded_from:x__2 = x__0 in
            f__1 x__1 x__2) labelled (fun inlined_from_env forwarded_from ->
              inlined_from_env, Some forwarded_from)
        | None -> inlined, None)
      | Inlined_attribute.Never_inlined -> inlined, None
      | Inlined_attribute.Unroll (_, _) -> inlined, None
      | Inlined_attribute.Default_inlined -> inlined, None
    in
    let apply1 =
      Flambda.Apply.create simplified_callee
        (Flambda.Apply.continuation apply0)
        (Flambda.Apply.exn_continuation apply0)
        args
        (Flambda.Apply.args_arity apply0)
        (Flambda.Apply.return_arity apply0)
        (Flambda.Apply.call_kind apply0)
        (Flambda.Apply.return_mode apply0)
        (Downwards_env.add_inlined_debuginfo (Downwards_acc.denv dacc)
           (Flambda.Apply.dbg apply0))
        inlined inlining_state
        (Flambda.Apply.probe apply0)
        (Flambda.Apply.position apply0)
        (Inlining_history.Relative.concat
           (Downwards_env.relative_history (Downwards_acc.denv dacc))
           (Flambda.Apply.relative_history apply0))
    in
    Ok (dacc, callee_ty, apply1, arg_types, inlined_forwarded_from)

(** val simplify_method_call : Downwards_acc.t -> Flambda.Apply.t ->
    Flambda2_types.t -> Call_kind.Method_kind.t -> Simple.t -> Simplified_expr.t
    down_to_up -> (Simplified_expr.t * Downwards_acc.t) coq_M **)

let simplify_method_call dacc apply0 callee_ty _ obj down_to_up0 =
  let () = fail_if_probe apply0 in
  let callee_kind = Flambda2_types.kind callee_ty in
  let () =
    if not (Flambda_kind.is_value callee_kind)
    then
      Misc.fatal_errorf "Method call with callee of wrong kind %a: %a"
        Flambda_kind.print callee_kind Flambda2_types.print callee_ty
    else ()
  in
  let apply_cont =
    match Flambda.Apply.continuation apply0 with
    | Apply_expr.Result_continuation.Return continuation -> continuation
    | Apply_expr.Result_continuation.Never_returns ->
      Misc.fatal_error "Cannot simplify a method call that never returns"
  in
  let denv = Downwards_acc.denv dacc in
  let () = Downwards_env.check_simple_is_bound denv obj in
  let dacc0, use_id0 =
    Downwards_acc.record_continuation_use dacc apply_cont
      ((fun x__1 ->
         (Continuation_use_kind.Non_inlinable { escaping = x__1 }
           : Continuation_use_kind.t))
         true)
      denv
      ((fun x__1 x__2 x__3 ->
         Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
         (Some
            (Alloc_mode.For_applications.as_type
               (Flambda.Apply.return_mode apply0)))
         (Downwards_env.machine_width denv)
         (Flambda.Apply.return_arity apply0))
  in
  let dacc1, exn_cont_use_id0 =
    Downwards_acc.record_continuation_use dacc0
      (Exn_continuation.exn_handler (Flambda.Apply.exn_continuation apply0))
      ((fun x__1 ->
         (Continuation_use_kind.Non_inlinable { escaping = x__1 }
           : Continuation_use_kind.t))
         true)
      (Downwards_acc.denv dacc0)
      ((fun x__1 x__2 x__3 ->
         Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
         None
         (Downwards_env.machine_width (Downwards_acc.denv dacc0))
         (Exn_continuation.arity (Flambda.Apply.exn_continuation apply0)))
  in
  let dacc2 =
    record_free_names_of_apply_as_used dacc1 (Some use_id0) exn_cont_use_id0
      apply0
  in
  down_to_up0 dacc2
    ((fun x__1 x__2 x__3 x__4 x__5 ->
       Simplified_expr.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)
       None apply0 (Some use_id0) exn_cont_use_id0 false)

(** val simplify_c_call : Flambda.Expr.t expr_simplifier -> Downwards_acc.t ->
    Flambda.Apply.t -> Flambda2_types.t -> Flambda2_types.t list ->
    Simplified_expr.t down_to_up -> (Simplified_expr.t * Downwards_acc.t) coq_M
    **)

let simplify_c_call simplify_expr dacc apply0 callee_ty arg_types down_to_up0 =
  let () = fail_if_probe apply0 in
  let return_arity = Flambda.Apply.return_arity apply0 in
  let callee_kind = Flambda2_types.kind callee_ty in
  let () =
    if not (Flambda_kind.is_value callee_kind)
    then
      Misc.fatal_errorf "C callees must be of kind [Value], not %a: %a"
        Flambda_kind.print callee_kind Flambda2_types.print callee_ty
    else ()
  in
  let simplified =
    Simplify_extcall.simplify_extcall dacc apply0 callee_ty arg_types
  in
  (fun f__1 f__2 f__3 x__0 ->
    match (x__0 : Simplify_extcall.t) with
    | Simplify_extcall.Unchanged { return_types = x__1 } -> f__1 x__1
    | Simplify_extcall.Specialised (x__1, x__2, x__3) -> f__2 x__1 x__2 x__3
    | Simplify_extcall.Invalid -> f__3 ())
    (fun return_types ->
      let dacc0, use_id0 =
        match Flambda.Apply.continuation apply0 with
        | Apply_expr.Result_continuation.Return apply_continuation ->
          let apply_continuation_arg_types =
            let from_arity =
              (fun x__1 x__2 x__3 ->
                Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2
                  x__3)
                (Some
                   (Alloc_mode.For_applications.as_type
                      (Flambda.Apply.return_mode apply0)))
                (Downwards_env.machine_width (Downwards_acc.denv dacc))
                return_arity
            in
            match return_types with
            | Or_unknown.Known return_types0 ->
              let () =
                assert (List.compare_lengths return_types0 from_arity = 0)
              in
              return_types0
            | Or_unknown.Unknown -> from_arity
          in
          let dacc0, use_id0 =
            Downwards_acc.record_continuation_use dacc apply_continuation
              ((fun x__1 ->
                 (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                   : Continuation_use_kind.t))
                 true)
              (Downwards_acc.denv dacc) apply_continuation_arg_types
          in
          dacc0, Some use_id0
        | Apply_expr.Result_continuation.Never_returns -> dacc, None
      in
      let dacc1, exn_cont_use_id0 =
        Downwards_acc.record_continuation_use dacc0
          (Exn_continuation.exn_handler (Flambda.Apply.exn_continuation apply0))
          ((fun x__1 ->
             (Continuation_use_kind.Non_inlinable { escaping = x__1 }
               : Continuation_use_kind.t))
             true)
          (Downwards_acc.denv dacc0)
          ((fun x__1 x__2 x__3 ->
             Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
             None
             (Downwards_env.machine_width (Downwards_acc.denv dacc0))
             (Exn_continuation.arity (Flambda.Apply.exn_continuation apply0)))
      in
      let dacc2 =
        record_free_names_of_apply_as_used dacc1 use_id0 exn_cont_use_id0 apply0
      in
      down_to_up0 dacc2
        ((fun x__1 x__2 x__3 x__4 x__5 ->
           Simplified_expr.simplified_apply ?result_arity:x__1 x__2 x__3 x__4
             x__5)
           None apply0 use_id0 exn_cont_use_id0 false))
    (fun dacc0 expr operation ->
      let down_to_up1 =
       fun dacc1 expr0 ->
        down_to_up0 dacc1 (Simplified_expr.notify_removed operation expr0)
      in
      simplify_expr dacc0 expr down_to_up1)
    (fun _ ->
      replace_apply_by_invalid dacc down_to_up0
        (Flambda.Invalid.Closure_type_was_invalid apply0))
    simplified

(** val simplify_effect_op : Downwards_acc.t -> Flambda.Apply.t ->
    Call_kind.Effect.t -> Simplified_expr.t down_to_up -> (Simplified_expr.t *
    Downwards_acc.t) coq_M **)

let simplify_effect_op dacc apply0 op down_to_up0 =
  let () = fail_if_probe apply0 in
  let denv = Downwards_acc.denv dacc in
  let op0 =
    let simplify_simple =
     fun simple ->
      let _, simple0 =
        Simplify_simple.simplify_simple dacc simple Name_mode.normal
      in
      simple0
    in
    (fun f__1 f__2 f__3 f__4 f__5 f__6 f__7 x__0 ->
      match (x__0 : Call_kind.Effect.t) with
      | Call_kind.Effect.Perform { eff = x__1 } -> f__1 x__1
      | Call_kind.Effect.Reperform
          { eff = x__1; cont = x__2; last_fiber = x__3 } ->
        f__2 x__1 x__2 x__3
      | Call_kind.Effect.With_stack
          { valuec = x__1; exnc = x__2; effc = x__3; f = x__4; arg = x__5 } ->
        f__3 x__1 x__2 x__3 x__4 x__5
      | Call_kind.Effect.With_stack_preemptible
          { valuec = x__1;
            exnc = x__2;
            effc = x__3;
            handle_tick = x__4;
            f = x__5;
            arg = x__6
          } ->
        f__4 x__1 x__2 x__3 x__4 x__5 x__6
      | Call_kind.Effect.Continue { cont = x__1; value = x__2 } ->
        f__5 x__1 x__2
      | Call_kind.Effect.Discontinue { cont = x__1; exn = x__2 } ->
        f__6 x__1 x__2
      | Call_kind.Effect.Discontinue_with_backtrace
          { cont = x__1; exn = x__2; bt = x__3 } ->
        f__7 x__1 x__2 x__3)
      (fun eff -> Call_kind.Effect.perform (simplify_simple eff))
      (fun eff cont last_fiber ->
        Call_kind.Effect.reperform (simplify_simple eff) (simplify_simple cont)
          (simplify_simple last_fiber))
      (fun valuec exnc effc f arg ->
        Call_kind.Effect.with_stack (simplify_simple valuec)
          (simplify_simple exnc) (simplify_simple effc) (simplify_simple f)
          (simplify_simple arg))
      (fun valuec exnc effc handle_tick f arg ->
        Call_kind.Effect.with_stack_preemptible (simplify_simple valuec)
          (simplify_simple exnc) (simplify_simple effc)
          (simplify_simple handle_tick)
          (simplify_simple f) (simplify_simple arg))
      (fun cont value ->
        Call_kind.Effect.continue (simplify_simple cont) (simplify_simple value))
      (fun cont exn ->
        Call_kind.Effect.discontinue (simplify_simple cont)
          (simplify_simple exn))
      (fun cont exn bt ->
        Call_kind.Effect.discontinue_with_backtrace (simplify_simple cont)
          (simplify_simple exn) (simplify_simple bt))
      op
  in
  let apply1 = Flambda.Apply.with_call_kind apply0 (Call_kind.effect_ op0) in
  let dacc0, use_id0 =
    match Flambda.Apply.continuation apply1 with
    | Apply_expr.Result_continuation.Return continuation ->
      let dacc0, use_id0 =
        Downwards_acc.record_continuation_use dacc continuation
          ((fun x__1 ->
             (Continuation_use_kind.Non_inlinable { escaping = x__1 }
               : Continuation_use_kind.t))
             true)
          denv
          ((fun x__1 x__2 x__3 ->
             Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
             (Some
                (Alloc_mode.For_applications.as_type
                   (Flambda.Apply.return_mode apply1)))
             (Downwards_env.machine_width denv)
             (Flambda.Apply.return_arity apply1))
      in
      dacc0, Some use_id0
    | Apply_expr.Result_continuation.Never_returns -> dacc, None
  in
  let dacc1, exn_cont_use_id0 =
    Downwards_acc.record_continuation_use dacc0
      (Exn_continuation.exn_handler (Flambda.Apply.exn_continuation apply1))
      ((fun x__1 ->
         (Continuation_use_kind.Non_inlinable { escaping = x__1 }
           : Continuation_use_kind.t))
         true)
      (Downwards_acc.denv dacc0)
      ((fun x__1 x__2 x__3 ->
         Flambda2_types.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
         None
         (Downwards_env.machine_width (Downwards_acc.denv dacc0))
         (Exn_continuation.arity (Flambda.Apply.exn_continuation apply1)))
  in
  let dacc2 =
    record_free_names_of_apply_as_used dacc1 use_id0 exn_cont_use_id0 apply1
  in
  down_to_up0 dacc2
    ((fun x__1 x__2 x__3 x__4 x__5 ->
       Simplified_expr.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)
       None apply1 use_id0 exn_cont_use_id0 false)

(** val simplify_apply : Flambda.Expr.t expr_simplifier -> Simplified_expr.t
    rebuild -> Downwards_acc.t -> Flambda.Apply.t -> Simplified_expr.t
    down_to_up -> (Simplified_expr.t * Downwards_acc.t) coq_M **)

let simplify_apply simplify_expr rebuild_expr dacc apply0 down_to_up0 =
  match simplify_apply_shared dacc apply0 with
  | Ok a ->
    let dacc0, callee_ty, apply1, arg_types, inlined_forwarded_from = a in
    (fun f__1 f__2 f__3 f__4 x__0 ->
      match (x__0 : Call_kind.t) with
      | Call_kind.Function { function_call = x__1 } -> f__1 x__1
      | Call_kind.Method { kind = x__1; obj = x__2 } -> f__2 x__1 x__2
      | Call_kind.C_call
          { needs_caml_c_call = x__1;
            is_c_builtin = x__2;
            effects = x__3;
            coeffects = x__4
          } ->
        f__3 x__1 x__2 x__3 x__4
      | Call_kind.Effect x__1 -> f__4 x__1)
      (fun function_call ->
        simplify_function_call simplify_expr rebuild_expr dacc0 apply1 callee_ty
          function_call down_to_up0 inlined_forwarded_from)
      (fun kind obj ->
        let callee_ty0 =
          match callee_ty with
          | Some callee_ty0 -> callee_ty0
          | None ->
            Misc.fatal_errorf "No callee provided for method call:@ %a"
              Flambda.Apply.print apply1
        in
        simplify_method_call dacc0 apply1 callee_ty0 kind obj down_to_up0)
      (fun _ _ _ _ ->
        let callee_ty0 =
          match callee_ty with
          | Some callee_ty0 -> callee_ty0
          | None ->
            Misc.fatal_errorf "No callee provided for C call:@ %a"
              Flambda.Apply.print apply1
        in
        simplify_c_call simplify_expr dacc0 apply1 callee_ty0 arg_types
          down_to_up0)
      (fun op -> simplify_effect_op dacc0 apply1 op down_to_up0)
      (Flambda.Apply.call_kind apply1)
  | Invalid args_arity ->
    replace_apply_by_invalid dacc down_to_up0
      (Flambda.Invalid.Application_argument_kind_mismatch (args_arity, apply0))
