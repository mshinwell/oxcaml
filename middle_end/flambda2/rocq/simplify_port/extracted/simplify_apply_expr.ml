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

(** val fail_if_probe : Apply.t -> unit coq_M **)

let fail_if_probe apply0 =
  match Apply.probe apply0 with
  | Some _ ->
    Misc.fatal_errorf
      "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
       always be direct applications of an OCaml function:@ %a"
      Apply.print apply0
  | None -> ()

(** val record_free_names_of_apply_as_used0 : Apply.t -> Apply_cont_rewrite_id.t
    option -> Apply_cont_rewrite_id.t -> Flow.Acc.t -> Flow.Acc.t coq_M **)

let record_free_names_of_apply_as_used0 apply0 use_id0 exn_cont_use_id0
    data_flow =
  let data_flow0 =
    Flow.Acc.add_used_in_current_handler
      (Apply.free_names_without_exn_continuation apply0)
      data_flow
  in
  let exn_cont = Apply.exn_continuation apply0 in
  let result_cont =
    let continuation = Apply.continuation apply0 in
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
    (Apply.return_arity apply0)
    data_flow0

(** val record_free_names_of_apply_as_used : DA.t -> Apply_cont_rewrite_id.t
    option -> Apply_cont_rewrite_id.t -> Apply.t -> DA.t coq_M **)

let record_free_names_of_apply_as_used dacc use_id0 exn_cont_use_id0 apply0 =
  DA.map_flow_acc dacc
    (record_free_names_of_apply_as_used0 apply0 use_id0 exn_cont_use_id0)

(** val loopify_decision_for_call : DA.t -> Apply.t -> Loopify_state.t coq_M **)

let loopify_decision_for_call dacc apply0 =
  let denv = DA.denv dacc in
  if Are_rebuilding_terms.do_not_rebuild_terms (DE.are_rebuilding_terms denv)
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
        let tenv = DE.typing_env denv in
        let canon =
         fun simple ->
          Simple.without_coercion
            ((fun x__1 x__2 x__3 x__4 ->
               TE.get_canonical_simple_exn x__1 ?min_name_mode:x__2
                 ?name_mode_of_existing_simple:x__3 x__4)
               tenv None None simple)
        in
        match Apply.callee apply0 with
        | Some callee ->
          if
            Simple.equal (canon (Simple.var my_closure)) (canon callee)
            && (match Apply.continuation apply0 with
              | Apply_expr.Result_continuation.Return apply_return_continuation
                ->
                Continuation.equal apply_return_continuation return_continuation
              | Apply_expr.Result_continuation.Never_returns -> true)
            && Exn_continuation.equal
                 (Apply.exn_continuation apply0)
                 (Exn_continuation.create exn_continuation [])
          then DE.loopify_state denv
          else Loopify_state.do_not_loopify
        | None -> Loopify_state.do_not_loopify)
      (DE.closure_info denv)

(** val simplify_self_tail_call : DA.t -> Apply.t -> Continuation.t -> SE.t
    Simplify_common.down_to_up -> (SE.t * DA.t) coq_M **)

let simplify_self_tail_call dacc apply0 self_cont down_to_up0 =
  Simplify_apply_cont_expr.simplify_apply_cont dacc
    ((fun x__1 x__2 x__3 x__4 ->
       Apply_cont_expr.create ?trap_action:x__1 x__2 x__3 x__4)
       None self_cont (Apply.args apply0) (Apply.dbg apply0))
    down_to_up0

(** val simplify_direct_tuple_application : Expr.t
    Simplify_common.expr_simplifier -> DA.t -> Apply.t -> Code_id.t ->
    Code_metadata.t -> SE.t Simplify_common.down_to_up -> (SE.t * DA.t) coq_M **)

let simplify_direct_tuple_application simplify_expr dacc apply0 callee's_code_id
    callee's_code_metadata down_to_up0 =
  let dbg = Apply.dbg apply0 in
  let tuple_size =
    Flambda_arity.cardinal_unarized
      (Code_metadata.params_arity callee's_code_metadata)
  in
  let tuple_arg, over_application_args =
    match Apply.args apply0 with
    | [] ->
      Misc.fatal_errorf "Empty argument list for direct tuple application:@ %a"
        Apply.print apply0
    | tuple :: others -> tuple, others
  in
  let vars_and_fields =
    List.init tuple_size (fun field ->
        ( (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
            None "tuple_field" K.value,
          Flambda_debug_uid.none,
          Simplify_common.project_tuple
            (DE.machine_width (DA.denv dacc))
            dbg tuple_size field tuple_arg ))
  in
  let args_arity =
    let tuple_arity =
      Flambda_arity.create_singletons
        (List.init tuple_size (fun _ -> K.With_subkind.any_value))
    in
    let over_application_arity =
      Flambda_arity.partially_apply (Apply.args_arity apply0) 1
    in
    Flambda_arity.concat tuple_arity over_application_arity
  in
  let apply1 =
    Apply.with_args apply0
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
    | [] -> Expr.create_apply apply1
    | _ :: _ ->
      Simplify_common.split_direct_over_application apply1 callee's_code_id
        callee's_code_metadata
  in
  let expr =
    List.fold_right
      (fun var_and_field body ->
        let v, v_duid, defining_expr = var_and_field in
        let var_bind = Bound_var.create v v_duid Name_mode.normal in
        Expr.create_let
          (Let.create
             (Bound_pattern.singleton var_bind)
             defining_expr body Or_unknown.Unknown))
      vars_and_fields apply_expr
  in
  simplify_expr dacc expr down_to_up0

(** val update_direct_call_benefit : SE.t -> Call_kind.Function_call.t ->
    Code_metadata.t -> Simplified_expr.t coq_M **)

let update_direct_call_benefit expr original_call callee's_code_metadata =
  match original_call with
  | Call_kind.Function_call.Direct old_code_id ->
    let code_id = Code_metadata.code_id callee's_code_metadata in
    if Code_id.equal code_id old_code_id
    then expr
    else SE.notify_removed Removed_operations.updated_direct_call expr
  | Call_kind.Function_call.Indirect_unknown_arity ->
    SE.notify_removed Removed_operations.direct_call_of_indirect expr
  | Call_kind.Function_call.Indirect_known_arity _ ->
    SE.notify_removed Removed_operations.direct_call_of_indirect expr

(** val rebuild_apply : Simplified_expr.simplified_apply_ -> UA.t ->
    Simplify_common.after_rebuild -> (RE.t * UA.t) coq_M **)

let rebuild_apply simplified_apply uacc after_rebuild =
  let { Simplified_expr.apply = apply0;
        Simplified_expr.use_id = use_id0;
        Simplified_expr.exn_cont_use_id = exn_cont_use_id0;
        Simplified_expr.result_arity = result_arity0;
        Simplified_expr.is_cold = is_cold0
      } =
    simplified_apply
  in
  let apply1 =
    Simplify_common.update_exn_continuation_extra_args uacc exn_cont_use_id0
      apply0
  in
  let erase_callee = false in
  let apply2 = if erase_callee then Apply.erase_callee apply1 else apply1 in
  let uacc0, expr =
    EB.rewrite_fixed_arity_apply uacc use_id0 is_cold0
      (Flambda_arity.unarize_t result_arity0)
      apply2
  in
  after_rebuild expr uacc0

type inlining_decision =
  | Do_not_inline of { erase_attribute : bool }
  | Inline of DA.t * Expr.t

(** val simplify_direct_full_application : Expr.t
    Simplify_common.expr_simplifier -> SE.t Simplify_common.rebuild -> DA.t ->
    Apply.t -> T.Function_type.t option -> [ `Complex ] Flambda_arity.t ->
    [ `Complex ] Flambda_arity.t -> Result_types.t Or_unknown_or_bottom.t ->
    SE.t Simplify_common.down_to_up -> Call_kind.Function_call.t ->
    Code_metadata.t -> Inlined_debuginfo.t option -> (SE.t * DA.t) coq_M **)

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
            (DE.are_rebuilding_terms (DA.denv dacc))
        then
          Inlining_report.record_decision_at_call_site_for_known_function
            (DE.inlining_history_tracker (DA.denv dacc))
            unrolling_depth apply0 Inlining_report.Pass.Before_simplify
            (Code_metadata.absolute_history callee's_code_metadata)
            (DA.are_rebuilding_terms dacc)
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
            DA.map_denv dacc (DE.record_inlining_decision apply0 decision)
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
            Inlined_attribute.with_use_info (Apply.inlined apply0)
              Inlined_attribute.Use_info.Unused_because_of_call_site_decision
        in
        Apply.with_inlined_attribute apply0 inlined0
      in
      match loopify_decision_for_call dacc apply1 with
      | Loopify_state.Do_not_loopify ->
        let dacc0, use_id0, result_continuation =
          let result_continuation = Apply.continuation apply1 in
          match result_continuation with
          | Apply_expr.Result_continuation.Return apply_return_continuation -> (
            match result_types with
            | Or_unknown_or_bottom.Unknown ->
              let env_at_use = DA.denv dacc in
              let env_at_use0 =
                if Code_metadata.cold callee's_code_metadata
                then DE.mark_as_cold env_at_use
                else env_at_use
              in
              let dacc0, use_id0 =
                DA.record_continuation_use dacc apply_return_continuation
                  ((fun x__1 ->
                     (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                       : Continuation_use_kind.t))
                     true)
                  env_at_use0
                  ((fun x__1 x__2 x__3 ->
                     T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
                     (Some
                        (Alloc_mode.For_applications.as_type
                           (Apply.return_mode apply1)))
                     (DE.machine_width (DA.denv dacc))
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
                        result_types0 Apply.print apply1
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
                        result_types0 Apply.print apply1
                    else ()
                  in
                  let denv = DA.denv dacc in
                  let denv0 =
                    (fun x__1 x__2 x__3 x__4 x__5 ->
                      DE.add_parameters_with_unknown_types x__1
                        ?alloc_modes:x__2 ?name_mode:x__3 x__4 x__5)
                      false None (Some Name_mode.in_types) denv params
                  in
                  let params0 = Bound_parameters.to_list params in
                  let results0 = Bound_parameters.to_list results in
                  let denv1 =
                    let args = Apply.args apply1 in
                    let () = assert (List.compare_lengths params0 args = 0) in
                    List.fold_left2
                      (fun denv1 param arg ->
                        DE.add_equation_on_variable denv1 (BP.var param)
                          (T.alias_type_of
                             (K.With_subkind.kind (BP.kind param))
                             arg))
                      denv0 params0 args
                  in
                  let result_arity1 = Flambda_arity.unarize result_arity0 in
                  let denv2 =
                    List.fold_left2
                      (fun denv2 kind result ->
                        let result_var, result_uid = BP.var_and_uid result in
                        DE.add_variable denv2
                          (VB.create result_var result_uid NM.in_types)
                          ((fun x__1 x__2 x__3 ->
                             T.unknown_with_subkind ?alloc_mode:x__1 x__2 x__3)
                             (Some
                                (Alloc_mode.For_applications.as_type
                                   (Apply.return_mode apply1)))
                             (DE.machine_width denv2) kind))
                      denv1 result_arity1 results0
                  in
                  let denv3 =
                    DE.extend_typing_environment denv2 env_extension
                  in
                  let arg_types =
                    List.map2
                      (fun kind result_var ->
                        T.alias_type_of (K.With_subkind.kind kind)
                          (BP.simple result_var))
                      result_arity1 results0
                  in
                  let env_at_use =
                    if Code_metadata.cold callee's_code_metadata
                    then DE.mark_as_cold denv3
                    else denv3
                  in
                  let dacc0, use_id0 =
                    DA.record_continuation_use dacc apply_return_continuation
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
        let env_at_use = DA.denv dacc0 in
        let env_at_use0 =
          if Code_metadata.cold callee's_code_metadata
          then DE.mark_as_cold env_at_use
          else env_at_use
        in
        let dacc1, exn_cont_use_id0 =
          DA.record_continuation_use dacc0
            (Exn_continuation.exn_handler (Apply.exn_continuation apply1))
            ((fun x__1 ->
               (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                 : Continuation_use_kind.t))
               true)
            env_at_use0
            ((fun x__1 x__2 x__3 ->
               T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
               None
               (DE.machine_width (DA.denv dacc0))
               (Exn_continuation.arity (Apply.exn_continuation apply1)))
        in
        let apply2 = Apply.with_continuation apply1 result_continuation in
        let dacc2 =
          record_free_names_of_apply_as_used dacc1 use_id0 exn_cont_use_id0
            apply2
        in
        let expr =
          (fun x__1 x__2 x__3 x__4 x__5 ->
            SE.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)
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
          SE.notify_removed Removed_operations.call simplified_body0
        in
        let simplified_body2 =
          if is_cold0
          then SE.mark_as_cold simplified_body1
          else simplified_body1
        in
        down_to_up0 dacc1 simplified_body2
      in
      simplify_expr dacc0 inlined0 down_to_up1)
    inlined

type applied_value =
  | Const of Reg_width_const.t
  | Symbol of Symbol.t
  | In_closure of
      { var : Variable.t;
        value : Simple.t;
        value_slot : Value_slot.t
      }

(** val simplify_direct_partial_application : Expr.t
    Simplify_common.expr_simplifier -> DA.t -> Apply.t -> Code_id.t ->
    Code_metadata.t -> Function_slot.t -> [ `Complex ] Flambda_arity.t ->
    Alloc_mode.For_types.t list -> [ `Complex ] Flambda_arity.t -> [ `Complex ]
    Flambda_arity.t -> Recursive.t -> SE.t Simplify_common.down_to_up ->
    Call_kind.Function_call.t -> Alloc_mode.For_types.t ->
    First_complex_local_param.t -> (SE.t * DA.t) coq_M **)

let simplify_direct_partial_application simplify_expr dacc apply0
    callee's_code_id callee's_code_metadata callee's_function_slot param_arity
    param_modes args_arity result_arity0 recursive down_to_up0 original_call
    closure_alloc_mode_from_type first_complex_local_param =
  let () = fail_if_probe apply0 in
  let args = Apply.args apply0 in
  let dbg = Apply.dbg apply0 in
  let apply_continuation =
    match Apply.continuation apply0 with
    | Apply_expr.Result_continuation.Return continuation -> continuation
    | Apply_expr.Result_continuation.Never_returns ->
      Misc.fatal_error
        "cannot simplify a partial application that never returns"
  in
  let () =
    match Apply.inlined apply0 with
    | Inlined_attribute.Always_inlined _ ->
      Location.prerr_warning
        (Debuginfo.to_location dbg)
        (Warnings.Inlining_impossible
           (Inlining_helpers.inlined_attribute_on_partial_application_msg
              Inlining_helpers.Inlined))
    | Inlined_attribute.Hint_inlined -> ()
    | Inlined_attribute.Forward_inlined -> ()
    | Inlined_attribute.Never_inlined ->
      Location.prerr_warning
        (Debuginfo.to_location dbg)
        (Warnings.Inlining_impossible
           (Inlining_helpers.inlined_attribute_on_partial_application_msg
              Inlining_helpers.Inlined))
    | Inlined_attribute.Unroll (_, _) ->
      Location.prerr_warning
        (Debuginfo.to_location dbg)
        (Warnings.Inlining_impossible
           (Inlining_helpers.inlined_attribute_on_partial_application_msg
              Inlining_helpers.Unrolled))
    | Inlined_attribute.Default_inlined -> ()
  in
  let num_non_unarized_params = Flambda_arity.num_params param_arity in
  let num_non_unarized_args = Flambda_arity.num_params args_arity in
  let () = assert (num_non_unarized_params > num_non_unarized_args) in
  let remaining_param_arity =
    Flambda_arity.partially_apply param_arity num_non_unarized_args
  in
  let applied_unarized_args, _ =
    Misc.Stdlib.List.map2_prefix
      (fun arg kind -> arg, kind)
      args
      (Flambda_arity.unarize param_arity)
  in
  let wrapper_var =
    (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
      None "partial_app" K.value
  in
  let wrapper_var_duid = Flambda_debug_uid.none in
  let compilation_unit = Current_unit.get_cu_exn () in
  let wrapper_function_slot =
    Function_slot.create compilation_unit "partial_app_closure"
      (Function_slot.size_from_arity
         (num_non_unarized_params - num_non_unarized_args)
         false)
  in
  let new_closure_alloc_mode_and_first_complex_local_param =
    match first_complex_local_param with
    | First_complex_local_param.Index index ->
      if num_non_unarized_args <= index
      then
        let alloc_region =
          (fun f__1 f__2 x__0 ->
            match (x__0 : Alloc_mode.For_applications.t) with
            | Alloc_mode.For_applications.Not_alloc_stack
                { alloc_region = x__1 } ->
              f__1 x__1
            | Alloc_mode.For_applications.Maybe_alloc_stack
                { alloc_region = x__1; region = x__2; ghost_region = x__3 } ->
              f__2 x__1 x__2 x__3)
            (fun alloc_region -> alloc_region)
            (fun alloc_region _ _ -> alloc_region)
            (Apply_expr.return_mode apply0)
        in
        Or_bottom.Ok
          ( Alloc_mode.For_allocations.heap alloc_region,
            First_complex_local_param.Index (index - num_non_unarized_args) )
      else
        (fun f__1 f__2 x__0 ->
          match (x__0 : Alloc_mode.For_applications.t) with
          | Alloc_mode.For_applications.Not_alloc_stack { alloc_region = x__1 }
            ->
            f__1 x__1
          | Alloc_mode.For_applications.Maybe_alloc_stack
              { alloc_region = x__1; region = x__2; ghost_region = x__3 } ->
            f__2 x__1 x__2 x__3)
          (fun _ -> Or_bottom.Bottom)
          (fun alloc_region region _ ->
            Or_bottom.Ok
              ( Alloc_mode.For_allocations.local alloc_region region,
                First_complex_local_param.Index 0 ))
          (Apply_expr.return_mode apply0)
    | First_complex_local_param.Never_partially_applied ->
      Misc.fatal_errorf
        "Partial application of %a, whose code metadata states that it is \
         never partially applied"
        Apply.print apply0
  in
  let expr, dacc0 =
    match new_closure_alloc_mode_and_first_complex_local_param with
    | Or_bottom.Ok p ->
      let new_closure_alloc_mode, first_complex_local_param0 = p in
      let () =
        match closure_alloc_mode_from_type with
        | Alloc_mode.For_types.Heap -> ()
        | Alloc_mode.For_types.Local ->
          (fun f__1 f__2 x__0 ->
            match (x__0 : Alloc_mode.For_allocations.t) with
            | Alloc_mode.For_allocations.Heap { alloc_region = x__1 } ->
              f__1 x__1
            | Alloc_mode.For_allocations.Local
                { alloc_region = x__1; region = x__2 } ->
              f__2 x__1 x__2)
            (fun _ ->
              Misc.fatal_errorf
                "New closure alloc mode cannot be [Not_alloc_stack] when \
                 existing closure alloc mode is [Local]: direct partial \
                 application:@ %a"
                Apply.print apply0)
            (fun _ _ -> ())
            new_closure_alloc_mode
        | Alloc_mode.For_types.Heap_or_local -> ()
      in
      let result_mode = Code_metadata.result_mode callee's_code_metadata in
      let ( wrapper_taking_remaining_args,
            wrapper_alloc_mode,
            dacc0,
            code_id,
            code ) =
        let return_continuation =
          (fun x__1 x__2 x__3 -> Continuation.create ?sort:x__1 ?name:x__2 x__3)
            (Some Continuation.Sort.Return) None ()
        in
        let remaining_params =
          Bound_parameters.create
            (List.map
               (fun kind ->
                 let param =
                   (fun x__1 x__2 x__3 ->
                     Variable.create ?user_visible:x__1 x__2 x__3)
                     None "param" (KS.kind kind)
                 in
                 let param_duid = Flambda_debug_uid.none in
                 Bound_parameter.create param kind param_duid)
               (Flambda_arity.unarize remaining_param_arity))
        in
        let _, remaining_params_alloc_modes =
          Misc.Stdlib.List.split_at (List.length args) param_modes
        in
        let mk_value_slot =
         fun kind ->
          let is_always_immediate =
            (fun f__1
              f__2
              f__3
              f__4
              f__5
              f__6
              f__7
              f__8
              f__9
              f__10
              f__11
              f__12
              f__13
              f__14
              f__15
              f__16
              f__17
              f__18
              f__19
              f__20
              f__21
              f__22
              f__23
              f__24
              f__25
              f__26
              f__27
              f__28
              f__29
              x__0
            ->
              match (x__0 : K.With_subkind.Non_null_value_subkind.t) with
              | K.With_subkind.Non_null_value_subkind.Anything -> f__1 ()
              | K.With_subkind.Non_null_value_subkind.Boxed_float32 -> f__2 ()
              | K.With_subkind.Non_null_value_subkind.Boxed_float -> f__3 ()
              | K.With_subkind.Non_null_value_subkind.Boxed_int32 -> f__4 ()
              | K.With_subkind.Non_null_value_subkind.Boxed_int64 -> f__5 ()
              | K.With_subkind.Non_null_value_subkind.Boxed_nativeint -> f__6 ()
              | K.With_subkind.Non_null_value_subkind.Boxed_vec128 -> f__7 ()
              | K.With_subkind.Non_null_value_subkind.Boxed_vec256 -> f__8 ()
              | K.With_subkind.Non_null_value_subkind.Boxed_vec512 -> f__9 ()
              | K.With_subkind.Non_null_value_subkind.Boxed_mask -> f__10 ()
              | K.With_subkind.Non_null_value_subkind.Tagged_immediate ->
                f__11 ()
              | K.With_subkind.Non_null_value_subkind.Variant
                  { consts = x__1; non_consts = x__2 } ->
                f__12 x__1 x__2
              | K.With_subkind.Non_null_value_subkind.Float_block
                  { num_fields = x__1 } ->
                f__13 x__1
              | K.With_subkind.Non_null_value_subkind.Float_array -> f__14 ()
              | K.With_subkind.Non_null_value_subkind.Immediate_array ->
                f__15 ()
              | K.With_subkind.Non_null_value_subkind.Value_array -> f__16 ()
              | K.With_subkind.Non_null_value_subkind.Generic_array -> f__17 ()
              | K.With_subkind.Non_null_value_subkind.Unboxed_float32_array ->
                f__18 ()
              | K.With_subkind.Non_null_value_subkind.Untagged_int_array ->
                f__19 ()
              | K.With_subkind.Non_null_value_subkind.Untagged_int8_array ->
                f__20 ()
              | K.With_subkind.Non_null_value_subkind.Untagged_int16_array ->
                f__21 ()
              | K.With_subkind.Non_null_value_subkind.Unboxed_int32_array ->
                f__22 ()
              | K.With_subkind.Non_null_value_subkind.Unboxed_int64_array ->
                f__23 ()
              | K.With_subkind.Non_null_value_subkind.Unboxed_nativeint_array ->
                f__24 ()
              | K.With_subkind.Non_null_value_subkind.Unboxed_vec128_array ->
                f__25 ()
              | K.With_subkind.Non_null_value_subkind.Unboxed_vec256_array ->
                f__26 ()
              | K.With_subkind.Non_null_value_subkind.Unboxed_vec512_array ->
                f__27 ()
              | K.With_subkind.Non_null_value_subkind.Unboxed_mask_array ->
                f__28 ()
              | K.With_subkind.Non_null_value_subkind.Unboxed_product_array ->
                f__29 ())
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> true)
              (fun _ _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (fun _ -> false)
              (K.With_subkind.non_null_value_subkind kind)
          in
          Value_slot.create compilation_unit "arg" is_always_immediate
            (K.With_subkind.kind kind)
        in
        let applied_value0 =
         fun value_and_kind ->
          let value, kind = value_and_kind in
          Simple.pattern_match' value
            (fun var _ ->
              (fun (x__1, x__2, x__3) ->
                In_closure { var = x__1; value = x__2; value_slot = x__3 })
                (var, value, mk_value_slot kind))
            (fun symbol coercion ->
              if Coercion.is_id coercion
              then Symbol symbol
              else
                let var =
                  (fun x__1 x__2 x__3 ->
                    Variable.create ?user_visible:x__1 x__2 x__3)
                    None "symbol" K.value
                in
                let () =
                  if not (K.equal (K.With_subkind.kind kind) K.value)
                  then
                    Misc.fatal_errorf
                      "Simple %a which is a symbol should be of kind Value"
                      Simple.print value
                  else ()
                in
                (fun (x__1, x__2, x__3) ->
                  In_closure { var = x__1; value = x__2; value_slot = x__3 })
                  (var, value, mk_value_slot kind))
            (fun const -> Const const)
        in
        let applied_callee =
          match Apply.callee apply0 with
          | Some callee ->
            Some (applied_value0 (callee, K.With_subkind.any_value))
          | None -> None
        in
        let applied_unarized_args0 =
          List.map applied_value0 applied_unarized_args
        in
        let applied_values =
          match applied_callee with
          | Some applied_callee0 -> applied_callee0 :: applied_unarized_args0
          | None -> applied_unarized_args0
        in
        let contains_no_escaping_local_allocs =
          match result_mode with
          | Lambda.Maybe_alloc_stack -> false
          | Lambda.Not_alloc_stack -> true
        in
        let my_closure =
          (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
            None "my_closure" K.value
        in
        let my_alloc_mode =
          if contains_no_escaping_local_allocs
          then
            Alloc_mode.For_applications.not_alloc_stack
              ((fun x__1 x__2 x__3 ->
                 Variable.create ?user_visible:x__1 x__2 x__3)
                 None "my_alloc_region" K.region)
          else
            Alloc_mode.For_applications.maybe_alloc_stack
              ((fun x__1 x__2 x__3 ->
                 Variable.create ?user_visible:x__1 x__2 x__3)
                 None "my_alloc_region" K.region)
              ((fun x__1 x__2 x__3 ->
                 Variable.create ?user_visible:x__1 x__2 x__3)
                 None "my_region" K.region)
              ((fun x__1 x__2 x__3 ->
                 Variable.create ?user_visible:x__1 x__2 x__3)
                 None "my_ghost_region" K.region)
        in
        let my_depth =
          (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
            None "my_depth" K.rec_info
        in
        let exn_continuation =
          Exn_continuation.without_extra_args (Apply.exn_continuation apply0)
        in
        let call_kind = Call_kind.direct_function_call callee's_code_id in
        let body, cost_metrics_of_body, free_names =
          let arg =
           fun x ->
            (fun f__1 f__2 f__3 x__0 ->
              match x__0 with
              | Const x__1 -> f__1 x__1
              | Symbol x__1 -> f__2 x__1
              | In_closure { var = x__1; value = x__2; value_slot = x__3 } ->
                f__3 x__1 x__2 x__3)
              (fun const -> Simple.const const)
              (fun symbol -> Simple.symbol symbol)
              (fun var _ _ -> Simple.var var)
              x
          in
          let callee = Option.map arg applied_callee in
          let args0 =
            List.map arg applied_unarized_args0
            @ Bound_parameters.simples remaining_params
          in
          let inlined = Inlined_attribute.forward_inlined () in
          let full_application =
            Apply.create callee
              (Apply_expr.Result_continuation.Return return_continuation)
              exn_continuation args0 param_arity result_arity0 call_kind
              my_alloc_mode dbg inlined
              (Apply.inlining_state apply0)
              None Apply_expr.Position.Normal Inlining_history.Relative.empty
          in
          let cost_metrics =
            Cost_metrics.from_size (Code_size.apply full_application)
          in
          List.fold_left
            (fun acc applied_value1 ->
              let expr, cost_metrics0, free_names = acc in
              (fun f__1 f__2 f__3 x__0 ->
                match x__0 with
                | Const x__1 -> f__1 x__1
                | Symbol x__1 -> f__2 x__1
                | In_closure { var = x__1; value = x__2; value_slot = x__3 } ->
                  f__3 x__1 x__2 x__3)
                (fun _ -> expr, cost_metrics0, free_names)
                (fun _ -> expr, cost_metrics0, free_names)
                (fun var _ value_slot ->
                  let arg0 =
                    VB.create var Flambda_debug_uid.none Name_mode.normal
                  in
                  let prim =
                    P.Unary
                      ( (fun (x__1, x__2) ->
                          (P.Project_value_slot
                             { project_from = x__1; value_slot = x__2 }
                            : P.unary_primitive))
                          (wrapper_function_slot, value_slot),
                        Simple.var my_closure )
                  in
                  let machine_width = DE.machine_width (DA.denv dacc) in
                  let cost_metrics_of_defining_expr =
                    Cost_metrics.from_size (Code_size.prim machine_width prim)
                  in
                  let free_names0 =
                    NO.add_value_slot_in_projection free_names value_slot
                      NM.normal
                  in
                  let expr0 =
                    Expr.create_let
                      (Let.create
                         (Bound_pattern.singleton arg0)
                         (Named.create_prim prim dbg)
                         expr Or_unknown.Unknown)
                  in
                  ( expr0,
                    Cost_metrics.( + ) cost_metrics0
                      (Cost_metrics.increase_due_to_let_expr false
                         cost_metrics_of_defining_expr),
                    free_names0 ))
                applied_value1)
            ( Expr.create_apply full_application,
              cost_metrics,
              NO.without_names_or_continuations
                (Apply.free_names full_application) )
            (List.rev applied_values)
        in
        let params_and_body =
          Function_params_and_body.create return_continuation
            (Exn_continuation.exn_handler exn_continuation)
            remaining_params body Or_unknown.Unknown my_closure my_alloc_mode
            my_depth
        in
        let name =
          Function_slot.to_string callee's_function_slot ^ "_partial"
        in
        let absolute_history, relative_history =
          Inlining_history.Tracker.fundecl dbg Inlining_history.Relative.empty
            name
            (DE.inlining_history_tracker (DA.denv dacc))
        in
        let code_id = Code_id.create name dbg (Current_unit.get_cu_exn ()) in
        let code =
          let code =
            Code.create params_and_body free_names code_id None
              remaining_param_arity remaining_params_alloc_modes
              first_complex_local_param0 result_arity0
              Or_unknown_or_bottom.Unknown result_mode true
              Inline_attribute.Default_inline Lambda.Default_zero_alloc
              Poll_attribute.Default Lambda.Default_regalloc
              Lambda.Default_regalloc_params false false false recursive
              cost_metrics_of_body
              (DE.inlining_arguments (DA.denv dacc))
              dbg false
              (Function_params_and_body.is_my_closure_used params_and_body)
              Function_decl_inlining_decision_type.Stub absolute_history
              relative_history Loopify_attribute.Never_loopify
          in
          Static_const_or_code.create_code code
        in
        let function_decls =
          Function_declarations.create
            (Function_slot.Lmap.singleton wrapper_function_slot
               ((fun (x__1, x__2) ->
                  (Function_declarations.Code_id
                     { code_id = x__1; only_full_applications = x__2 }
                    : Function_declarations.code_id_in_function_declaration))
                  (code_id, false)))
        in
        let value_slots =
          Value_slot.Map.of_list
            (List.filter_map
               (fun value ->
                 (fun f__1 f__2 f__3 x__0 ->
                   match x__0 with
                   | Const x__1 -> f__1 x__1
                   | Symbol x__1 -> f__2 x__1
                   | In_closure { var = x__1; value = x__2; value_slot = x__3 }
                     ->
                     f__3 x__1 x__2 x__3)
                   (fun _ -> None)
                   (fun _ -> None)
                   (fun _ value0 value_slot -> Some (value_slot, value0))
                   value)
               applied_values)
        in
        ( Set_of_closures.create value_slots dbg function_decls,
          new_closure_alloc_mode,
          dacc,
          code_id,
          code )
      in
      let apply_cont =
        (fun x__1 x__2 x__3 x__4 ->
          Apply_cont.create ?trap_action:x__1 x__2 x__3 x__4)
          None apply_continuation
          (Simple.var wrapper_var :: [])
          dbg
      in
      let expr =
        let wrapper_var0 =
          VB.create wrapper_var wrapper_var_duid Name_mode.normal
        in
        let bound_vars = wrapper_var0 :: [] in
        let bound = Bound_pattern.set_of_closures bound_vars in
        let body =
          Expr.create_let
            (Let.create bound
               (Named.create_set_of_closures wrapper_alloc_mode
                  wrapper_taking_remaining_args)
               (Expr.create_apply_cont apply_cont)
               Or_unknown.Unknown)
        in
        let bound_static =
          Bound_static.singleton (Bound_static.Pattern.code code_id)
        in
        let static_consts = Static_const_group.create (code :: []) in
        Expr.create_let
          (Let.create
             (Bound_pattern.static bound_static)
             (Named.create_static_consts static_consts)
             body Or_unknown.Unknown)
      in
      expr, dacc0
    | Or_bottom.Bottom ->
      ( Expr.create_invalid
          (Flambda.Invalid.Partial_application_mode_mismatch
             (apply0, callee's_code_metadata)),
        dacc )
  in
  let down_to_up1 =
   fun dacc1 expr0 ->
    let expr1 =
      match original_call with
      | Call_kind.Function_call.Direct _ -> expr0
      | Call_kind.Function_call.Indirect_unknown_arity ->
        SE.notify_removed Removed_operations.direct_call_of_indirect expr0
      | Call_kind.Function_call.Indirect_known_arity _ ->
        SE.notify_removed Removed_operations.direct_call_of_indirect expr0
    in
    let expr2 = SE.notify_removed Removed_operations.call expr1 in
    down_to_up0 dacc1 expr2
  in
  simplify_expr dacc0 expr down_to_up1

(** val simplify_direct_over_application : Expr.t
    Simplify_common.expr_simplifier -> DA.t -> Apply.t -> SE.t
    Simplify_common.down_to_up -> Call_kind.Function_call.t -> Code_id.t ->
    Code_metadata.t -> (SE.t * DA.t) coq_M **)

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
        SE.notify_removed Removed_operations.direct_call_of_indirect expr0
      | Call_kind.Function_call.Indirect_known_arity _ ->
        SE.notify_removed Removed_operations.direct_call_of_indirect expr0
    in
    down_to_up0 dacc0 expr1
  in
  simplify_expr dacc expr down_to_up1

(** val replace_apply_by_invalid : DA.t -> SE.t Simplify_common.down_to_up ->
    Flambda.Invalid.t -> (SE.t * DA.t) coq_M **)

let replace_apply_by_invalid dacc down_to_up0 reason =
  down_to_up0 dacc (SE.simplified_invalid reason)

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
              not (K.equal (KS.kind param_component) (KS.kind arg_component)))
            param arg
          || has_mismatch params1 args1
        else true)
  in
  has_mismatch params args

(** val simplify_function_call_where_callee's_type_unavailable : DA.t -> Apply.t
    -> Call_kind.Function_call.t -> SE.t Simplify_common.down_to_up -> (SE.t *
    DA.t) coq_M **)

let simplify_function_call_where_callee's_type_unavailable dacc apply0 call
    down_to_up0 =
  let () = fail_if_probe apply0 in
  let denv = DA.denv dacc in
  let () =
    if Are_rebuilding_terms.do_rebuild_terms (DE.are_rebuilding_terms denv)
    then
      Inlining_report.record_decision_at_call_site_for_unknown_function
        (DE.inlining_history_tracker denv)
        apply0 Inlining_report.Pass.Before_simplify ()
    else ()
  in
  let env_at_use = denv in
  let dacc0, use_id0 =
    match Apply.continuation apply0 with
    | Apply_expr.Result_continuation.Return continuation ->
      let dacc0, use_id0 =
        DA.record_continuation_use dacc continuation
          ((fun x__1 ->
             (Continuation_use_kind.Non_inlinable { escaping = x__1 }
               : Continuation_use_kind.t))
             true)
          env_at_use
          ((fun x__1 x__2 x__3 ->
             T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
             (Some
                (Alloc_mode.For_applications.as_type (Apply.return_mode apply0)))
             (DE.machine_width denv)
             (Apply.return_arity apply0))
      in
      dacc0, Some use_id0
    | Apply_expr.Result_continuation.Never_returns -> dacc, None
  in
  let dacc1, exn_cont_use_id0 =
    DA.record_continuation_use dacc0
      (Exn_continuation.exn_handler (Apply.exn_continuation apply0))
      ((fun x__1 ->
         (Continuation_use_kind.Non_inlinable { escaping = x__1 }
           : Continuation_use_kind.t))
         true)
      (DA.denv dacc0)
      ((fun x__1 x__2 x__3 ->
         T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
         None
         (DE.machine_width (DA.denv dacc0))
         (Exn_continuation.arity (Apply.exn_continuation apply0)))
  in
  let call_kind =
    match call with
    | Call_kind.Function_call.Direct code_id ->
      if Code_id.Set.mem code_id (DA.code_ids_never_simplified dacc1)
      then Call_kind.indirect_function_call_known_arity Or_unknown.Unknown
      else Call_kind.direct_function_call code_id
    | Call_kind.Function_call.Indirect_unknown_arity ->
      Call_kind.indirect_function_call_unknown_arity
    | Call_kind.Function_call.Indirect_known_arity t -> (
      match t with
      | Or_unknown.Known code_ids ->
        if Code_id.Set.disjoint code_ids (DA.code_ids_never_simplified dacc1)
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
      (Inlined_attribute.with_use_info (Apply.inlined apply1)
         Inlined_attribute.Use_info.Unused_because_function_unknown)
  in
  let dacc2 =
    record_free_names_of_apply_as_used dacc1 use_id0 exn_cont_use_id0 apply2
  in
  down_to_up0 dacc2
    ((fun x__1 x__2 x__3 x__4 x__5 ->
       SE.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)
       None apply2 use_id0 exn_cont_use_id0 false)

(** val simplify_direct_function_call : Expr.t Simplify_common.expr_simplifier
    -> SE.t Simplify_common.rebuild -> DA.t -> Apply.t -> Code_id.t ->
    Code_metadata.t -> Code_id.Set.t Or_unknown.t -> Function_slot.t ->
    Call_kind.Function_call.t -> [ `Complex ] Flambda_arity.t -> Result_types.t
    Or_unknown_or_bottom.t -> Recursive.t -> bool -> Alloc_mode.For_types.t ->
    T.Function_type.t -> SE.t Simplify_common.down_to_up ->
    Call_kind.Function_call.t -> Inlined_debuginfo.t option -> (SE.t * DA.t)
    coq_M **)

let simplify_direct_function_call simplify_expr rebuild_expr dacc apply0
    callee's_code_id_from_type callee's_code_metadata_from_type
    callee's_code_ids_from_call_kind callee's_function_slot original_call
    result_arity0 result_types recursive must_be_detupled
    closure_alloc_mode_from_type function_decl down_to_up0 call
    inlined_forwarded_from =
  let result_types0 =
    let inlined = Apply.inlined apply0 in
    let probe = Apply.probe apply0 in
    match probe with
    | Some _ -> (
      match inlined with
      | Inlined_attribute.Always_inlined _ ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Apply.print apply0
      | Inlined_attribute.Hint_inlined ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Apply.print apply0
      | Inlined_attribute.Forward_inlined ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Apply.print apply0
      | Inlined_attribute.Never_inlined -> Or_unknown_or_bottom.Unknown
      | Inlined_attribute.Unroll (_, _) ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Apply.print apply0
      | Inlined_attribute.Default_inlined ->
        Misc.fatal_errorf
          "[Apply] terms with a [probe] (i.e. that call a tracing probe) must \
           always be marked as [Never_inline]:@ %a"
          Apply.print apply0)
    | None -> result_types
  in
  let callee's_code_ids =
    match callee's_code_ids_from_call_kind with
    | Or_unknown.Known callee's_code_ids_from_call_kind0 ->
      let typing_env = DA.typing_env dacc in
      T.Code_age_relation.meet_set
        (TE.code_age_relation typing_env)
        (TE.code_age_relation_resolver typing_env)
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
          (fun _ -> DE.find_code_metadata_exn (DA.denv dacc) callee's_code_id)
          Port_monad.not_found
          (fun _ ->
            callee's_code_id_from_type, callee's_code_metadata_from_type)
          (fun callee's_code_metadata ->
            callee's_code_id, callee's_code_metadata)
      | None -> callee's_code_id_from_type, callee's_code_metadata_from_type
    in
    let call_kind = Call_kind.direct_function_call callee's_code_id in
    let apply1 = Apply.with_call_kind apply0 call_kind in
    let params_arity = Code_metadata.params_arity callee's_code_metadata in
    let args_arity = Apply.args_arity apply1 in
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
          Apply.print apply1
      else
        replace_apply_by_invalid dacc down_to_up0
          ((fun (x__1, x__2, x__3) ->
             (Flambda.Invalid.Direct_application_parameter_kind_mismatch
                { params_arity = x__1; args_arity = x__2; apply = x__3 }
               : Flambda.Invalid.t))
             (params_arity, args_arity, apply1))
    else
      let args_arity0 = Apply.args_arity apply1 in
      let provided_num_args = Flambda_arity.num_params args_arity0 in
      let num_params = Flambda_arity.num_params params_arity in
      let result_arity_of_application = Apply.return_arity apply1 in
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
              result_arity_of_application Apply.print apply1
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
              Apply.print apply1
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
              Apply.print apply1
          else
            replace_apply_by_invalid dacc down_to_up0
              (Flambda.Invalid.Application_result_kind_mismatch
                 ( Flambda_arity.create_singletons
                     (Flambda_kind.With_subkind.any_value :: []),
                   apply1 ))
        else if DE.disable_partial_application_stub_generation (DA.denv dacc)
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
          num_params provided_num_args Apply.print apply1
  | Or_bottom.Bottom ->
    replace_apply_by_invalid dacc down_to_up0
      (Flambda.Invalid.Closure_type_was_invalid apply0)

(** val simplify_function_call : Expr.t Simplify_common.expr_simplifier -> SE.t
    Simplify_common.rebuild -> DA.t -> Apply.t -> T.t option ->
    Call_kind.Function_call.t -> SE.t Simplify_common.down_to_up ->
    Inlined_debuginfo.t option -> (SE.t * DA.t) coq_M **)

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
      (SE.simplified_invalid (Flambda.Invalid.Closure_type_was_invalid apply0))
  in
  let denv = DA.denv dacc in
  match callee_ty with
  | Some callee_ty0 ->
    (fun f__1 f__2 f__3 x__0 ->
      match (x__0 : _ T.meet_shortcut) with
      | T.Known_result x__1 -> f__1 x__1
      | T.Need_meet -> f__2 ()
      | T.Invalid -> f__3 ())
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
          T.Function_type.code_id func_decl_type
        in
        Port_monad.match_exn
          (fun _ -> DE.find_code_metadata_exn denv callee's_code_id_from_type)
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
            match (x__0 : _ T.meet_shortcut) with
            | T.Known_result x__1 -> f__1 x__1
            | T.Need_meet -> f__2 ()
            | T.Invalid -> f__3 ())
            (fun code_ids ->
              let args_arity = Apply.args_arity apply0 in
              if
                Code_id.Set.for_all
                  (fun code_id ->
                    Port_monad.match_exn
                      (fun _ -> DE.find_code_metadata_exn denv code_id)
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
            (T.meet_code_ids (DE.typing_env denv) callee_ty0)
        | Call_kind.Function_call.Indirect_known_arity _ ->
          type_unavailable call)
      (fun _ -> not_a_closure ())
      (T.meet_single_closures_entry (DE.typing_env denv) callee_ty0)
  | None -> (
    match call with
    | Call_kind.Function_call.Direct callee's_code_id ->
      Port_monad.match_exn
        (fun _ -> DE.find_code_metadata_exn denv callee's_code_id)
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
        "No callee provided for non-direct OCaml function call:@ %a" Apply.print
        apply0
    | Call_kind.Function_call.Indirect_known_arity _ ->
      Misc.fatal_errorf
        "No callee provided for non-direct OCaml function call:@ %a" Apply.print
        apply0)

type ('a, 'b) simplify_apply_shared_result =
  | Ok of 'a
  | Invalid of 'b

(** val simplify_apply_shared : DA.t -> Apply.t -> ((DA.t, T.t option, Apply.t,
    T.t list, Inlined_debuginfo.t option) Port_monad.tuple5, [ `Unarized ]
    Flambda_arity.t) simplify_apply_shared_result coq_M **)

let simplify_apply_shared dacc apply0 =
  let callee_ty, simplified_callee =
    match Apply.callee apply0 with
    | Some callee ->
      let callee_ty, simplified_callee =
        S.simplify_simple dacc callee NM.normal
      in
      Some callee_ty, Some simplified_callee
    | None -> None, None
  in
  let { Simplify_simple.simples = args; Simplify_simple.simple_tys = arg_types }
      =
    Simplify_simple.simplify_simples dacc (Apply.args apply0)
  in
  let kind_mismatch = ref false in
  let () =
    List.iter2
      (fun kind_with_subkind arg_type ->
        let kind = K.With_subkind.kind kind_with_subkind in
        if not (K.equal kind (T.kind arg_type))
        then
          if not (Flambda_features.kind_checks ())
          then kind_mismatch := true
          else
            Misc.fatal_errorf
              "Argument kind %a from arity does not match kind from type %a \
               for application:@ %a"
              K.print kind T.print arg_type Apply.print apply0
        else ())
      (Flambda_arity.unarize (Apply.args_arity apply0))
      arg_types
  in
  if !kind_mismatch
  then
    Invalid
      (Flambda_arity.create_singletons
         (List.map K.With_subkind.anything (List.map T.kind arg_types)))
  else
    let inlining_state =
      Inlining_state.combine
        (DE.get_inlining_state (DA.denv dacc))
        (Apply.inlining_state apply0)
    in
    let inlined, inlined_forwarded_from =
      let inlined = Apply.inlined apply0 in
      match inlined with
      | Inlined_attribute.Always_inlined _ -> inlined, None
      | Inlined_attribute.Hint_inlined -> inlined, None
      | Inlined_attribute.Forward_inlined -> (
        match DE.inlined_attribute_to_forward (DA.denv dacc) with
        | Some f ->
          (fun f__1 x__0 ->
            let x__1, ~forwarded_from:x__2 = x__0 in
            f__1 x__1 x__2)
            (fun inlined_from_env forwarded_from ->
              inlined_from_env, Some forwarded_from)
            f
        | None -> inlined, None)
      | Inlined_attribute.Never_inlined -> inlined, None
      | Inlined_attribute.Unroll (_, _) -> inlined, None
      | Inlined_attribute.Default_inlined -> inlined, None
    in
    let apply1 =
      Apply.create simplified_callee
        (Apply.continuation apply0)
        (Apply.exn_continuation apply0)
        args (Apply.args_arity apply0)
        (Apply.return_arity apply0)
        (Apply.call_kind apply0) (Apply.return_mode apply0)
        (DE.add_inlined_debuginfo (DA.denv dacc) (Apply.dbg apply0))
        inlined inlining_state (Apply.probe apply0) (Apply.position apply0)
        (Inlining_history.Relative.concat
           (DE.relative_history (DA.denv dacc))
           (Apply.relative_history apply0))
    in
    Ok (dacc, callee_ty, apply1, arg_types, inlined_forwarded_from)

(** val simplify_method_call : DA.t -> Apply.t -> T.t -> Call_kind.Method_kind.t
    -> Simple.t -> SE.t Simplify_common.down_to_up -> (SE.t * DA.t) coq_M **)

let simplify_method_call dacc apply0 callee_ty _ obj down_to_up0 =
  let () = fail_if_probe apply0 in
  let callee_kind = T.kind callee_ty in
  let () =
    if not (K.is_value callee_kind)
    then
      Misc.fatal_errorf "Method call with callee of wrong kind %a: %a" K.print
        callee_kind T.print callee_ty
    else ()
  in
  let apply_cont =
    match Apply.continuation apply0 with
    | Apply_expr.Result_continuation.Return continuation -> continuation
    | Apply_expr.Result_continuation.Never_returns ->
      Misc.fatal_error "Cannot simplify a method call that never returns"
  in
  let denv = DA.denv dacc in
  let () = DE.check_simple_is_bound denv obj in
  let dacc0, use_id0 =
    DA.record_continuation_use dacc apply_cont
      ((fun x__1 ->
         (Continuation_use_kind.Non_inlinable { escaping = x__1 }
           : Continuation_use_kind.t))
         true)
      denv
      ((fun x__1 x__2 x__3 ->
         T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
         (Some (Alloc_mode.For_applications.as_type (Apply.return_mode apply0)))
         (DE.machine_width denv)
         (Apply.return_arity apply0))
  in
  let dacc1, exn_cont_use_id0 =
    DA.record_continuation_use dacc0
      (Exn_continuation.exn_handler (Apply.exn_continuation apply0))
      ((fun x__1 ->
         (Continuation_use_kind.Non_inlinable { escaping = x__1 }
           : Continuation_use_kind.t))
         true)
      (DA.denv dacc0)
      ((fun x__1 x__2 x__3 ->
         T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
         None
         (DE.machine_width (DA.denv dacc0))
         (Exn_continuation.arity (Apply.exn_continuation apply0)))
  in
  let dacc2 =
    record_free_names_of_apply_as_used dacc1 (Some use_id0) exn_cont_use_id0
      apply0
  in
  down_to_up0 dacc2
    ((fun x__1 x__2 x__3 x__4 x__5 ->
       SE.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)
       None apply0 (Some use_id0) exn_cont_use_id0 false)

(** val simplify_c_call : Expr.t Simplify_common.expr_simplifier -> DA.t ->
    Apply.t -> T.t -> T.t list -> SE.t Simplify_common.down_to_up -> (SE.t *
    DA.t) coq_M **)

let simplify_c_call simplify_expr dacc apply0 callee_ty arg_types down_to_up0 =
  let () = fail_if_probe apply0 in
  let return_arity = Apply.return_arity apply0 in
  let callee_kind = T.kind callee_ty in
  let () =
    if not (K.is_value callee_kind)
    then
      Misc.fatal_errorf "C callees must be of kind [Value], not %a: %a" K.print
        callee_kind T.print callee_ty
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
        match Apply.continuation apply0 with
        | Apply_expr.Result_continuation.Return apply_continuation ->
          let apply_continuation_arg_types =
            let from_arity =
              (fun x__1 x__2 x__3 ->
                T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
                (Some
                   (Alloc_mode.For_applications.as_type
                      (Apply.return_mode apply0)))
                (DE.machine_width (DA.denv dacc))
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
            DA.record_continuation_use dacc apply_continuation
              ((fun x__1 ->
                 (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                   : Continuation_use_kind.t))
                 true)
              (DA.denv dacc) apply_continuation_arg_types
          in
          dacc0, Some use_id0
        | Apply_expr.Result_continuation.Never_returns -> dacc, None
      in
      let dacc1, exn_cont_use_id0 =
        DA.record_continuation_use dacc0
          (Exn_continuation.exn_handler (Apply.exn_continuation apply0))
          ((fun x__1 ->
             (Continuation_use_kind.Non_inlinable { escaping = x__1 }
               : Continuation_use_kind.t))
             true)
          (DA.denv dacc0)
          ((fun x__1 x__2 x__3 ->
             T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
             None
             (DE.machine_width (DA.denv dacc0))
             (Exn_continuation.arity (Apply.exn_continuation apply0)))
      in
      let dacc2 =
        record_free_names_of_apply_as_used dacc1 use_id0 exn_cont_use_id0 apply0
      in
      down_to_up0 dacc2
        ((fun x__1 x__2 x__3 x__4 x__5 ->
           SE.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)
           None apply0 use_id0 exn_cont_use_id0 false))
    (fun dacc0 expr operation ->
      let down_to_up1 =
       fun dacc1 expr0 -> down_to_up0 dacc1 (SE.notify_removed operation expr0)
      in
      simplify_expr dacc0 expr down_to_up1)
    (fun _ ->
      replace_apply_by_invalid dacc down_to_up0
        (Flambda.Invalid.Closure_type_was_invalid apply0))
    simplified

(** val simplify_effect_op : DA.t -> Apply.t -> Call_kind.Effect.t -> SE.t
    Simplify_common.down_to_up -> (SE.t * DA.t) coq_M **)

let simplify_effect_op dacc apply0 op down_to_up0 =
  let () = fail_if_probe apply0 in
  let denv = DA.denv dacc in
  let op0 =
    let simplify_simple =
     fun simple ->
      let _, simple0 = S.simplify_simple dacc simple NM.normal in
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
  let apply1 = Apply.with_call_kind apply0 (Call_kind.effect_ op0) in
  let dacc0, use_id0 =
    match Apply.continuation apply1 with
    | Apply_expr.Result_continuation.Return continuation ->
      let dacc0, use_id0 =
        DA.record_continuation_use dacc continuation
          ((fun x__1 ->
             (Continuation_use_kind.Non_inlinable { escaping = x__1 }
               : Continuation_use_kind.t))
             true)
          denv
          ((fun x__1 x__2 x__3 ->
             T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
             (Some
                (Alloc_mode.For_applications.as_type (Apply.return_mode apply1)))
             (DE.machine_width denv)
             (Apply.return_arity apply1))
      in
      dacc0, Some use_id0
    | Apply_expr.Result_continuation.Never_returns -> dacc, None
  in
  let dacc1, exn_cont_use_id0 =
    DA.record_continuation_use dacc0
      (Exn_continuation.exn_handler (Apply.exn_continuation apply1))
      ((fun x__1 ->
         (Continuation_use_kind.Non_inlinable { escaping = x__1 }
           : Continuation_use_kind.t))
         true)
      (DA.denv dacc0)
      ((fun x__1 x__2 x__3 ->
         T.unknown_types_from_arity ?alloc_mode:x__1 x__2 x__3)
         None
         (DE.machine_width (DA.denv dacc0))
         (Exn_continuation.arity (Apply.exn_continuation apply1)))
  in
  let dacc2 =
    record_free_names_of_apply_as_used dacc1 use_id0 exn_cont_use_id0 apply1
  in
  down_to_up0 dacc2
    ((fun x__1 x__2 x__3 x__4 x__5 ->
       SE.simplified_apply ?result_arity:x__1 x__2 x__3 x__4 x__5)
       None apply1 use_id0 exn_cont_use_id0 false)

(** val simplify_apply : Expr.t Simplify_common.expr_simplifier -> SE.t
    Simplify_common.rebuild -> DA.t -> Apply.t -> SE.t
    Simplify_common.down_to_up -> (SE.t * DA.t) coq_M **)

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
              Apply.print apply1
        in
        simplify_method_call dacc0 apply1 callee_ty0 kind obj down_to_up0)
      (fun _ _ _ _ ->
        let callee_ty0 =
          match callee_ty with
          | Some callee_ty0 -> callee_ty0
          | None ->
            Misc.fatal_errorf "No callee provided for C call:@ %a" Apply.print
              apply1
        in
        simplify_c_call simplify_expr dacc0 apply1 callee_ty0 arg_types
          down_to_up0)
      (fun op -> simplify_effect_op dacc0 apply1 op down_to_up0)
      (Apply.call_kind apply1)
  | Invalid args_arity ->
    replace_apply_by_invalid dacc down_to_up0
      (Flambda.Invalid.Application_argument_kind_mismatch (args_arity, apply0))
