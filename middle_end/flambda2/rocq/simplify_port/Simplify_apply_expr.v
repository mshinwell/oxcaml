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

(* This file follows middle_end/flambda2/simplify/simplify_apply_expr.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md, and the
   eliminator of one tuple with a label, below. The donor opens
   [Flambda.Import] and then [Simplify_import]: so does this file. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda.
Import Flambda.Import_.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Apply_cont_expr Apply_cont_rewrite_id
  Apply_expr Are_rebuilding_terms Bound_parameters Bound_pattern Bound_var
  Call_kind Call_site_inlining_decision Call_site_inlining_decision_type
  Closure_info Code_id Code_metadata Continuation Continuation_use_kind
  Exn_continuation First_complex_local_param Flambda_arity Flambda_debug_uid
  Flambda_features Flow Function_slot Inlined_attribute Inlined_debuginfo
  Inlining_history Inlining_report Inlining_state Inlining_transforms List
  Loopify_state Name_mode Or_bottom Or_unknown Or_unknown_or_bottom Recursive
  Removed_operations Result_types Simple Simplify_apply_cont_expr
  Simplify_common Simplify_extcall Simplify_rec_info_expr Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(*OCAML
open! Flambda.Import
open! Simplify_import
OCAML*)

(* PORT-GAP(decl): 1317, [DE.inlined_attribute_to_forward] gives a tuple
   with a label, [(inlined_from_env, ~forwarded_from)], which decl/ gives as
   a plain pair: OCaml does not take a pattern without the label for it.
   The eliminator of that tuple is here. *)
Definition match_inlined_attribute_to_forward {Res : Type}
    (x : Inlined_attribute.t * Inlined_debuginfo.t)
    (f : Inlined_attribute.t -> Inlined_debuginfo.t -> M Res) : M Res :=
  match x with (x1, x2) => f x1 x2 end.
Extract Inlined Constant match_inlined_attribute_to_forward => "(fun x__0 f__1 -> let (x__1, ~forwarded_from:x__2) = x__0 in f__1 x__1 x__2)".

(* 20-27 *)
Definition fail_if_probe (apply : Apply.t) : M unit :=
  let! tmp1 := Apply.probe apply in
  match tmp1 with
  | None => ret tt
  | Some _ =>
    fatal_errorf2
      "[Apply] terms with a [probe] (i.e. that call a tracing probe) must always be direct applications of an OCaml function:@ %a"
      Apply.print apply
  end.

(* 29-45. In the compiler: [apply ~use_id ~exn_cont_use_id data_flow]. *)
Definition record_free_names_of_apply_as_used0 (apply : Apply.t)
    (use_id : option Apply_cont_rewrite_id.t)
    (exn_cont_use_id : Apply_cont_rewrite_id.t) (data_flow : Flow.Acc.t)
    : M Flow.Acc.t :=
  let* data_flow :=
    let! tmp1 := Apply.free_names_without_exn_continuation apply in
    Flow.Acc.add_used_in_current_handler tmp1 data_flow
  in
  let* exn_cont := Apply.exn_continuation apply in
  (* 37-42: the call that is one of the two values of the match is bound by
     [let*]. *)
  let* result_cont :=
    let* continuation := Apply.continuation apply in
    match continuation, use_id with
    | Apply_expr.Result_continuation.Never_returns, None => ret None
    | Apply_expr.Result_continuation.Return k, Some use_id =>
      ret (Some (use_id, k))
    | Apply_expr.Result_continuation.Never_returns, Some _
    | Apply_expr.Result_continuation.Return _, None =>
      assert_false
    end
  in
  (* 43-45: the arguments are in the order of the interface. *)
  let! tmp1 := Apply.return_arity apply in
  Flow.Acc.add_apply_conts result_cont (exn_cont_use_id, exn_cont) tmp1
    data_flow.

(* 47-49. In the compiler: [dacc ~use_id ~exn_cont_use_id apply]. *)
Definition record_free_names_of_apply_as_used (dacc : DA.t)
    (use_id : option Apply_cont_rewrite_id.t)
    (exn_cont_use_id : Apply_cont_rewrite_id.t) (apply : Apply.t) : M DA.t :=
  (* 49: [record_free_names_of_apply_as_used0], of this file, given its
     first three arguments only, is a value. *)
  DA.map_flow_acc dacc
    (record_free_names_of_apply_as_used0 apply use_id exn_cont_use_id).

(* 51-96 *)
Definition loopify_decision_for_call (dacc : DA.t) (apply : Apply.t)
    : M Loopify_state.t :=
  let* denv := DA.denv dacc in
  let! tmp1 := DE.are_rebuilding_terms denv in
  let! tmp2 := Are_rebuilding_terms.do_not_rebuild_terms tmp1 in
  if tmp2
  then
    (* During speculative inlining, we are only rebuilding the inlined body, and
       in particular we run the Flow Analysis on just the inlined body. The Flow
       Analysis assumes that it sees all of the code being simplified, which is
       usually true for inlined body since (apart from the return and exn
       continuations which are treated separately) they are closed. However this
       is not true for a function being loopified since an apply_expr can be
       turned into an apply_cont pointing to the `self` continuation, which is
       missing from the Flow Accumulator. Therefore, during speculative inlining
       (and thus when we are not rebuilding terms), we disable loopification. *)
    ret Loopify_state.do_not_loopify
  else
    let! tmp3 := DE.closure_info denv in
    match tmp3 with
    | Closure_info.Not_in_a_closure
    | Closure_info.In_a_set_of_closures_but_not_yet_in_a_specific_closure =>
      ret Loopify_state.do_not_loopify
    | Closure_info.Closure _ return_continuation exn_continuation my_closure _
      =>
      let* tenv := DE.typing_env denv in
      (* PORT-GAP(loose): 77, the attribute [@inline always] is not kept. *)
      let& canon :=
        fun (simple : Simple.t) =>
        let! tmp1 := TE.get_canonical_simple_exn tenv None None simple in
        Simple.without_coercion tmp1
      in
      let! tmp1 := Apply.callee apply in
      match tmp1 with
      | None => ret Loopify_state.do_not_loopify
      | Some callee =>
        (* 83-94: [a && b && c] is [a && (b && c)]. *)
        let! tmp1 := canon callee in
        let! tmp2 := Simple.var my_closure in
        let! tmp3 := canon tmp2 in
        let! tmp4 := Simple.equal tmp3 tmp1 in
        let! tmp5 :=
          and_then tmp4
            (let! tmp6 :=
               (let! tmp7 := Apply.continuation apply in
                match tmp7 with
                | Apply_expr.Result_continuation.Never_returns =>
                  (* If we never return, then this call is a tail-call *)
                  ret true
                | Apply_expr.Result_continuation.Return
                    apply_return_continuation =>
                  Continuation.equal apply_return_continuation
                    return_continuation
                end)
             in
             and_then tmp6
               (let! tmp8 := Exn_continuation.create exn_continuation [] in
                let! tmp9 := Apply.exn_continuation apply in
                Exn_continuation.equal tmp9 tmp8))
        in
        if tmp5 then DE.loopify_state denv else ret Loopify_state.do_not_loopify
      end
    end.

(* 98-102 *)
Definition simplify_self_tail_call (dacc : DA.t) (apply : Apply.t)
    (self_cont : Continuation.t) (down_to_up : Simplify_common.down_to_up SE.t)
    : M (SE.t * DA.t) :=
  let! tmp1 := Apply.dbg apply in
  let! tmp2 := Apply.args apply in
  let! tmp3 := Apply_cont_expr.create None self_cont tmp2 tmp1 in
  Simplify_apply_cont_expr.simplify_apply_cont dacc tmp3 down_to_up.

(* 104-182. In the compiler: [~simplify_expr dacc apply ~callee's_code_id
   ~callee's_code_metadata ~down_to_up]. *)
Definition simplify_direct_tuple_application
    (simplify_expr : Simplify_common.expr_simplifier Expr.t) (dacc : DA.t)
    (apply : Apply.t) (callee's_code_id : Code_id.t)
    (callee's_code_metadata : Code_metadata.t)
    (down_to_up : Simplify_common.down_to_up SE.t) : M (SE.t * DA.t) :=
  let* dbg := Apply.dbg apply in
  let* tuple_size :=
    (* The code for the function being applied has exactly as many parameters as
       there are components of the tuple (which is the first element of
       [Apply.args apply]). The components must be of kind [Value] due to the
       check in [transl_tupled_function] and therefore cannot be unboxed
       products themselves. *)
    let! tmp1 := Code_metadata.params_arity callee's_code_metadata in
    Flambda_arity.cardinal_unarized tmp1
  in
  (* Split the tuple argument from any over application arguments *)
  let* '(tuple_arg, over_application_args) :=
    let! tmp1 := Apply.args apply in
    match tmp1 with
    | tuple :: others => ret (tuple, others)
    | _ =>
      fatal_errorf2 "Empty argument list for direct tuple application:@ %a"
        Apply.print apply
    end
  in
  (* Create the list of variables and projections *)
  let* vars_and_fields :=
    List.init tuple_size
      (fun field =>
        (* This internally created variable does not get a
           [Flambda_debug_uid.t]. *)
        let! tmp1 := DA.denv dacc in
        let! tmp2 := DE.machine_width tmp1 in
        let! tmp3 :=
          Simplify_common.project_tuple tmp2 dbg tuple_size field tuple_arg
        in
        let! tmp4 := Variable_.create None "tuple_field" K.value in
        ret (T3 tmp4 Flambda_debug_uid.none tmp3))
  in
  (* Construct the arities for the tuple and any over application arguments *)
  let* args_arity :=
    let* tuple_arity :=
      let! tmp1 :=
        List.init tuple_size (fun _ => ret K.With_subkind.any_value)
      in
      Flambda_arity.create_singletons tmp1
    in
    let* over_application_arity :=
      (* Any over application might involve complex arities. *)
      let! tmp1 := Apply.args_arity apply in
      Flambda_arity.partially_apply tmp1 1
    in
    Flambda_arity.concat tuple_arity over_application_arity
  in
  (* Change the application to operate on the fields of the tuple *)
  let* apply :=
    let! tmp1 := List.map (fun '(T3 v _ _) => Simple.var v) vars_and_fields in
    Apply.with_args apply (tmp1 ++ over_application_args) args_arity
  in
  (* Immediately simplify over_applications to avoid having direct applications
     with the wrong arity. *)
  let* apply_expr :=
    match over_application_args with
    | [] => Expr.create_apply apply
    | _ =>
      (* [apply] already got a correct relative_history and
         [split_direct_over_application] infers the relative history from the
         one on [apply] so there's nothing to do here. *)
      Simplify_common.split_direct_over_application apply callee's_code_id
        callee's_code_metadata
    end
  in
  (* Insert the projections and simplify the new expression, to allow field
     projections to be simplified, and over-application/full_application
     optimizations *)
  let* expr :=
    (* 174: the compiler's first parameter is the pattern [(v, v_duid,
       defining_expr)]; here it has a name and is taken apart on the next
       line. *)
    List.fold_right
      (fun var_and_field body =>
        let '(T3 v v_duid defining_expr) := var_and_field in
        let* var_bind := Bound_var.create v v_duid Name_mode.normal in
        let! tmp1 := Bound_pattern.singleton var_bind in
        let! tmp2 := Let.create tmp1 defining_expr body Or_unknown.Unknown in
        Expr.create_let tmp2)
      vars_and_fields apply_expr
  in
  simplify_expr dacc expr down_to_up.

(* 184-197. In the compiler: [expr ~original_call ~callee's_code_metadata]. *)
Definition update_direct_call_benefit (expr : SE.t)
    (original_call : Call_kind.Function_call.t)
    (callee's_code_metadata : Code_metadata.t) : M SE.t :=
  match original_call with
  | Call_kind.Function_call.Indirect_unknown_arity
  | Call_kind.Function_call.Indirect_known_arity _ =>
    SE.notify_removed Removed_operations.direct_call_of_indirect expr
  | Call_kind.Function_call.Direct old_code_id =>
    let* code_id := Code_metadata.code_id callee's_code_metadata in
    let! tmp1 := Code_id.equal code_id old_code_id in
    if tmp1
    then ret expr
    else SE.notify_removed Removed_operations.updated_direct_call expr
  end.

(* 199-222 *)
(* PORT-GAP(loose): 199-201, the compiler's first parameter is the record
   pattern [{ apply; use_id; exn_cont_use_id; result_arity; is_cold }]; here
   it has a name and is taken apart on the next lines. *)
Definition rebuild_apply (simplified_apply : SE.simplified_apply_)
    (uacc : UA.t) (after_rebuild : Simplify_common.after_rebuild)
    : M (RE.t * UA.t) :=
  let '{| SE.apply := apply;
          SE.use_id := use_id;
          SE.exn_cont_use_id := exn_cont_use_id;
          SE.result_arity := result_arity;
          SE.is_cold := is_cold
       |} := simplified_apply in
  let* apply :=
    Simplify_common.update_exn_continuation_extra_args uacc exn_cont_use_id
      apply
  in
  let& erase_callee := false in
  let* apply := if erase_callee then Apply.erase_callee apply else ret apply in
  let* '(uacc, expr) :=
    let! tmp1 := Flambda_arity.unarize_t result_arity in
    EB.rewrite_fixed_arity_apply uacc use_id is_cold tmp1 apply
  in
  after_rebuild expr uacc.

(* 224-226 *)
(* PORT-GAP(type): 224-226, a variant with an inline record: the Rocq type
   takes the field by place; Rocq prints the compiler's definition at its
   place. *)
Inductive inlining_decision_ : Type :=
| Do_not_inline (erase_attribute : bool)
| Inline (dacc : DA.t) (inlined : Expr.t).
Extract Inductive inlining_decision_ => "inlining_decision" [ "(fun x__1 -> Do_not_inline { erase_attribute = x__1 })" "Inline" ] "(fun f__1 f__2 x__0 -> match x__0 with Do_not_inline { erase_attribute = x__1 } -> f__1 x__1 | Inline (x__1, x__2) -> f__2 x__1 x__2)".
Definition inlining_decision : Type := inlining_decision_.
Extract Constant inlining_decision => "| Do_not_inline of { erase_attribute : bool } | Inline of DA.t * Expr.t".

(* 230-436. In the compiler: [~simplify_expr ~rebuild_expr dacc apply
   function_type ~params_arity ~result_arity ~result_types ~down_to_up
   ~original_call ~callee's_code_metadata ~inlined_forwarded_from]. *)
Definition simplify_direct_full_application
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (rebuild_expr : Simplify_common.rebuild SE.t) (dacc : DA.t)
    (apply : Apply.t) (function_type : option T.Function_type.t)
    (params_arity : Flambda_arity.t_Complex)
    (result_arity : Flambda_arity.t_Complex)
    (result_types : Or_unknown_or_bottom.t Result_types.t)
    (down_to_up : Simplify_common.down_to_up SE.t)
    (original_call : Call_kind.Function_call.t)
    (callee's_code_metadata : Code_metadata.t)
    (inlined_forwarded_from : option Inlined_debuginfo.t)
    : M (SE.t * DA.t) :=
  let* inlined :=
    match function_type with
    | None =>
      (* No rec info available, prevent inlining to avoid problems *)
      ret (Do_not_inline false)
    | Some function_type =>
      (* 241-244: the arguments are in the order of the interface. *)
      let* decision :=
        Call_site_inlining_decision.make_decision dacc simplify_expr
          rebuild_expr function_type apply result_arity
      in
      let* unrolling_depth :=
        let! tmp1 :=
          Call_site_inlining_decision.get_rec_info dacc function_type
        in
        Simplify_rec_info_expr.known_remaining_unrolling_depth dacc tmp1
      in
      (* 249-258: the arguments are in the order of the interface. *)
      (let! tmp1 := DA.denv dacc in
       let! tmp2 := DE.are_rebuilding_terms tmp1 in
       let! tmp3 := Are_rebuilding_terms.do_rebuild_terms tmp2 in
       if tmp3
       then
         let! tmp4 := DA.are_rebuilding_terms dacc in
         let! tmp5 := Code_metadata.absolute_history callee's_code_metadata in
         let! tmp6 := DA.denv dacc in
         let! tmp7 := DE.inlining_history_tracker tmp6 in
         Inlining_report.record_decision_at_call_site_for_known_function tmp7
           unrolling_depth apply Inlining_report.Pass.Before_simplify tmp5
           tmp4 inlined_forwarded_from decision
       else ret tt) ;;
      let! tmp1 := Call_site_inlining_decision_type.can_inline decision in
      match tmp1 with
      | Call_site_inlining_decision_type.Do_not_inline
          erase_attribute_if_ignored =>
        ret (Do_not_inline erase_attribute_if_ignored)
      | Call_site_inlining_decision_type.Inline unroll_to was_inline_always =>
        let* dacc :=
          (* PORT-GAP(papp): 264, [DE.record_inlining_decision] is given its
             first two arguments only. *)
          let! tmp1 := papp2 DE.record_inlining_decision apply decision in
          DA.map_denv dacc tmp1
        in
        let* '(dacc, inlined) :=
          Inlining_transforms.inline dacc apply unroll_to was_inline_always
            function_type
        in
        ret (Inline dacc inlined)
      end
    end
  in
  match inlined with
  | Inline dacc inlined =>
    let* is_cold := Code_metadata.cold callee's_code_metadata in
    let& down_to_up :=
      fun (dacc : DA.t) (simplified_body : SE.t) =>
      let* simplified_body :=
        update_direct_call_benefit simplified_body original_call
          callee's_code_metadata
      in
      let* simplified_body :=
        SE.notify_removed Removed_operations.call simplified_body
      in
      let* simplified_body :=
        if is_cold then SE.mark_as_cold simplified_body else ret simplified_body
      in
      down_to_up dacc simplified_body
    in
    simplify_expr dacc inlined down_to_up
  | Do_not_inline erase_attribute =>
    let* apply :=
      let* inlined :=
        if erase_attribute
        then ret Inlined_attribute.Default_inlined
        else
          let! tmp1 := Apply.inlined apply in
          Inlined_attribute.with_use_info tmp1
            Inlined_attribute.Use_info.Unused_because_of_call_site_decision
      in
      Apply.with_inlined_attribute apply inlined
    in
    let! tmp1 := loopify_decision_for_call dacc apply in
    match tmp1 with
    | Loopify_state.Loopify self_cont =>
      simplify_self_tail_call dacc apply self_cont down_to_up
    | Loopify_state.Do_not_loopify =>
      let* '(T3 dacc use_id result_continuation) :=
        let* result_continuation := Apply.continuation apply in
        match result_continuation, result_types with
        | Apply_expr.Result_continuation.Never_returns,
          ( Or_unknown_or_bottom.Unknown | Or_unknown_or_bottom.Bottom
          | Or_unknown_or_bottom.Ok _ )
        | Apply_expr.Result_continuation.Return _, Or_unknown_or_bottom.Bottom
          =>
          ret (T3 dacc None Apply_expr.Result_continuation.Never_returns)
        | Apply_expr.Result_continuation.Return apply_return_continuation,
          Or_unknown_or_bottom.Unknown =>
          let* env_at_use := DA.denv dacc in
          let* env_at_use :=
            let! tmp1 := Code_metadata.cold callee's_code_metadata in
            if tmp1 then DE.mark_as_cold env_at_use else ret env_at_use
          in
          (* 316-325: the arguments are in the order of the interface. *)
          let* '(dacc, use_id) :=
            let! tmp1 := DA.denv dacc in
            let! tmp2 := DE.machine_width tmp1 in
            let! tmp3 := Apply.return_mode apply in
            let! tmp4 := Alloc_mode.For_applications.as_type tmp3 in
            let! tmp5 :=
              T.unknown_types_from_arity (Some tmp4) tmp2 result_arity
            in
            DA.record_continuation_use dacc apply_return_continuation
              (Continuation_use_kind.Non_inlinable true) env_at_use tmp5
          in
          ret (T3 dacc (Some use_id) result_continuation)
        | Apply_expr.Result_continuation.Return apply_return_continuation,
          Or_unknown_or_bottom.Ok result_types =>
          Result_types.pattern_match result_types
            (fun params results env_extension =>
              (* 331-339 *)
              (let! tmp1 := Bound_parameters.cardinal params in
               let! tmp2 := Flambda_arity.cardinal_unarized params_arity in
               if tmp2 <>? tmp1
               then
                 fatal_errorf6
                   "Params arity %a does not match up with params in the result types structure:@ %a@ for application:@ %a"
                   Flambda_arity.print params_arity Result_types.print
                   result_types Apply.print apply
               else ret tt) ;;
              (* 340-348 *)
              (let! tmp1 := Bound_parameters.cardinal results in
               let! tmp2 := Flambda_arity.cardinal_unarized result_arity in
               if tmp2 <>? tmp1
               then
                 fatal_errorf6
                   "Result arity %a does not match up with the result types structure:@ %a@ for application:@ %a"
                   Flambda_arity.print params_arity Result_types.print
                   result_types Apply.print apply
               else ret tt) ;;
              let* denv := DA.denv dacc in
              let* denv :=
                DE.add_parameters_with_unknown_types false None
                  (Some Name_mode.in_types) denv params
              in
              let* params := Bound_parameters.to_list params in
              let* results := Bound_parameters.to_list results in
              let* denv :=
                let* args := Apply.args apply in
                (let! tmp1 := List.compare_lengths params args in
                 assert_ (tmp1 =? 0)) ;;
                List.fold_left2
                  (fun denv param arg =>
                    let! tmp1 := BP.kind param in
                    let! tmp2 := K.With_subkind.kind tmp1 in
                    let! tmp3 := T.alias_type_of tmp2 arg in
                    let! tmp4 := BP.var param in
                    DE.add_equation_on_variable denv tmp4 tmp3)
                  denv params args
              in
              let* result_arity := Flambda_arity.unarize result_arity in
              let* denv :=
                List.fold_left2
                  (fun denv kind result =>
                    let* '(result_var, result_uid) := BP.var_and_uid result in
                    let! tmp1 := DE.machine_width denv in
                    let! tmp2 := Apply.return_mode apply in
                    let! tmp3 := Alloc_mode.For_applications.as_type tmp2 in
                    let! tmp4 := T.unknown_with_subkind (Some tmp3) tmp1 kind in
                    let! tmp5 := VB.create result_var result_uid NM.in_types in
                    DE.add_variable denv tmp5 tmp4)
                  denv result_arity results
              in
              let* denv := DE.extend_typing_environment denv env_extension in
              (* Note: the result types of the application will go into a meet
                 with the kind information on the parameter(s) of the return
                 continuation (just like the normal [Apply_cont] case where the
                 meet is only done upon reaching the handler). *)
              let* arg_types :=
                List.map2
                  (fun kind result_var =>
                    let! tmp1 := BP.simple result_var in
                    let! tmp2 := K.With_subkind.kind kind in
                    T.alias_type_of tmp2 tmp1)
                  result_arity results
              in
              let* env_at_use :=
                let! tmp1 := Code_metadata.cold callee's_code_metadata in
                if tmp1 then DE.mark_as_cold denv else ret denv
              in
              let* '(dacc, use_id) :=
                DA.record_continuation_use dacc apply_return_continuation
                  (Continuation_use_kind.Non_inlinable true) env_at_use
                  arg_types
              in
              ret (T3 dacc (Some use_id) result_continuation))
        end
      in
      let* env_at_use := DA.denv dacc in
      let* env_at_use :=
        let! tmp1 := Code_metadata.cold callee's_code_metadata in
        if tmp1 then DE.mark_as_cold env_at_use else ret env_at_use
      in
      (* 411-420: the arguments are in the order of the interface. *)
      let* '(dacc, exn_cont_use_id) :=
        let! tmp1 := Apply.exn_continuation apply in
        let! tmp2 := Exn_continuation.arity tmp1 in
        let! tmp3 := DA.denv dacc in
        let! tmp4 := DE.machine_width tmp3 in
        let! tmp5 := T.unknown_types_from_arity None tmp4 tmp2 in
        let! tmp6 := Apply.exn_continuation apply in
        let! tmp7 := Exn_continuation.exn_handler tmp6 in
        DA.record_continuation_use dacc tmp7
          (Continuation_use_kind.Non_inlinable true) env_at_use tmp5
      in
      let* apply := Apply.with_continuation apply result_continuation in
      let* dacc :=
        record_free_names_of_apply_as_used dacc use_id exn_cont_use_id apply
      in
      let* expr :=
        let! tmp1 := Code_metadata.cold callee's_code_metadata in
        SE.simplified_apply (Some result_arity) apply use_id exn_cont_use_id
          tmp1
      in
      let* expr :=
        update_direct_call_benefit expr original_call callee's_code_metadata
      in
      down_to_up dacc expr
    end
  end.

(* PORT-GAP(unported): 441-851, [simplify_direct_partial_application]. In
   the compiler: [~simplify_expr dacc apply ~callee's_code_id
   ~callee's_code_metadata ~callee's_function_slot ~param_arity ~param_modes
   ~args_arity ~result_arity ~recursive ~down_to_up ~original_call
   ~closure_alloc_mode_from_type ~first_complex_local_param]. *)
Parameter simplify_direct_partial_application :
  Simplify_common.expr_simplifier Expr.t -> DA.t -> Apply.t -> Code_id.t ->
  Code_metadata.t -> Function_slot.t -> Flambda_arity.t_Complex ->
  list Alloc_mode.For_types.t -> Flambda_arity.t_Complex ->
  Flambda_arity.t_Complex -> Recursive.t -> Simplify_common.down_to_up SE.t ->
  Call_kind.Function_call.t -> Alloc_mode.For_types.t ->
  First_complex_local_param.t -> M (SE.t * DA.t).
Extract Constant simplify_direct_partial_application => "fun _ -> Misc.fatal_error ""PORT-GAP(unported): simplify_direct_partial_application""".

(* 853-871. In the compiler: [~simplify_expr dacc apply ~down_to_up
   ~original_call ~callee's_code_id ~callee's_code_metadata]. *)
Definition simplify_direct_over_application
    (simplify_expr : Simplify_common.expr_simplifier Expr.t) (dacc : DA.t)
    (apply : Apply.t) (down_to_up : Simplify_common.down_to_up SE.t)
    (original_call : Call_kind.Function_call.t) (callee's_code_id : Code_id.t)
    (callee's_code_metadata : Code_metadata.t) : M (SE.t * DA.t) :=
  fail_if_probe apply ;;
  let* expr :=
    Simplify_common.split_direct_over_application apply callee's_code_id
      callee's_code_metadata
  in
  let& down_to_up :=
    fun (dacc : DA.t) (expr : SE.t) =>
    let* expr :=
      match original_call with
      | Call_kind.Function_call.Direct _ => ret expr
      | Call_kind.Function_call.Indirect_known_arity _
      | Call_kind.Function_call.Indirect_unknown_arity =>
        SE.notify_removed Removed_operations.direct_call_of_indirect expr
      end
    in
    down_to_up dacc expr
  in
  simplify_expr dacc expr down_to_up.

(* 873-874. In the compiler: [dacc ~down_to_up reason]. *)
Definition replace_apply_by_invalid (dacc : DA.t)
    (down_to_up : Simplify_common.down_to_up SE.t)
    (reason : Flambda.Invalid.t) : M (SE.t * DA.t) :=
  let! tmp1 := SE.simplified_invalid reason in
  down_to_up dacc tmp1.

(* 876-896. In the compiler: [~params_arity ~args_arity]. *)
(* PORT-GAP(loose): 880-893, Rocq prints the local function [has_mismatch]
   after the two [let]s of lines 894-895, where it is used, and not before
   them. *)
Definition arity_mismatch (params_arity : Flambda_arity.t_Complex)
    (args_arity : Flambda_arity.t_Complex) : M bool :=
  (* This checks the shortest of the two arities against the prefix of the same
     size of the other. 880: a local [let rec] that Rocq sees to end, on the
     list [params]. *)
  let has_mismatch :=
    fix has_mismatch (params args : list (list KS.t)) {struct params}
        : M bool :=
      match params, args with
      | [], _ | _, [] => ret false
      | param :: params, arg :: args =>
        let* c := List.compare_lengths param arg in
        if c =? 0
        then
          let! tmp1 :=
            List.exists2_
              (fun param_component arg_component =>
                let! tmp2 := KS.kind arg_component in
                let! tmp3 := KS.kind param_component in
                let! tmp4 := K.equal tmp3 tmp2 in
                ret (negb tmp4))
              param arg
          in
          or_else tmp1 (has_mismatch params args)
        else ret true
      end
  in
  let* params := Flambda_arity.unarize_per_parameter params_arity in
  let* args := Flambda_arity.unarize_per_parameter args_arity in
  has_mismatch params args.

(* 898-966. In the compiler: [dacc apply call ~down_to_up]. *)
Definition simplify_function_call_where_callee's_type_unavailable
    (dacc : DA.t) (apply : Apply.t) (call : Call_kind.Function_call.t)
    (down_to_up : Simplify_common.down_to_up SE.t) : M (SE.t * DA.t) :=
  fail_if_probe apply ;;
  let* denv := DA.denv dacc in
  (* 902-907: the arguments are in the order of the interface. *)
  (let! tmp1 := DE.are_rebuilding_terms denv in
   let! tmp2 := Are_rebuilding_terms.do_rebuild_terms tmp1 in
   if tmp2
   then
     let! tmp3 := DE.inlining_history_tracker denv in
     Inlining_report.record_decision_at_call_site_for_unknown_function tmp3
       apply Inlining_report.Pass.Before_simplify tt
   else ret tt) ;;
  let& env_at_use := denv in
  let* '(dacc, use_id) :=
    let! tmp1 := Apply.continuation apply in
    match tmp1 with
    | Apply_expr.Result_continuation.Never_returns => ret (dacc, None)
    | Apply_expr.Result_continuation.Return continuation =>
      (* 913-921: the arguments are in the order of the interface. *)
      let* '(dacc, use_id) :=
        let! tmp1 := Apply.return_arity apply in
        let! tmp2 := DE.machine_width denv in
        let! tmp3 := Apply.return_mode apply in
        let! tmp4 := Alloc_mode.For_applications.as_type tmp3 in
        let! tmp5 := T.unknown_types_from_arity (Some tmp4) tmp2 tmp1 in
        DA.record_continuation_use dacc continuation
          (Continuation_use_kind.Non_inlinable true) env_at_use tmp5
      in
      ret (dacc, Some use_id)
    end
  in
  (* 925-934: the arguments are in the order of the interface. *)
  let* '(dacc, exn_cont_use_id) :=
    let! tmp1 := Apply.exn_continuation apply in
    let! tmp2 := Exn_continuation.arity tmp1 in
    let! tmp3 := DA.denv dacc in
    let! tmp4 := DE.machine_width tmp3 in
    let! tmp5 := T.unknown_types_from_arity None tmp4 tmp2 in
    let! tmp6 := DA.denv dacc in
    let! tmp7 := Apply.exn_continuation apply in
    let! tmp8 := Exn_continuation.exn_handler tmp7 in
    DA.record_continuation_use dacc tmp8
      (Continuation_use_kind.Non_inlinable true) tmp6 tmp5
  in
  let* call_kind :=
    match call with
    | Call_kind.Function_call.Indirect_unknown_arity =>
      ret Call_kind.indirect_function_call_unknown_arity
    | Call_kind.Function_call.Indirect_known_arity Or_unknown.Unknown =>
      Call_kind.indirect_function_call_known_arity Or_unknown.Unknown
    | Call_kind.Function_call.Indirect_known_arity (Or_unknown.Known code_ids)
      =>
      (* If this records a non-simplified code id, we can't continue keeping
         track of the possible code ids without maintaining this non-simplified
         code id alive, so we just forget everything. *)
      let! tmp1 := DA.code_ids_never_simplified dacc in
      let! tmp2 := Code_id.Set_.disjoint code_ids tmp1 in
      if tmp2
      then
        Call_kind.indirect_function_call_known_arity (Or_unknown.Known code_ids)
      else Call_kind.indirect_function_call_known_arity Or_unknown.Unknown
    | Call_kind.Function_call.Direct code_id =>
      (* Keep the code ID if it corresponds to a simplified function, otherwise
         demote it to avoid keeping non-simplified code alive. Keep the
         function's arity as it is never allowed to change. *)
      let! tmp1 := DA.code_ids_never_simplified dacc in
      let! tmp2 := Code_id.Set_.mem code_id tmp1 in
      if tmp2
      then Call_kind.indirect_function_call_known_arity Or_unknown.Unknown
      else Call_kind.direct_function_call code_id
    end
  in
  let* apply := Apply_expr.with_call_kind apply call_kind in
  let* apply :=
    let! tmp1 := Apply.inlined apply in
    let! tmp2 :=
      Inlined_attribute.with_use_info tmp1
        Inlined_attribute.Use_info.Unused_because_function_unknown
    in
    Apply_expr.with_inlined_attribute apply tmp2
  in
  let* dacc :=
    record_free_names_of_apply_as_used dacc use_id exn_cont_use_id apply
  in
  let! tmp1 := SE.simplified_apply None apply use_id exn_cont_use_id false in
  down_to_up dacc tmp1.

(* 968-1145. In the compiler: [~simplify_expr ~rebuild_expr dacc apply
   ~callee's_code_id_from_type ~callee's_code_metadata_from_type
   ~callee's_code_ids_from_call_kind ~callee's_function_slot ~original_call
   ~result_arity ~result_types ~recursive ~must_be_detupled
   ~closure_alloc_mode_from_type function_decl ~down_to_up ~call
   ~inlined_forwarded_from]. *)
Definition simplify_direct_function_call
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (rebuild_expr : Simplify_common.rebuild SE.t) (dacc : DA.t)
    (apply : Apply.t) (callee's_code_id_from_type : Code_id.t)
    (callee's_code_metadata_from_type : Code_metadata.t)
    (callee's_code_ids_from_call_kind : Or_unknown.t Code_id.Set_.t)
    (callee's_function_slot : Function_slot.t)
    (original_call : Call_kind.Function_call.t)
    (result_arity : Flambda_arity.t_Complex)
    (result_types : Or_unknown_or_bottom.t Result_types.t)
    (recursive : Recursive.t) (must_be_detupled : bool)
    (closure_alloc_mode_from_type : Alloc_mode.For_types.t)
    (function_decl : T.Function_type.t)
    (down_to_up : Simplify_common.down_to_up SE.t)
    (call : Call_kind.Function_call.t)
    (inlined_forwarded_from : option Inlined_debuginfo.t)
    : M (SE.t * DA.t) :=
  (* 974-989: the two calls that are the values of the match are bound by
     [let*], the last first. *)
  let* result_types :=
    let* inlined := Apply.inlined apply in
    let* probe := Apply.probe apply in
    match probe, inlined with
    | None, _ => ret result_types
    | Some _, Inlined_attribute.Never_inlined =>
      (* The handler of a disabled probe is not called, so nothing can be
         deduced from its result types (in particular, the probe may return even
         if the handler never does). *)
      ret Or_unknown_or_bottom.Unknown
    | Some _,
      ( Inlined_attribute.Hint_inlined | Inlined_attribute.Forward_inlined
      | Inlined_attribute.Unroll _ _ | Inlined_attribute.Default_inlined
      | Inlined_attribute.Always_inlined _ ) =>
      fatal_errorf2
        "[Apply] terms with a [probe] (i.e. that call a tracing probe) must always be marked as [Never_inline]:@ %a"
        Apply.print apply
    end
  in
  let* callee's_code_ids :=
    match callee's_code_ids_from_call_kind with
    | Or_unknown.Unknown =>
      let! tmp1 := Code_id.Set_.singleton callee's_code_id_from_type in
      ret (Or_bottom.Ok tmp1)
    | Or_unknown.Known callee's_code_ids_from_call_kind =>
      let* typing_env := DA.typing_env dacc in
      (* PORT-GAP(papp): 997, [TE.code_age_relation_resolver] is given its
         first argument only. *)
      let! tmp1 := Code_id.Set_.singleton callee's_code_id_from_type in
      let! tmp2 := papp1 TE.code_age_relation_resolver typing_env in
      let! tmp3 := TE.code_age_relation typing_env in
      T.Code_age_relation.meet_set tmp3 tmp2 callee's_code_ids_from_call_kind
        tmp1
    end
  in
  match callee's_code_ids with
  | Or_bottom.Bottom =>
    replace_apply_by_invalid dacc down_to_up
      (Flambda.Invalid.Closure_type_was_invalid apply)
  | Or_bottom.Ok callee's_code_ids =>
    let* '(callee's_code_id, callee's_code_metadata) :=
      let! tmp1 := Code_id.Set_.get_singleton callee's_code_ids in
      match tmp1 with
      | None =>
        ret (callee's_code_id_from_type, callee's_code_metadata_from_type)
      | Some callee's_code_id =>
        match_exn
          (fun _ =>
            let! tmp1 := DA.denv dacc in
            DE.find_code_metadata_exn tmp1 callee's_code_id)
          Not_found
          (fun _ =>
            (* This can happen if we have a more precise code id from the call
               kind, but we don't have the metadata for it. This should be rare
               (and will trigger warning 58 when we try to load the metadata for
               this code id); in that case, we use the metadata that we do have
               available for the code id from the type. *)
            ret (callee's_code_id_from_type, callee's_code_metadata_from_type))
          (fun callee's_code_metadata =>
            ret (callee's_code_id, callee's_code_metadata))
      end
    in
    let* call_kind := Call_kind.direct_function_call callee's_code_id in
    let* apply := Apply.with_call_kind apply call_kind in
    let* params_arity := Code_metadata.params_arity callee's_code_metadata in
    (* A function declaration with [is_tupled = true] must be treated specially:

       - Direct calls adopt the normal calling convention of the code's body,
       i.e. that given by [Code.params_arity].

       - Indirect calls adopt the calling convention consisting of a single
       tuple argument, irrespective of what [Code.params_arity] says. *)
    let* args_arity := Apply.args_arity apply in
    if must_be_detupled
    then
      simplify_direct_tuple_application simplify_expr dacc apply
        callee's_code_id callee's_code_metadata down_to_up
    else
      let! tmp1 := arity_mismatch params_arity args_arity in
      if tmp1
      then
        let! tmp2 := Flambda_features.kind_checks tt in
        if tmp2
        then
          fatal_errorf6
            "Mismatched arities for arguments to direct OCaml function call@ (expected %a, found %a):@ %a"
            Flambda_arity.print params_arity Flambda_arity.print args_arity
            Apply.print apply
        else
          replace_apply_by_invalid dacc down_to_up
            (Flambda.Invalid.Direct_application_parameter_kind_mismatch
               params_arity args_arity apply)
      else
        let* args_arity := Apply.args_arity apply in
        let* provided_num_args := Flambda_arity.num_params args_arity in
        let* num_params := Flambda_arity.num_params params_arity in
        let* result_arity_of_application := Apply.return_arity apply in
        if provided_num_args =? num_params
        then
          (* This check can only be performed for exact applications:

             - In the partial application case, the type checker should have
             specified kind Value as the return kind of the application
             (propagated through Lambda to this point), and it would be wrong to
             compare against the return arity of the fully-applied function.

             - In the overapplication case, the correct return arity is only
             present on the application expression, so all we can do is check
             that the function being overapplied returns kind Value. *)
          let! tmp2 :=
            Flambda_arity.equal_ignoring_subkinds result_arity
              result_arity_of_application
          in
          if negb tmp2
          then
            let! tmp3 := Flambda_features.kind_checks tt in
            if tmp3
            then
              fatal_errorf6
                "Wrong return arity for direct OCaml function call@ (expected %a, found %a):@ %a"
                Flambda_arity.print result_arity Flambda_arity.print
                result_arity_of_application Apply.print apply
            else
              replace_apply_by_invalid dacc down_to_up
                (Flambda.Invalid.Application_result_kind_mismatch result_arity
                   apply)
          else
            simplify_direct_full_application simplify_expr rebuild_expr dacc
              apply (Some function_decl) params_arity result_arity result_types
              down_to_up original_call callee's_code_metadata
              inlined_forwarded_from
        else if provided_num_args >? num_params
        then
          (* See comment above. *)
          let! tmp2 := Flambda_arity.is_one_param_of_kind_value result_arity in
          if negb tmp2
          then
            let! tmp3 := Flambda_features.kind_checks tt in
            if tmp3
            then
              fatal_errorf2
                "Non-singleton-value return arity for overapplied OCaml function:@ %a"
                Apply.print apply
            else
              replace_apply_by_invalid dacc down_to_up
                (Flambda.Invalid.Application_result_kind_mismatch result_arity
                   apply)
          else
            simplify_direct_over_application simplify_expr dacc apply down_to_up
              original_call callee's_code_id callee's_code_metadata
        else if (provided_num_args >? 0) && (provided_num_args <? num_params)
        then
          (* See comment above. *)
          let! tmp2 :=
            Flambda_arity.is_one_param_of_kind_value result_arity_of_application
          in
          if negb tmp2
          then
            let! tmp3 := Flambda_features.kind_checks tt in
            if tmp3
            then
              fatal_errorf2
                "Non-singleton-value return arity for partially-applied OCaml function:@ %a"
                Apply.print apply
            else
              let! tmp4 :=
                Flambda_arity.create_singletons
                  [Flambda_kind.With_subkind.any_value]
              in
              replace_apply_by_invalid dacc down_to_up
                (Flambda.Invalid.Application_result_kind_mismatch tmp4 apply)
          else
            let! tmp3 := DA.denv dacc in
            let! tmp4 := DE.disable_partial_application_stub_generation tmp3 in
            if tmp4
            then
              simplify_function_call_where_callee's_type_unavailable dacc apply
                call down_to_up
            else
              (* 1133-1140: the arguments are in the order of the definition. *)
              let! tmp5 :=
                Code_metadata.first_complex_local_param callee's_code_metadata
              in
              let! tmp6 := Code_metadata.param_modes callee's_code_metadata in
              simplify_direct_partial_application simplify_expr dacc apply
                callee's_code_id callee's_code_metadata callee's_function_slot
                params_arity tmp6 args_arity result_arity recursive down_to_up
                original_call closure_alloc_mode_from_type tmp5
        else
          fatal_errorf4
            "Function with %d params when simplifying direct OCaml function call with %d arguments: %a"
            num_params provided_num_args Apply.print apply
  end.

(* 1147-1263. In the compiler: [~simplify_expr ~rebuild_expr dacc apply
   ~callee_ty call ~down_to_up ~inlined_forwarded_from]. *)
Definition simplify_function_call
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (rebuild_expr : Simplify_common.rebuild SE.t) (dacc : DA.t)
    (apply : Apply.t) (callee_ty : option T.t)
    (call : Call_kind.Function_call.t)
    (down_to_up : Simplify_common.down_to_up SE.t)
    (inlined_forwarded_from : option Inlined_debuginfo.t)
    : M (SE.t * DA.t) :=
  (* Function declarations and params and body might not have the same calling
     convention. Currently the only case when it happens is for tupled
     functions. For such functions, the function_declaration declares a
     param_arity with a single argument (which is the tuple), whereas the code
     body takes an argument for each field of the tuple (the body is currified).

     When simplifying a function call, it can happen that we need to change the
     calling convention. Currently this only happens when we have a generic call
     (Indirect_unknown_arity), which uses the generic/function_declaration
     calling convention, but we simplify it into a direct call, which uses the
     callee's code calling convention. In this case, we need to "detuple" the
     call in order to correctly adapt to the change in calling convention. *)
  let& call_must_be_detupled :=
    fun (is_function_decl_tupled : bool) =>
    match call with
    | Call_kind.Function_call.Direct _
    | Call_kind.Function_call.Indirect_known_arity _ =>
      (* In these cases, the calling convention already used in the application
         being simplified is that of the code actually called. Thus we must not
         detuple the function. *)
      ret false
    | Call_kind.Function_call.Indirect_unknown_arity =>
      (* In the indirect case, the calling convention used currently is the
         generic one. Thus we need to detuple the call iff the function
         declaration is tupled. *)
      ret is_function_decl_tupled
    end
  in
  let& type_unavailable :=
    fun (call : Call_kind.Function_call.t) =>
    simplify_function_call_where_callee's_type_unavailable dacc apply call
      down_to_up
  in
  let& not_a_closure :=
    fun (_ : unit) =>
    let! tmp1 :=
      SE.simplified_invalid (Flambda.Invalid.Closure_type_was_invalid apply)
    in
    down_to_up dacc tmp1
  in
  let* denv := DA.denv dacc in
  match callee_ty with
  | None =>
    match call with
    | Call_kind.Function_call.Direct callee's_code_id =>
      match_exn
        (fun _ => DE.find_code_metadata_exn denv callee's_code_id)
        Not_found
        (fun _ => type_unavailable call)
        (fun callee's_code_metadata =>
          (* 1191-1197: the arguments are in the order of the definition. *)
          let! tmp1 := Code_metadata.result_types callee's_code_metadata in
          let! tmp2 := Code_metadata.result_arity callee's_code_metadata in
          let! tmp3 := Code_metadata.params_arity callee's_code_metadata in
          simplify_direct_full_application simplify_expr rebuild_expr dacc
            apply None tmp3 tmp2 tmp1 down_to_up call callee's_code_metadata
            inlined_forwarded_from)
    | Call_kind.Function_call.Indirect_known_arity _
    | Call_kind.Function_call.Indirect_unknown_arity =>
      fatal_errorf2
        "No callee provided for non-direct OCaml function call:@ %a"
        Apply.print apply
    end
  | Some callee_ty =>
    let! tmp1 := DE.typing_env denv in
    let! tmp2 := T.meet_single_closures_entry tmp1 callee_ty in
    match tmp2 with
    | T.Known_result
        (T4 callee's_function_slot closure_alloc_mode_from_type
           _closures_entry func_decl_type) =>
      let* callee's_code_ids_from_call_kind :=
        match call with
        | Call_kind.Function_call.Direct code_id =>
          let! tmp1 := Code_id.Set_.singleton code_id in
          ret (Or_unknown.Known tmp1)
        | Call_kind.Function_call.Indirect_known_arity code_ids => ret code_ids
        | Call_kind.Function_call.Indirect_unknown_arity =>
          ret Or_unknown.Unknown
        end
      in
      let* callee's_code_id_from_type :=
        T.Function_type.code_id func_decl_type
      in
      match_exn
        (fun _ => DE.find_code_metadata_exn denv callee's_code_id_from_type)
        Not_found
        (fun _ => type_unavailable call)
        (fun callee's_code_metadata_from_type =>
          let* must_be_detupled :=
            let! tmp1 :=
              Code_metadata.is_tupled callee's_code_metadata_from_type
            in
            call_must_be_detupled tmp1
          in
          (* 1223-1233: the arguments are in the order of the definition. *)
          let! tmp1 := Code_metadata.recursive callee's_code_metadata_from_type in
          let! tmp2 :=
            Code_metadata.result_types callee's_code_metadata_from_type
          in
          let! tmp3 :=
            Code_metadata.result_arity callee's_code_metadata_from_type
          in
          simplify_direct_function_call simplify_expr rebuild_expr dacc apply
            callee's_code_id_from_type callee's_code_metadata_from_type
            callee's_code_ids_from_call_kind callee's_function_slot call tmp3
            tmp2 tmp1 must_be_detupled closure_alloc_mode_from_type
            func_decl_type down_to_up call inlined_forwarded_from)
    | T.Need_meet =>
      match call with
      | Call_kind.Function_call.Direct _
      | Call_kind.Function_call.Indirect_known_arity _ =>
        type_unavailable call
      | Call_kind.Function_call.Indirect_unknown_arity =>
        (* If the call is to a known set of potential code IDs that all have the
           same arity as the actual arguments of the call, promote it to an
           [Indirect_known_arity] call, skipping [caml_applyN]. *)
        let! tmp1 := DE.typing_env denv in
        let! tmp2 := T.meet_code_ids tmp1 callee_ty in
        match tmp2 with
        | T.Known_result code_ids =>
          let* args_arity := Apply.args_arity apply in
          let! tmp1 :=
            Code_id.Set_.for_all
              (fun code_id =>
                match_exn
                  (fun _ => DE.find_code_metadata_exn denv code_id)
                  Not_found
                  (fun _ => ret false)
                  (fun code_metadata =>
                    let* params_arity :=
                      Code_metadata.params_arity code_metadata
                    in
                    let* is_tupled := Code_metadata.is_tupled code_metadata in
                    and_then (negb is_tupled)
                      (Flambda_arity.equal_ignoring_subkinds args_arity
                         params_arity)))
              code_ids
          in
          if tmp1
          then
            let! tmp2 :=
              Call_kind.Function_call.indirect_known_arity
                (Or_unknown.Known code_ids)
            in
            type_unavailable tmp2
          else type_unavailable call
        | T.Need_meet => type_unavailable call
        | T.Invalid => not_a_closure tt
        end
      end
    | T.Invalid => not_a_closure tt
    end
  end.

(* 1265-1267 *)
Inductive simplify_apply_shared_result (A B : Type) : Type :=
| Ok (a : A)
| Invalid (b : B).
Arguments Ok {A B}.
Arguments Invalid {A B}.

(* 1269-1336 *)
Definition simplify_apply_shared (dacc : DA.t) (apply : Apply.t)
    : M (simplify_apply_shared_result
           (tuple5 DA.t (option T.t) Apply.t (list T.t)
              (option Inlined_debuginfo.t))
           Flambda_arity.t_Unarized) :=
  let* '(callee_ty, simplified_callee) :=
    let! tmp1 := Apply.callee apply in
    match tmp1 with
    | None => ret (None, None)
    | Some callee =>
      let* '(callee_ty, simplified_callee) :=
        S.simplify_simple dacc callee NM.normal
      in
      ret (Some callee_ty, Some simplified_callee)
    end
  in
  let* '{| S.simples := args; S.simple_tys := arg_types |} :=
    let! tmp1 := Apply.args apply in
    S.simplify_simples dacc tmp1
  in
  let* kind_mismatch := mk_ref false in
  (* 1283-1296 *)
  (let! tmp1 := Apply.args_arity apply in
   let! tmp2 := Flambda_arity.unarize tmp1 in
   List.iter2
     (fun kind_with_subkind arg_type =>
       let* kind := K.With_subkind.kind kind_with_subkind in
       let! tmp3 := T.kind arg_type in
       let! tmp4 := K.equal kind tmp3 in
       if negb tmp4
       then
         let! tmp5 := Flambda_features.kind_checks tt in
         if negb tmp5
         then set kind_mismatch true
         else
           fatal_errorf6
             "Argument kind %a from arity does not match kind from type %a for application:@ %a"
             K.print kind T.print arg_type Apply.print apply
       else ret tt)
     tmp2 arg_types) ;;
  let! tmp1 := get kind_mismatch in
  if tmp1
  then
    (* 1299-1302: [a |> f] is [f a]. *)
    let! tmp2 := List.map T.kind arg_types in
    let! tmp3 := List.map K.With_subkind.anything tmp2 in
    let! tmp4 := Flambda_arity.create_singletons tmp3 in
    ret (Invalid tmp4)
  else
    let* inlining_state :=
      let! tmp2 := Apply.inlining_state apply in
      let! tmp3 := DA.denv dacc in
      let! tmp4 := DE.get_inlining_state tmp3 in
      Inlining_state.combine tmp4 tmp2
    in
    (* 1309-1319: the match names its scrutinee ([... as inlined]). *)
    let* '(inlined, inlined_forwarded_from) :=
      let* inlined := Apply.inlined apply in
      match inlined with
      | Inlined_attribute.Never_inlined | Inlined_attribute.Default_inlined
      | Inlined_attribute.Unroll _ _ | Inlined_attribute.Always_inlined _
      | Inlined_attribute.Hint_inlined =>
        ret (inlined, None)
      | Inlined_attribute.Forward_inlined =>
        let! tmp2 := DA.denv dacc in
        let! tmp3 := DE.inlined_attribute_to_forward tmp2 in
        match tmp3 with
        | None => ret (inlined, None)
        | Some labelled =>
          match_inlined_attribute_to_forward labelled
            (fun inlined_from_env forwarded_from =>
              ret (inlined_from_env, Some forwarded_from))
        end
      end
    in
    (* 1320-1335: the arguments are in the order of the interface. *)
    let* apply :=
      let! tmp2 := Apply.relative_history apply in
      let! tmp3 := DA.denv dacc in
      let! tmp4 := DE.relative_history tmp3 in
      let! tmp5 := Inlining_history.Relative.concat tmp4 tmp2 in
      let! tmp6 := Apply.position apply in
      let! tmp7 := Apply.probe apply in
      let! tmp8 := Apply.dbg apply in
      let! tmp9 := DA.denv dacc in
      let! tmp10 := DE.add_inlined_debuginfo tmp9 tmp8 in
      let! tmp11 := Apply.return_mode apply in
      let! tmp12 := Apply.call_kind apply in
      let! tmp13 := Apply.return_arity apply in
      let! tmp14 := Apply.args_arity apply in
      let! tmp15 := Apply.exn_continuation apply in
      let! tmp16 := Apply.continuation apply in
      Apply.create simplified_callee tmp16 tmp15 args tmp14 tmp13 tmp12 tmp11
        tmp10 inlined inlining_state tmp7 tmp6 tmp5
    in
    ret (Ok (T5 dacc callee_ty apply arg_types inlined_forwarded_from)).

(* 1338-1379. In the compiler: [dacc apply ~callee_ty ~kind:_ ~obj
   ~down_to_up]. *)
Definition simplify_method_call (dacc : DA.t) (apply : Apply.t)
    (callee_ty : T.t) (_ : Call_kind.Method_kind.t) (obj : Simple.t)
    (down_to_up : Simplify_common.down_to_up SE.t) : M (SE.t * DA.t) :=
  fail_if_probe apply ;;
  let* callee_kind := T.kind callee_ty in
  (let! tmp1 := K.is_value callee_kind in
   if negb tmp1
   then
     fatal_errorf4 "Method call with callee of wrong kind %a: %a" K.print
       callee_kind T.print callee_ty
   else ret tt) ;;
  let* apply_cont :=
    let! tmp1 := Apply.continuation apply in
    match tmp1 with
    | Apply_expr.Result_continuation.Never_returns =>
      fatal_error "Cannot simplify a method call that never returns"
    | Apply_expr.Result_continuation.Return continuation => ret continuation
    end
  in
  let* denv := DA.denv dacc in
  DE.check_simple_is_bound denv obj ;;
  (* 1353-1361: the arguments are in the order of the interface. *)
  let* '(dacc, use_id) :=
    let! tmp1 := Apply.return_arity apply in
    let! tmp2 := DE.machine_width denv in
    let! tmp3 := Apply.return_mode apply in
    let! tmp4 := Alloc_mode.For_applications.as_type tmp3 in
    let! tmp5 := T.unknown_types_from_arity (Some tmp4) tmp2 tmp1 in
    DA.record_continuation_use dacc apply_cont
      (Continuation_use_kind.Non_inlinable true) denv tmp5
  in
  (* 1363-1372: the arguments are in the order of the interface. *)
  let* '(dacc, exn_cont_use_id) :=
    let! tmp1 := Apply.exn_continuation apply in
    let! tmp2 := Exn_continuation.arity tmp1 in
    let! tmp3 := DA.denv dacc in
    let! tmp4 := DE.machine_width tmp3 in
    let! tmp5 := T.unknown_types_from_arity None tmp4 tmp2 in
    let! tmp6 := DA.denv dacc in
    let! tmp7 := Apply.exn_continuation apply in
    let! tmp8 := Exn_continuation.exn_handler tmp7 in
    DA.record_continuation_use dacc tmp8
      (Continuation_use_kind.Non_inlinable true) tmp6 tmp5
  in
  let* dacc :=
    record_free_names_of_apply_as_used dacc (Some use_id) exn_cont_use_id apply
  in
  let! tmp1 :=
    SE.simplified_apply None apply (Some use_id) exn_cont_use_id false
  in
  down_to_up dacc tmp1.

(* 1381-1440. In the compiler: [~simplify_expr dacc apply ~callee_ty
   ~arg_types ~down_to_up]. *)
Definition simplify_c_call
    (simplify_expr : Simplify_common.expr_simplifier Expr.t) (dacc : DA.t)
    (apply : Apply.t) (callee_ty : T.t) (arg_types : list T.t)
    (down_to_up : Simplify_common.down_to_up SE.t) : M (SE.t * DA.t) :=
  fail_if_probe apply ;;
  let* return_arity := Apply.return_arity apply in
  let* callee_kind := T.kind callee_ty in
  (let! tmp1 := K.is_value callee_kind in
   if negb tmp1
   then
     fatal_errorf4 "C callees must be of kind [Value], not %a: %a" K.print
       callee_kind T.print callee_ty
   else ret tt) ;;
  let* simplified :=
    Simplify_extcall.simplify_extcall dacc apply callee_ty arg_types
  in
  match simplified with
  | Simplify_extcall.Specialised dacc expr operation =>
    let& down_to_up :=
      fun (dacc : DA.t) (expr : SE.t) =>
      let! tmp1 := SE.notify_removed operation expr in
      down_to_up dacc tmp1
    in
    simplify_expr dacc expr down_to_up
  | Simplify_extcall.Unchanged return_types =>
    let* '(dacc, use_id) :=
      let! tmp1 := Apply.continuation apply in
      match tmp1 with
      | Apply_expr.Result_continuation.Return apply_continuation =>
        let* apply_continuation_arg_types :=
          (* 1404-1409: the arguments are in the order of the interface. *)
          let* from_arity :=
            let! tmp1 := DA.denv dacc in
            let! tmp2 := DE.machine_width tmp1 in
            let! tmp3 := Apply.return_mode apply in
            let! tmp4 := Alloc_mode.For_applications.as_type tmp3 in
            T.unknown_types_from_arity (Some tmp4) tmp2 return_arity
          in
          match return_types with
          | Or_unknown.Unknown => ret from_arity
          | Or_unknown.Known return_types =>
            (let! tmp1 := List.compare_lengths return_types from_arity in
             assert_ (tmp1 =? 0)) ;;
            ret return_types
          end
        in
        let* '(dacc, use_id) :=
          let! tmp1 := DA.denv dacc in
          DA.record_continuation_use dacc apply_continuation
            (Continuation_use_kind.Non_inlinable true) tmp1
            apply_continuation_arg_types
        in
        ret (dacc, Some use_id)
      | Apply_expr.Result_continuation.Never_returns => ret (dacc, None)
      end
    in
    (* 1424-1433: the arguments are in the order of the interface. *)
    let* '(dacc, exn_cont_use_id) :=
      let! tmp1 := Apply.exn_continuation apply in
      let! tmp2 := Exn_continuation.arity tmp1 in
      let! tmp3 := DA.denv dacc in
      let! tmp4 := DE.machine_width tmp3 in
      let! tmp5 := T.unknown_types_from_arity None tmp4 tmp2 in
      let! tmp6 := DA.denv dacc in
      let! tmp7 := Apply.exn_continuation apply in
      let! tmp8 := Exn_continuation.exn_handler tmp7 in
      DA.record_continuation_use dacc tmp8
        (Continuation_use_kind.Non_inlinable true) tmp6 tmp5
    in
    let* dacc :=
      record_free_names_of_apply_as_used dacc use_id exn_cont_use_id apply
    in
    let! tmp1 := SE.simplified_apply None apply use_id exn_cont_use_id false in
    down_to_up dacc tmp1
  | Simplify_extcall.Invalid =>
    replace_apply_by_invalid dacc down_to_up
      (Flambda.Invalid.Closure_type_was_invalid apply)
  end.

(* 1442-1506. In the compiler: [dacc apply op ~down_to_up]. *)
Definition simplify_effect_op (dacc : DA.t) (apply : Apply.t)
    (op : Call_kind.Effect.t) (down_to_up : Simplify_common.down_to_up SE.t)
    : M (SE.t * DA.t) :=
  fail_if_probe apply ;;
  let* denv := DA.denv dacc in
  (* PORT-GAP(loose): 1446, [let module E = Call_kind.Effect in] is not kept:
     [E.perform] is [Call_kind.Effect.perform]; 1447, the attribute [@inline]
     is not kept. *)
  let* op :=
    let& simplify_simple :=
      fun (simple : Simple.t) =>
      let* '(_ty, simple) := S.simplify_simple dacc simple NM.normal in
      ret simple
    in
    match op with
    | Call_kind.Effect.Perform eff =>
      let! tmp1 := simplify_simple eff in
      Call_kind.Effect.perform tmp1
    | Call_kind.Effect.Reperform eff cont last_fiber =>
      let! tmp1 := simplify_simple last_fiber in
      let! tmp2 := simplify_simple cont in
      let! tmp3 := simplify_simple eff in
      Call_kind.Effect.reperform tmp3 tmp2 tmp1
    | Call_kind.Effect.With_stack valuec exnc effc f arg =>
      let! tmp1 := simplify_simple arg in
      let! tmp2 := simplify_simple f in
      let! tmp3 := simplify_simple effc in
      let! tmp4 := simplify_simple exnc in
      let! tmp5 := simplify_simple valuec in
      Call_kind.Effect.with_stack tmp5 tmp4 tmp3 tmp2 tmp1
    | Call_kind.Effect.With_stack_preemptible valuec exnc effc handle_tick f
        arg =>
      let! tmp1 := simplify_simple arg in
      let! tmp2 := simplify_simple f in
      let! tmp3 := simplify_simple handle_tick in
      let! tmp4 := simplify_simple effc in
      let! tmp5 := simplify_simple exnc in
      let! tmp6 := simplify_simple valuec in
      Call_kind.Effect.with_stack_preemptible tmp6 tmp5 tmp4 tmp3 tmp2 tmp1
    | Call_kind.Effect.Continue cont value =>
      let! tmp1 := simplify_simple value in
      let! tmp2 := simplify_simple cont in
      Call_kind.Effect.continue tmp2 tmp1
    | Call_kind.Effect.Discontinue cont exn =>
      let! tmp1 := simplify_simple exn in
      let! tmp2 := simplify_simple cont in
      Call_kind.Effect.discontinue tmp2 tmp1
    | Call_kind.Effect.Discontinue_with_backtrace cont exn bt =>
      let! tmp1 := simplify_simple bt in
      let! tmp2 := simplify_simple exn in
      let! tmp3 := simplify_simple cont in
      Call_kind.Effect.discontinue_with_backtrace tmp3 tmp2 tmp1
    end
  in
  let* apply :=
    let! tmp1 := Call_kind.effect_ op in
    Apply.with_call_kind apply tmp1
  in
  let* '(dacc, use_id) :=
    let! tmp1 := Apply.continuation apply in
    match tmp1 with
    | Apply_expr.Result_continuation.Never_returns => ret (dacc, None)
    | Apply_expr.Result_continuation.Return continuation =>
      (* 1480-1488: the arguments are in the order of the interface. *)
      let* '(dacc, use_id) :=
        let! tmp1 := Apply.return_arity apply in
        let! tmp2 := DE.machine_width denv in
        let! tmp3 := Apply.return_mode apply in
        let! tmp4 := Alloc_mode.For_applications.as_type tmp3 in
        let! tmp5 := T.unknown_types_from_arity (Some tmp4) tmp2 tmp1 in
        DA.record_continuation_use dacc continuation
          (Continuation_use_kind.Non_inlinable true) denv tmp5
      in
      ret (dacc, Some use_id)
    end
  in
  (* 1492-1501: the arguments are in the order of the interface. *)
  let* '(dacc, exn_cont_use_id) :=
    let! tmp1 := Apply.exn_continuation apply in
    let! tmp2 := Exn_continuation.arity tmp1 in
    let! tmp3 := DA.denv dacc in
    let! tmp4 := DE.machine_width tmp3 in
    let! tmp5 := T.unknown_types_from_arity None tmp4 tmp2 in
    let! tmp6 := DA.denv dacc in
    let! tmp7 := Apply.exn_continuation apply in
    let! tmp8 := Exn_continuation.exn_handler tmp7 in
    DA.record_continuation_use dacc tmp8
      (Continuation_use_kind.Non_inlinable true) tmp6 tmp5
  in
  let* dacc :=
    record_free_names_of_apply_as_used dacc use_id exn_cont_use_id apply
  in
  let! tmp1 := SE.simplified_apply None apply use_id exn_cont_use_id false in
  down_to_up dacc tmp1.

(* 1508-1539. In the compiler: [~simplify_expr ~rebuild_expr dacc apply
   ~down_to_up]. *)
Definition simplify_apply
    (simplify_expr : Simplify_common.expr_simplifier Expr.t)
    (rebuild_expr : Simplify_common.rebuild SE.t) (dacc : DA.t)
    (apply : Apply.t) (down_to_up : Simplify_common.down_to_up SE.t)
    : M (SE.t * DA.t) :=
  let! tmp1 := simplify_apply_shared dacc apply in
  match tmp1 with
  | Invalid args_arity =>
    replace_apply_by_invalid dacc down_to_up
      (Flambda.Invalid.Application_argument_kind_mismatch args_arity apply)
  | Ok (T5 dacc callee_ty apply arg_types inlined_forwarded_from) =>
    let! tmp1 := Apply.call_kind apply in
    match tmp1 with
    | Call_kind.Function function_call =>
      simplify_function_call simplify_expr rebuild_expr dacc apply callee_ty
        function_call down_to_up inlined_forwarded_from
    | Call_kind.Method kind obj =>
      let* callee_ty :=
        match callee_ty with
        | Some callee_ty => ret callee_ty
        | None =>
          fatal_errorf2 "No callee provided for method call:@ %a" Apply.print
            apply
        end
      in
      simplify_method_call dacc apply callee_ty kind obj down_to_up
    | Call_kind.C_call _ _ _ _ =>
      let* callee_ty :=
        match callee_ty with
        | Some callee_ty => ret callee_ty
        | None =>
          fatal_errorf2 "No callee provided for C call:@ %a" Apply.print apply
        end
      in
      simplify_c_call simplify_expr dacc apply callee_ty arg_types down_to_up
    | Call_kind.Effect op => simplify_effect_op dacc apply op down_to_up
    end
  end.
