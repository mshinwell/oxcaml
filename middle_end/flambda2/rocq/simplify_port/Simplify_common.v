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

(* This file follows middle_end/flambda2/simplify/simplify_common.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Apply_cont_rewrite_id Apply_expr
  Bound_parameter Bound_parameters Bound_pattern Bound_var Call_kind Code_id
  Code_metadata Continuation Continuation_use_kind Debuginfo Exn_continuation
  Expr_builder Flambda_arity Flambda_debug_uid Flambda_features Lambda List
  Loopify_state Misc Mutability Name Name_mode Option Or_bottom Or_unknown
  Simple Simplify_primitive_result Stdlib_ Symbol_projection Tag
  Target_ocaml_int Target_system Trap_action Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open Simplify_import
OCAML*)

(* 19-54: the six types are abbreviations of function types. In Rocq each
   is what decl/ has for it; its realisation is the compiler's own
   definition, which Rocq prints after [type NAME =], at its place. *)

(* PORT-GAP(type): 19-20, an abbreviation of a function type. *)
Definition after_rebuild : Type :=
  Rebuilt_expr.t -> Upwards_acc.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Constant after_rebuild => "Rebuilt_expr.t -> Upwards_acc.t -> Rebuilt_expr.t * Upwards_acc.t".

(* PORT-GAP(type): 22-26, an abbreviation of a function type with a label. *)
Definition rebuild (A : Type) : Type :=
  A -> Upwards_acc.t -> after_rebuild -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Constant rebuild "'a" => "'a -> Upwards_acc.t -> after_rebuild:after_rebuild -> Rebuilt_expr.t * Upwards_acc.t".

(* PORT-GAP(type): 28-29, an abbreviation of a function type. *)
Definition down_to_up (A : Type) : Type :=
  Downwards_acc.t -> A -> M (Simplified_expr.t * Downwards_acc.t).
Extract Constant down_to_up "'a" => "Downwards_acc.t -> 'a -> Simplified_expr.t * Downwards_acc.t".

(* PORT-GAP(type): 31-35, an abbreviation of a function type with a label. *)
Definition expr_simplifier (A : Type) : Type :=
  Downwards_acc.t -> A -> down_to_up Simplified_expr.t ->
  M (Simplified_expr.t * Downwards_acc.t).
Extract Constant expr_simplifier "'a" => "Downwards_acc.t -> 'a -> down_to_up:Simplified_expr.t down_to_up -> Simplified_expr.t * Downwards_acc.t".

(* PORT-GAP(type): 37-43, an abbreviation of a function type with labels
   and a polymorphic variant. *)
Definition simplify_toplevel : Type :=
  Downwards_acc.t -> Expr.t -> Continuation.t -> Flambda_arity.t_Complex ->
  Continuation.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Constant simplify_toplevel => "Downwards_acc.t -> Expr.t -> return_continuation:Continuation.t -> return_arity:[ `Complex ] Flambda_arity.t -> exn_continuation:Continuation.t -> Rebuilt_expr.t * Upwards_acc.t".

(* PORT-GAP(type): 45-54, an abbreviation of a function type with labels
   and a polymorphic variant. *)
Definition simplify_function_body : Type :=
  Downwards_acc.t -> Expr.t -> Continuation.t -> Flambda_arity.t_Complex ->
  Continuation.t -> Loopify_state.t -> Bound_parameters.t ->
  Bound_parameters.t -> M (Rebuilt_expr.t * Upwards_acc.t).
Extract Constant simplify_function_body => "Downwards_acc.t -> Expr.t -> return_continuation:Continuation.t -> return_arity:[ `Complex ] Flambda_arity.t -> exn_continuation:Continuation.t -> loopify_state:Loopify_state.t -> params:Bound_parameters.t -> implicit_params:Bound_parameters.t -> Rebuilt_expr.t * Upwards_acc.t".

(* 56-72. In the compiler: [dacc ~original_term ~deconstructing ~shape
   ~result_var ~result_kind]. *)
Definition simplify_projection (dacc : DA.t) (original_term : Named.t)
    (deconstructing : T.t) (shape : T.t) (result_var : Bound_var.t)
    (result_kind : K.t) : M Simplify_primitive_result.t :=
  let* denv := DA.denv dacc in
  let* denv := DE.define_variable denv result_var result_kind in
  let* env := DE.typing_env denv in
  let! tmp1 := T.meet_shape env deconstructing shape in
  match tmp1 with
  | Or_bottom.Bottom =>
    let* denv :=
      let! tmp1 := T.bottom result_kind in
      let! tmp2 := Bound_var.var result_var in
      DE.add_equation_on_variable denv tmp2 tmp1
    in
    let* dacc := DA.with_denv dacc denv in
    Simplify_primitive_result.create_invalid dacc
  | Or_bottom.Ok env =>
    let* denv := DE.with_typing_env denv env in
    let* dacc := DA.with_denv dacc denv in
    Simplify_primitive_result.create original_term true dacc
  end.

(* 74-84. In the compiler: [uacc ~exn_cont_use_id apply]. *)
Definition update_exn_continuation_extra_args (uacc : UA.t)
    (exn_cont_use_id : Apply_cont_rewrite_id.t) (apply : Apply.t)
    : M Apply.t :=
  let* exn_cont_rewrite :=
    let! tmp1 := Apply.exn_continuation apply in
    let! tmp2 := Exn_continuation.exn_handler tmp1 in
    let! tmp3 := UA.uenv uacc in
    UE.find_apply_cont_rewrite tmp3 tmp2
  in
  match exn_cont_rewrite with
  | None => ret apply
  | Some rewrite =>
    let! tmp1 := Apply.exn_continuation apply in
    let! tmp2 :=
      Expr_builder.rewrite_exn_continuation rewrite exn_cont_use_id tmp1
    in
    Apply.with_exn_continuation apply tmp2
  end.

(* generate the projection of the i-th field of a n-tuple *)
(* 87-101. In the compiler: [~machine_width ~dbg ~size ~field tuple]. *)
(* PORT-GAP(loose): 88, [let module BAK = P.Block_access_kind in] is not
   kept: [BAK.t] is [P.Block_access_kind.t]. *)
Definition project_tuple (machine_width : Target_system.Machine_width.t)
    (dbg : Debuginfo.t) (size : int) (field : int) (tuple : Simple.t)
    : M Named.t :=
  (* 89-95: the fields of the record of [Values] by place, in the order of
     the type: [tag], [size], [field_kind]. *)
  let* bak :=
    let! tmp1 := Target_ocaml_int.of_int machine_width size in
    ret
      (P.Block_access_kind.Values (Or_unknown.Known Tag.Scannable.zero)
         (Or_unknown.Known tmp1) P.Block_access_field_kind.Any_value)
  in
  let& mutability := Mutability.Immutable in
  let* field := Target_ocaml_int.of_int machine_width field in
  let& prim := P.Unary (P.Block_load bak mutability field) tuple in
  Named.create_prim prim dbg.

(* 103-340. In the compiler: [apply ~callee's_code_id
   ~callee's_code_metadata]. *)
Definition split_direct_over_application (apply : Apply.t)
    (callee's_code_id : Code_id.t) (callee's_code_metadata : Code_metadata.t)
    : M Expr.t :=
  let* apply_alloc_mode := Apply.return_mode apply in
  let* callee's_params_arity :=
    Code_metadata.params_arity callee's_code_metadata
  in
  let* num_non_unarized_params :=
    Flambda_arity.num_params callee's_params_arity
  in
  let* args_arity := Apply.args_arity apply in
  let* num_non_unarized_args := Flambda_arity.num_params args_arity in
  assert_ (num_non_unarized_params <? num_non_unarized_args) ;;
  let* args := Apply.args apply in
  let* '(first_args, remaining_args) :=
    let! tmp1 := Flambda_arity.cardinal_unarized callee's_params_arity in
    Misc.Stdlib.List.split_at tmp1 args
  in
  let* remaining_arity :=
    Flambda_arity.partially_apply args_arity num_non_unarized_params
  in
  (* 125-128 *)
  (let! tmp1 := Flambda_arity.cardinal_unarized remaining_arity in
   let! tmp2 := List.compare_length_with remaining_args tmp1 in
   assert_ (tmp2 =? 0)) ;;
  let* func_var := Variable_.create None "full_apply" K.value in
  let& func_var_duid := Flambda_debug_uid.none in
  let* result_mode := Code_metadata.result_mode callee's_code_metadata in
  let& outer_apply_alloc_mode := apply_alloc_mode in
  (* 133-160 *)
  let* '(needs_region, inner_apply_alloc_mode) :=
    (* If the function being called might do a local allocation that escapes,
       then we need a region for such function's return value, unless the
       allocation mode of the [Apply] is already [Local]. Note that we must not
       add an extra region if the allocation mode of the [Apply] is [Local],
       otherwise the allocation stack pointer might be reset (by the
       [End_region] primitive corresponding to such region) whilst the return
       value is still live (and with the caller expecting such value to have
       been allocated in their region). *)
    match result_mode with
    | Lambda.Not_alloc_stack =>
      let! tmp1 :=
        Alloc_mode.For_applications.not_alloc_stack
          match apply_alloc_mode with
          | Alloc_mode.For_applications.Not_alloc_stack alloc_region
          | Alloc_mode.For_applications.Maybe_alloc_stack alloc_region _ _ =>
            alloc_region
          end
      in
      ret (None, tmp1)
    | Lambda.Maybe_alloc_stack =>
      match apply_alloc_mode with
      | Alloc_mode.For_applications.Not_alloc_stack alloc_region =>
        let* region := Variable_.create None "over_app_region" K.region in
        let* ghost_region :=
          Variable_.create None "over_app_ghost_region" K.region
        in
        let! tmp1 :=
          Alloc_mode.For_applications.maybe_alloc_stack alloc_region region
            ghost_region
        in
        let! tmp2 := Continuation.create None None tt in
        ret (Some (T3 region ghost_region tmp2), tmp1)
      | Alloc_mode.For_applications.Maybe_alloc_stack _ _ _ =>
        ret (None, apply_alloc_mode)
      end
    end
  in
  (* 161-184 *)
  let* perform_over_application :=
    let* continuation :=
      (* If there is no need for a new region, then the second (over)
         application jumps directly to the return continuation of the original
         [Apply]. Otherwise it will need to go through [cont], which we define
         below, so that the [End_region] marker for the new region can be
         inserted. *)
      match needs_region with
      | None => Apply.continuation apply
      | Some (T3 _ _ cont) => ret (Apply_expr.Result_continuation.Return cont)
      end
    in
    (* 172-183: the arguments are in the order of the interface. *)
    let! tmp1 := Apply.relative_history apply in
    let! tmp2 := Apply.position apply in
    let! tmp3 := Apply.probe apply in
    let! tmp4 := Apply.inlining_state apply in
    let! tmp5 := Apply.inlined apply in
    let! tmp6 := Apply.dbg apply in
    let! tmp7 := Apply.return_arity apply in
    let! tmp8 := Apply.exn_continuation apply in
    let! tmp9 := Simple.var func_var in
    Apply.create (Some tmp9) continuation tmp8 remaining_args remaining_arity
      tmp7 Call_kind.indirect_function_call_unknown_arity
      outer_apply_alloc_mode tmp6 tmp5 tmp4 tmp3 tmp2 tmp1
  in
  let* perform_over_application_free_names :=
    Apply.free_names perform_over_application
  in
  (* 188-264 *)
  let* perform_over_application :=
    match needs_region with
    | None => Expr.create_apply perform_over_application
    | Some (T3 region ghost_region after_over_application) =>
      (* This wraps both applications (the full application and the second
         application) with [Begin_region] ... [End_region] for both the normal
         and ghost regions. The applications might raise an exception, but that
         doesn't need any special handling, since we're not actually introducing
         any more local allocations here. (Missing the [End_region]s on the
         exceptional return path is fine, c.f. the usual compilation of [try ...
         with] -- see [Closure_conversion].) *)
      let* over_application_results :=
        let! tmp1 := Apply.return_arity apply in
        let! tmp2 := Flambda_arity.unarize tmp1 in
        List.mapi
          (fun (i : int) kind =>
            let* result_var :=
              let! tmp3 := KS.kind kind in
              let! tmp4 := Stdlib_.string_of_int i in
              Variable_.create None (String.append "result" tmp4) tmp3
            in
            let& result_var_duid := Flambda_debug_uid.none in
            BP.create result_var kind result_var_duid)
          tmp2
      in
      (* 209-222 *)
      let* '(call_return_continuation, call_return_continuation_free_names) :=
        let! tmp1 := Apply.continuation apply in
        match tmp1 with
        | Apply_expr.Result_continuation.Return return_cont =>
          let* apply_cont :=
            let! tmp1 := Apply.dbg apply in
            let! tmp2 := List.map BP.simple over_application_results in
            Apply_cont.create None return_cont tmp2 tmp1
          in
          let! tmp1 := Apply_cont.free_names apply_cont in
          let! tmp2 := Expr.create_apply_cont apply_cont in
          ret (tmp2, tmp1)
        | Apply_expr.Result_continuation.Never_returns =>
          (* The whole overapplication never returns, so this point is
             unreachable. *)
          let! tmp1 :=
            Expr.create_invalid
              (Flambda.Invalid.Over_application_never_returns apply)
          in
          ret (tmp1, NO.empty)
        end
      in
      (* 223-249: [a |> f] is [f a]; the arguments of each call from the last
         to the first. *)
      let* handler_expr :=
        let! tmp1 :=
          NO.remove_var call_return_continuation_free_names ghost_region
        in
        let! tmp2 := Apply.dbg apply in
        let! tmp3 := Simple.var ghost_region in
        let! tmp4 := Named.create_prim (P.Unary (P.End_region true) tmp3) tmp2 in
        let! tmp5 := Variable_.create None "unit" K.value in
        let! tmp6 :=
          Bound_var.create tmp5 Flambda_debug_uid.none Name_mode.normal
        in
        let! tmp7 := Bound_pattern.singleton tmp6 in
        let! tmp8 :=
          Let.create tmp7 tmp4 call_return_continuation
            (Or_unknown.Known call_return_continuation_free_names)
        in
        let! tmp9 := Expr.create_let tmp8 in
        let! tmp10 := Apply.dbg apply in
        let! tmp11 := Simple.var region in
        let! tmp12 :=
          Named.create_prim (P.Unary (P.End_region false) tmp11) tmp10
        in
        let! tmp13 := Variable_.create None "unit" K.value in
        let! tmp14 :=
          Bound_var.create tmp13 Flambda_debug_uid.none Name_mode.normal
        in
        let! tmp15 := Bound_pattern.singleton tmp14 in
        let! tmp16 := Let.create tmp15 tmp12 tmp9 (Or_unknown.Known tmp1) in
        Expr.create_let tmp16
      in
      let* handler_expr_free_names :=
        NO.add_variable call_return_continuation_free_names region
          Name_mode.normal
      in
      let* handler :=
        let! tmp1 := Bound_parameters.create over_application_results in
        Continuation_handler.create tmp1 handler_expr
          (Or_unknown.Known handler_expr_free_names) false false
      in
      let! tmp1 := Expr.create_apply perform_over_application in
      Let_cont.create_non_liftable after_over_application handler tmp1
        (Or_unknown.Known perform_over_application_free_names)
    end
  in
  let* after_full_application := Continuation.create None None tt in
  let* full_apply_result_arity :=
    Code_metadata.result_arity callee's_code_metadata
  in
  (* 269-294 *)
  let* after_full_application_handler :=
    let! tmp1 :=
      Flambda_arity.is_one_param_of_kind_value full_apply_result_arity
    in
    if negb tmp1
    then
      let* params :=
        let! tmp1 := Flambda_arity.unarize full_apply_result_arity in
        let! tmp2 :=
          List.map
            (fun kind =>
              let! tmp3 := KS.kind kind in
              let! tmp4 := Variable_.create None "over_app_result" tmp3 in
              Bound_parameter.create tmp4 kind Flambda_debug_uid.none)
            tmp1
        in
        Bound_parameters.create tmp2
      in
      let! tmp1 :=
        Expr.create_invalid
          (Flambda.Invalid.Over_application_never_returns apply)
      in
      Continuation_handler.create params tmp1
        (Or_unknown.Known Name_occurrences.empty) false true
    else
      let* func_param :=
        BP.create func_var K.With_subkind.any_value func_var_duid
      in
      let! tmp1 := Bound_parameters.create [func_param] in
      Continuation_handler.create tmp1 perform_over_application
        (Or_unknown.Known perform_over_application_free_names) false false
  in
  (* 295-307: the arguments are in the order of the interface. *)
  let* full_apply :=
    let! tmp1 := Apply.relative_history apply in
    let! tmp2 := Apply.position apply in
    let! tmp3 := Apply.probe apply in
    let! tmp4 := Apply.inlining_state apply in
    let! tmp5 := Apply.inlined apply in
    let! tmp6 := Apply.dbg apply in
    let! tmp7 := Call_kind.direct_function_call callee's_code_id in
    let! tmp8 := Code_metadata.result_arity callee's_code_metadata in
    let! tmp9 := Apply.exn_continuation apply in
    let! tmp10 := Apply.callee apply in
    Apply.create tmp10
      (Apply_expr.Result_continuation.Return after_full_application) tmp9
      first_args callee's_params_arity tmp8 tmp7 inner_apply_alloc_mode tmp6
      tmp5 tmp4 tmp3 tmp2 tmp1
  in
  let* both_applications :=
    let! tmp1 := Apply.free_names full_apply in
    let! tmp2 := Expr.create_apply full_apply in
    Let_cont.create_non_liftable after_full_application
      after_full_application_handler tmp2 (Or_unknown.Known tmp1)
  in
  match needs_region with
  | None => ret both_applications
  | Some (T3 region ghost_region _) =>
    let* free_names_of_body :=
      let! tmp1 := Apply.free_names full_apply in
      NO.union tmp1 perform_over_application_free_names
    in
    let& region_duid := Flambda_debug_uid.none in
    let& ghost_region_duid := Flambda_debug_uid.none in
    (* 322-340: [a |> f] is [f a]; the arguments of each call from the last
       to the first. *)
    let! tmp1 := NO.remove_var free_names_of_body ghost_region in
    let! tmp2 := Apply.dbg apply in
    let! tmp3 :=
      Named.create_prim (P.Variadic (P.Begin_region false) []) tmp2
    in
    let! tmp4 :=
      Bound_var.create ghost_region ghost_region_duid Name_mode.normal
    in
    let! tmp5 := Bound_pattern.singleton tmp4 in
    let! tmp6 :=
      Let.create tmp5 tmp3 both_applications
        (Or_unknown.Known free_names_of_body)
    in
    let! tmp7 := Expr.create_let tmp6 in
    let! tmp8 := Apply.dbg apply in
    let! tmp9 :=
      Named.create_prim (P.Variadic (P.Begin_region false) []) tmp8
    in
    let! tmp10 := Bound_var.create region region_duid Name_mode.normal in
    let! tmp11 := Bound_pattern.singleton tmp10 in
    let! tmp12 := Let.create tmp11 tmp9 tmp7 (Or_unknown.Known tmp1) in
    Expr.create_let tmp12
  end.

(* 342-344 *)
Inductive apply_cont_context : Type :=
| Apply_cont_expr
| Switch_branch.

(* 346-374. In the compiler: [~context apply_cont]. *)
Definition apply_cont_use_kind (context : apply_cont_context)
    (apply_cont : Apply_cont.t) : M Continuation_use_kind.t :=
  let* default :=
    match context with
    | Apply_cont_expr => ret Continuation_use_kind.Inlinable
    | Switch_branch => ret (Continuation_use_kind.Non_inlinable false)
    end
  in
  let! tmp1 := AC.continuation apply_cont in
  let! tmp2 := Continuation.sort tmp1 in
  match tmp2 with
  | Continuation.Sort.Normal_or_exn =>
    let! tmp1 := Apply_cont.trap_action apply_cont in
    match tmp1 with
    | None => ret default
    | Some (Trap_action.Push _) =>
      ret (Continuation_use_kind.Non_inlinable false)
    | Some (Trap_action.Pop _ raise_kind) =>
      match raise_kind with
      | None | Some Trap_action.Raise_kind.Regular
      | Some Trap_action.Raise_kind.Reraise =>
        (* Until such time as we can manually add to the backtrace buffer, we
           only convert "raise_notrace" into jumps, except if debugging
           information generation is disabled. (This matches the handling at Cmm
           level; see [Cmm_helpers.raise_prim].)

           We set [escaping = true] for the cases we do not want to convert into
           jumps. *)
        let! tmp1 := Flambda_features.debug tt in
        if tmp1
        then ret (Continuation_use_kind.Non_inlinable true)
        else ret (Continuation_use_kind.Non_inlinable false)
      | Some Trap_action.Raise_kind.No_trace =>
        ret (Continuation_use_kind.Non_inlinable false)
      end
    end
  | Continuation.Sort.Return | Continuation.Sort.Toplevel_return =>
    ret (Continuation_use_kind.Non_inlinable false)
  | Continuation.Sort.Define_root_symbol =>
    (let! tmp1 := Apply_cont.trap_action apply_cont in
     let! tmp2 := Option.is_none tmp1 in
     assert_ tmp2) ;;
    ret default
  end.

(* 376-384 *)
Definition clear_demoted_trap_action (uacc : UA.t) (apply_cont : AC.t)
    : M AC.t :=
  let! tmp1 := AC.trap_action apply_cont in
  match tmp1 with
  | None => ret apply_cont
  | Some (Trap_action.Push exn_handler | Trap_action.Pop exn_handler _) =>
    let! tmp1 := UA.uenv uacc in
    let! tmp2 := UE.mem_continuation tmp1 exn_handler in
    let! tmp3 :=
      and_then tmp2
        (let! tmp4 := UA.is_demoted_exn_handler uacc exn_handler in
         ret (negb tmp4))
    in
    if tmp3 then ret apply_cont else AC.clear_trap_action apply_cont
  end.

(* 386-413 *)
Definition patch_unused_exn_bucket (uacc : UA.t) (apply_cont : AC.t)
    : M AC.t :=
  let! tmp1 := AC.is_raise apply_cont in
  if tmp1
  then
    let! tmp2 := AC.args apply_cont in
    match tmp2 with
    | [] => assert_false
    | exn_value :: other_args =>
      (* Note: [exn_value_is_used] is a global property, not one local to the
         continuation specified by [apply_cont]. In the event of one exception
         value propagating to (say) two different exception continuations, where
         only one of them uses the value, it will still be passed to both
         continuations. However this should be fine as the value still needed to
         be allocated anyway and some value still has to be passed (because of
         the calling convention of exception continuations). 399-405: the
         arguments are in the order of the interface. *)
      let* exn_value_is_used :=
        Simple.pattern_match exn_value
          (fun name _ =>
            let! tmp1 := UA.required_names uacc in
            Name.Set_.mem name tmp1)
          (fun _ => ret true)
      in
      if exn_value_is_used
      then ret apply_cont
      else
        (* The raise argument must be present, if it is unused, we replace it by
           a dummy value to avoid keeping a useless value alive *)
        let* dummy_value :=
          let! tmp1 := UA.uenv uacc in
          let! tmp2 := UE.machine_width tmp1 in
          Simple.const_zero tmp2
        in
        AC.update_args apply_cont (dummy_value :: other_args)
    end
  else ret apply_cont.

(* 415-417 *)
Definition clear_demoted_trap_action_and_patch_unused_exn_bucket (uacc : UA.t)
    (apply_cont : AC.t) : M AC.t :=
  let* apply_cont := clear_demoted_trap_action uacc apply_cont in
  patch_unused_exn_bucket uacc apply_cont.

(* Warning: This function relies on [T.meet_is_flat_float_array], which could
   return any kind for empty arrays. So this function is only safe for
   operations that are invalid on empty arrays.
   [T.meet_is_non_empty_naked_number_array] also has the same restriction. *)
(* 423-465. In the compiler: [dacc array_kind ~array_ty]. *)
Definition specialise_array_kind (dacc : DA.t) (array_kind : P.Array_kind.t)
    (array_ty : T.t) : M (Or_bottom.t P.Array_kind.t) :=
  let* typing_env := DA.typing_env dacc in
  let& for_naked_number :=
    fun (kind : K.Naked_number_kind.t) =>
    let! tmp1 :=
      T.meet_is_non_empty_naked_number_array kind typing_env array_ty
    in
    match tmp1 with
    | T.Known_result tt => ret (Or_bottom.Ok array_kind)
    | T.Need_meet => ret (Or_bottom.Ok array_kind)
    | T.Invalid => ret Or_bottom.Bottom
    end
  in
  match array_kind with
  | P.Array_kind.Naked_floats =>
    for_naked_number K.Naked_number_kind.Naked_float
  | P.Array_kind.Naked_float32s =>
    for_naked_number K.Naked_number_kind.Naked_float32
  | P.Array_kind.Naked_ints =>
    for_naked_number K.Naked_number_kind.Naked_immediate
  | P.Array_kind.Naked_int8s =>
    for_naked_number K.Naked_number_kind.Naked_int8
  | P.Array_kind.Naked_int16s =>
    for_naked_number K.Naked_number_kind.Naked_int16
  | P.Array_kind.Naked_int32s =>
    for_naked_number K.Naked_number_kind.Naked_int32
  | P.Array_kind.Naked_int64s =>
    for_naked_number K.Naked_number_kind.Naked_int64
  | P.Array_kind.Naked_nativeints =>
    for_naked_number K.Naked_number_kind.Naked_nativeint
  | P.Array_kind.Naked_vec128s =>
    for_naked_number K.Naked_number_kind.Naked_vec128
  | P.Array_kind.Naked_vec256s =>
    for_naked_number K.Naked_number_kind.Naked_vec256
  | P.Array_kind.Naked_vec512s =>
    for_naked_number K.Naked_number_kind.Naked_vec512
  | P.Array_kind.Naked_masks =>
    for_naked_number K.Naked_number_kind.Naked_mask
  | P.Array_kind.Immediates =>
    (* The only thing worth checking is for float arrays, as that would allow us
       to remove the branch *)
    let! tmp1 := T.meet_is_flat_float_array typing_env array_ty in
    match tmp1 with
    | T.Known_result false | T.Need_meet => ret (Or_bottom.Ok array_kind)
    | T.Known_result true | T.Invalid => ret Or_bottom.Bottom
    end
  | P.Array_kind.Gc_ignorable_values | P.Array_kind.Values =>
    (* Try to specialise to immediates *)
    let! tmp1 := T.prove_is_immediates_array typing_env array_ty in
    match tmp1 with
    | T.Proved tt =>
      (* Specialise the array operation to [Immediates]. *)
      ret (Or_bottom.Ok P.Array_kind.Immediates)
    | T.Unknown =>
      (* Check for float arrays *)
      let! tmp1 := T.meet_is_flat_float_array typing_env array_ty in
      match tmp1 with
      | T.Known_result false | T.Need_meet => ret (Or_bottom.Ok array_kind)
      | T.Known_result true | T.Invalid => ret Or_bottom.Bottom
      end
    end
  | P.Array_kind.Unboxed_product _ =>
    (* No float array optimization here. We could potentially specialize to
       immediates, but not yet. *)
    ret (Or_bottom.Ok array_kind)
  end.

(* 467-479. In the compiler: [dacc ~projected_from projection
   ~projection_bound_to ~kind]. *)
(* PORT-GAP(loose): 472, [let module SP = Symbol_projection in] is not kept:
   [SP.create] is [Symbol_projection.create]. *)
Definition add_symbol_projection (dacc : DA.t) (projected_from : Simple.t)
    (projection : Symbol_projection.Projection.t)
    (projection_bound_to : Bound_var.t) (kind : K.With_subkind.t) : M DA.t :=
  let! tmp1 := DA.denv dacc in
  let! tmp2 := DE.at_unit_toplevel tmp1 in
  if tmp2
  then ret dacc
  else
    (* 473-479: the arguments are in the order of the interface. *)
    Simple.pattern_match' projected_from
      (fun _ _ => ret dacc)
      (fun symbol_projected_from _ =>
        let* proj :=
          Symbol_projection.create symbol_projected_from projection kind
        in
        let* var := Bound_var.var projection_bound_to in
        DA.map_denv dacc (fun denv => DE.add_symbol_projection denv var proj))
      (fun _ => ret dacc).
