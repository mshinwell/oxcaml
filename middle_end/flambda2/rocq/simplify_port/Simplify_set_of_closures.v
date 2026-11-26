(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2022 OCamlPro SAS                                    *)
(*   Copyright 2014--2022 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/simplify_set_of_closures.ml
   (Git blob 80ee04e8e29d0cfc2c8510c47d0cc7526d89a865), function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the fuel of the local recursive
   function [run]) is that of GUIDE.md; the module [List_] stands for the
   module [List] that the compiler's file makes. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Are_rebuilding_terms Bound_name
  Bound_parameters Bound_pattern Bound_static Bound_var Code_id
  Code_metadata Code_or_metadata Coercion Continuation Continuation_uses
  Cost_metrics Current_unit Debuginfo Flambda_arity Flambda_colours
  Flambda_debug_uid Flambda_features Format Function_decl_inlining_decision
  Function_declarations Function_slot Inlining_arguments Inlining_history
  Inlining_report Join_points Lambda List Loopify_attribute Loopify_state
  Name Name_mode Or_null Or_unknown Or_unknown_or_bottom Printexc
  Rec_info_expr Recursive Removed_operations Result_types Scope Simple
  Simplified_named Simplify_common Simplify_named_result
  Simplify_set_of_closures_context Simplify_simple Specialization_cost
  Stdlib_ Symbol Symbol_projection Value_slot Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Code_or_metadata.View.t
   Flambda2_types.proof_of_property Flambda2_types.to_erase
   Inlining_report.Pass.t Lambda.zero_alloc_attribute Or_null.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 17 *)
(*OCAML
open! Simplify_import
OCAML*)

(* 27 *)
From SimplifyPort.abbrev.simplify_set_of_closures Require Import Port_abbreviations.
(*OCAML
module C = Simplify_set_of_closures_context
OCAML*)

(* 29-137. In the compiler: [context ~outer_dacc ~params ~my_closure
   ~my_alloc_mode ~my_depth function_slot_opt
   ~closure_bound_names_inside_function ~inlining_arguments
   ~absolute_history code_id ~return_continuation ~exn_continuation
   ~loopify_state code_metadata]. *)
Definition dacc_inside_function (context : C.t) (outer_dacc : DA.t)
    (params : Bound_parameters.t) (my_closure : Variable_.t)
    (my_alloc_mode : Alloc_mode.For_applications.t) (my_depth : Variable_.t)
    (function_slot_opt : option Function_slot.t)
    (closure_bound_names_inside_function : Function_slot.Map.t Bound_name.t)
    (inlining_arguments : Inlining_arguments.t)
    (absolute_history : Inlining_history.Absolute.t) (code_id : Code_id.t)
    (return_continuation : Continuation.t)
    (exn_continuation : Continuation.t) (loopify_state : Loopify_state.t)
    (code_metadata : Code_metadata.t) : M DA.t :=
  let* dacc := C.dacc_inside_functions context in
  let* alloc_modes := Code_metadata.param_modes code_metadata in
  (* 35-41: [a |> f b] is [f b a]. *)
  let* denv :=
    let! tmp1 := DA.denv dacc in
    let! tmp2 :=
      DE.add_parameters_with_unknown_types false (Some alloc_modes) None tmp1
        params
    in
    let! tmp3 := DE.set_inlining_arguments inlining_arguments tmp2 in
    let! tmp4 := Inlining_history.Tracker.inside_function absolute_history in
    DE.set_inlining_history_tracker tmp4 tmp3
  in
  let* denv :=
    let! tmp1 := Code_metadata.stub code_metadata in
    if tmp1 then DE.enter_stub_function denv else ret denv
  in
  let& my_closure_duid := Flambda_debug_uid.none in
  (* 48-72 *)
  let* denv :=
    match function_slot_opt with
    | None =>
      (* This happens in the stub case, where we are only simplifying code,
         not a set of closures. *)
      let! tmp1 := T.unknown K.value in
      let! tmp2 := Bound_var.create my_closure my_closure_duid NM.normal in
      DE.add_variable denv tmp2 tmp1
    | Some function_slot =>
      match_exn
        (fun _ =>
          Function_slot.Map.find function_slot
            closure_bound_names_inside_function)
        Not_found
        (fun _ =>
          let! tmp1 := papp1 Function_slot.Map.print Bound_name.print in
          fatal_errorf4
            "No closure name for function slot %a.@ closure_bound_names_inside_function = %a."
            Function_slot.print function_slot tmp1
            closure_bound_names_inside_function)
        (fun name =>
          let* name := Bound_name.name name in
          let! tmp1 := Simple.name name in
          let! tmp2 := T.alias_type_of K.value tmp1 in
          let! tmp3 := Bound_var.create my_closure my_closure_duid NM.normal in
          DE.add_variable denv tmp3 tmp2)
    end
  in
  (* 73-101 *)
  let* denv :=
    match my_alloc_mode with
    | Alloc_mode.For_applications.Not_alloc_stack my_alloc_region =>
      let& my_alloc_region_duid := Flambda_debug_uid.none in
      let* my_alloc_region :=
        Bound_var.create my_alloc_region my_alloc_region_duid Name_mode.normal
      in
      let! tmp1 := T.unknown K.region in
      DE.add_variable denv my_alloc_region tmp1
    | Alloc_mode.For_applications.Maybe_alloc_stack my_alloc_region my_region
        my_ghost_region =>
      let& my_alloc_region_duid := Flambda_debug_uid.none in
      let* my_alloc_region :=
        Bound_var.create my_alloc_region my_alloc_region_duid Name_mode.normal
      in
      let* denv :=
        let! tmp1 := T.unknown K.region in
        DE.add_variable denv my_alloc_region tmp1
      in
      let& my_region_duid := Flambda_debug_uid.none in
      let* my_region :=
        Bound_var.create my_region my_region_duid Name_mode.normal
      in
      let* denv :=
        let! tmp1 := T.unknown K.region in
        DE.add_variable denv my_region tmp1
      in
      let& my_ghost_region_duid := Flambda_debug_uid.none in
      let* my_ghost_region :=
        Bound_var.create my_ghost_region my_ghost_region_duid Name_mode.normal
      in
      let! tmp1 := T.unknown K.region in
      DE.add_variable denv my_ghost_region tmp1
    end
  in
  let& my_depth_duid := Flambda_debug_uid.none in
  let* denv :=
    let* my_depth :=
      Bound_var.create my_depth my_depth_duid Name_mode.normal
    in
    let! tmp1 := T.unknown K.rec_info in
    DE.add_variable denv my_depth tmp1
  in
  (* 107-116: [a |> f b] is [f b a]. *)
  let* denv :=
    let! tmp1 := DA.get_lifted_constants outer_dacc in
    let! tmp2 := DE.add_lifted_constant_state (Some tt) denv tmp1 in
    let! tmp3 := Alloc_mode.For_applications.alloc_region my_alloc_mode in
    let! tmp4 :=
      DE.enter_closure code_id return_continuation exn_continuation
        my_closure tmp3 tmp2
    in
    let! tmp5 := DE.set_loopify_state loopify_state tmp4 in
    DE.increment_continuation_scope tmp5
  in
  let* denv :=
    let! tmp1 := Code_metadata.cold code_metadata in
    if tmp1 then DE.mark_as_cold denv else ret denv
  in
  let* dacc := DA.with_denv dacc denv in
  let* code_ids_to_remember := DA.code_ids_to_remember outer_dacc in
  let* code_ids_to_never_delete := DA.code_ids_to_never_delete outer_dacc in
  let* code_ids_never_simplified :=
    DA.code_ids_never_simplified outer_dacc
  in
  let* used_value_slots := DA.used_value_slots outer_dacc in
  let* shareable_constants := DA.shareable_constants outer_dacc in
  let* slot_offsets := DA.slot_offsets outer_dacc in
  (* 130-137: [a |> f b] is [f b a]; the arguments are in the order of the
     interface. *)
  let! tmp1 := DA.with_code_ids_to_remember dacc code_ids_to_remember in
  let! tmp2 := DA.with_code_ids_to_never_delete tmp1 code_ids_to_never_delete in
  let! tmp3 :=
    DA.with_code_ids_never_simplified tmp2 code_ids_never_simplified
  in
  let! tmp4 := DA.with_used_value_slots tmp3 used_value_slots in
  let! tmp5 := DA.with_shareable_constants tmp4 shareable_constants in
  let! tmp6 := DA.with_slot_offsets tmp5 slot_offsets in
  DA.reset_continuation_lifting_budget tmp6.

(* 139-176. In the compiler: [outer_dacc ~dacc_after_body
   ~uacc_after_upwards_traversal]. *)
Definition extract_accumulators_from_function (outer_dacc : DA.t)
    (dacc_after_body : DA.t) (uacc_after_upwards_traversal : UA.t)
    : M (DA.t * LCS.t) :=
  let* lifted_consts_this_function :=
    (* Subtle point: [uacc_after_upwards_traversal] must be used to retrieve
       all of the lifted constants generated during the simplification of
       the function, not [dacc_after_body]. The reason for this is that
       sometimes the constants in [DA] are cleared (but remembered) and
       reinstated afterwards, for example at a [Let_cont]. It follows that
       if the turning point where the downwards traversal turns into an
       upwards traversal is in such a context, not all of the constants may
       currently be present in [DA]. *)
    UA.lifted_constants uacc_after_upwards_traversal
  in
  let* code_ids_to_remember := DA.code_ids_to_remember dacc_after_body in
  let* code_ids_to_never_delete :=
    DA.code_ids_to_never_delete dacc_after_body
  in
  let* code_ids_never_simplified :=
    DA.code_ids_never_simplified dacc_after_body
  in
  let* used_value_slots :=
    UA.used_value_slots uacc_after_upwards_traversal
  in
  let* shareable_constants :=
    UA.shareable_constants uacc_after_upwards_traversal
  in
  let* slot_offsets := DA.slot_offsets dacc_after_body in
  let* code_age_relation :=
    let! tmp1 := DA.typing_env dacc_after_body in
    TE.code_age_relation tmp1
  in
  (* 165-175: [a |> f b] is [f b a]; the arguments are in the order of the
     interface. *)
  let* outer_dacc :=
    let! tmp1 :=
      DA.add_to_lifted_constant_accumulator (Some tt) outer_dacc
        lifted_consts_this_function
    in
    let! tmp2 := DA.with_code_ids_to_remember tmp1 code_ids_to_remember in
    let! tmp3 :=
      DA.with_code_ids_to_never_delete tmp2 code_ids_to_never_delete
    in
    let! tmp4 :=
      DA.with_code_ids_never_simplified tmp3 code_ids_never_simplified
    in
    let! tmp5 := DA.with_used_value_slots tmp4 used_value_slots in
    let! tmp6 := DA.with_shareable_constants tmp5 shareable_constants in
    let! tmp7 := DA.with_slot_offsets tmp6 slot_offsets in
    DA.with_code_age_relation tmp7 code_age_relation
  in
  ret (outer_dacc, lifted_consts_this_function).

(* 178-189 *)
Record simplify_function_body_result : Type := {
  params : Bound_parameters.t;
  params_and_body : Rebuilt_expr.Function_params_and_body.t;
  body_is_cold : bool;
  dacc_at_function_entry : DA.t;
  dacc_after_body : DA.t;
  free_names_of_code : NO.t;
  return_cont_uses : option Continuation_uses.t;
  is_my_closure_used : bool;
  recursive : Recursive.t;
  uacc_after_upwards_traversal : UA.t
}.

(* 191-313. In the compiler: [context ~outer_dacc function_slot_opt
   ~closure_bound_names_inside_function ~inlining_arguments
   ~absolute_history code_id code ~return_continuation ~exn_continuation
   params ~body ~my_closure ~is_my_closure_used:_ ~my_alloc_mode ~my_depth
   ~free_names_of_body:_]. *)
Definition simplify_function_body (context : C.t) (outer_dacc : DA.t)
    (function_slot_opt : option Function_slot.t)
    (closure_bound_names_inside_function : Function_slot.Map.t Bound_name.t)
    (inlining_arguments : Inlining_arguments.t)
    (absolute_history : Inlining_history.Absolute.t) (code_id : Code_id.t)
    (code : Code.t) (return_continuation : Continuation.t)
    (exn_continuation : Continuation.t) (params : Bound_parameters.t)
    (body : Expr.t) (my_closure : Variable_.t) (_ : Or_unknown.t bool)
    (my_alloc_mode : Alloc_mode.For_applications.t) (my_depth : Variable_.t)
    (_ : Or_unknown.t NO.t) : M simplify_function_body_result :=
  let* loopify_state :=
    let! tmp1 := Code.loopify code in
    let! tmp2 := Loopify_attribute.should_loopify tmp1 in
    if tmp2
    then
      let! tmp1 := Continuation.create None (Some "self") tt in
      Loopify_state.loopify tmp1
    else ret Loopify_state.do_not_loopify
  in
  (* 200-205: the arguments are in the order of the definition. *)
  let* dacc_at_function_entry :=
    let! tmp1 := Code.code_metadata code in
    dacc_inside_function context outer_dacc params my_closure my_alloc_mode
      my_depth function_slot_opt closure_bound_names_inside_function
      inlining_arguments absolute_history code_id return_continuation
      exn_continuation loopify_state tmp1
  in
  let& dacc := dacc_at_function_entry in
  (let! tmp1 := DA.no_lifted_constants dacc in
   if negb tmp1
   then
     fatal_errorf2 "Did not expect lifted constants in [dacc]:@ %a" DA.print
       dacc
   else ret tt) ;;
  (let! tmp1 := DA.denv dacc in
   let! tmp2 := DE.at_unit_toplevel tmp1 in
   assert_ (negb tmp2)) ;;
  let& my_alloc_region_duid := Flambda_debug_uid.none in
  let& my_region_duid := Flambda_debug_uid.none in
  let& my_ghost_region_duid := Flambda_debug_uid.none in
  (* 215-227 *)
  let* region_params :=
    match my_alloc_mode with
    | Alloc_mode.For_applications.Not_alloc_stack alloc_region =>
      let! tmp1 :=
        Bound_parameter.create alloc_region Flambda_kind.With_subkind.region
          my_alloc_region_duid
      in
      ret [tmp1]
    | Alloc_mode.For_applications.Maybe_alloc_stack alloc_region region
        ghost_region =>
      let! tmp1 :=
        Bound_parameter.create ghost_region Flambda_kind.With_subkind.region
          my_ghost_region_duid
      in
      let! tmp2 :=
        Bound_parameter.create region Flambda_kind.With_subkind.region
          my_region_duid
      in
      let! tmp3 :=
        Bound_parameter.create alloc_region Flambda_kind.With_subkind.region
          my_alloc_region_duid
      in
      ret [tmp3; tmp2; tmp1]
    end
  in
  let& my_closure_duid := Flambda_debug_uid.none in
  let& my_depth_duid := Flambda_debug_uid.none in
  (* 230-313: [match e with (body, uacc) -> ... | exception Misc.Fatal_error
     -> ...]. The arguments of [C.simplify_function_body] are in the order
     of its type. *)
  match_exn
    (fun _ =>
      let! tmp1 :=
        Bound_parameter.create my_depth Flambda_kind.With_subkind.rec_info
          my_depth_duid
      in
      let! tmp2 :=
        Bound_parameter.create my_closure Flambda_kind.With_subkind.any_value
          my_closure_duid
      in
      let! tmp3 := Bound_parameters.create ([tmp2; tmp1] ++ region_params) in
      let! tmp4 := Code.result_arity code in
      C.simplify_function_body context dacc body return_continuation tmp4
        exn_continuation loopify_state params tmp3)
    Fatal_error
    (fun _ =>
      (* 301-313 *)
      let* bt := Printexc.get_raw_backtrace tt in
      (let! tmp1 := papp2 Format.pp_print_option None Function_slot.print in
       Format.eprintf16
         "
%tContext is:%t simplifying function with function slot %a,@ params %a,@ return continuation %a,@ exn continuation %a,@ my_closure %a,@ body:@ %a@ with downwards accumulator:@ %a
"
         Flambda_colours.error Flambda_colours.pop tmp1 function_slot_opt
         Bound_parameters.print params Continuation.print return_continuation
         Continuation.print exn_continuation Variable_.print my_closure
         Expr.print body DA.print dacc) ;;
      Printexc.raise_with_backtrace (exn_make Fatal_error tt) bt)
    (fun '(body, uacc) =>
      (* 242-300 *)
      let* dacc_after_body := UA.creation_dacc uacc in
      let* return_cont_uses :=
        let! tmp1 := DA.continuation_uses_env dacc_after_body in
        CUE.get_continuation_uses tmp1 return_continuation
      in
      let* free_names_of_body := UA.name_occurrences uacc in
      let* body_is_cold := RE.is_cold body in
      (* 251-255: the arguments are in the order of the interface. *)
      let* params_and_body :=
        RE.Function_params_and_body.create return_continuation
          exn_continuation params body free_names_of_body my_closure
          my_alloc_mode my_depth
      in
      let* is_my_closure_used := NO.mem_var free_names_of_body my_closure in
      let* previously_free_depth_variables :=
        let! tmp1 := C.previously_free_depth_variables context in
        NO.create_variables tmp1 NM.normal
      in
      let* recursive :=
        let! tmp1 := Name_occurrences.mem_var free_names_of_body my_depth in
        if tmp1 then ret Recursive.Recursive else ret Recursive.Non_recursive
      in
      (* 265-274: [a |> f b] is [f a b] here (the piped value is the first
         argument of each function); the two calls that are arguments
         ([Bound_parameters.free_names], then
         [Alloc_mode.For_applications.free_names]) come first, as OCaml
         evaluates them. *)
      let* free_names_of_code :=
        let! tmp1 := Bound_parameters.free_names params in
        let! tmp2 := Alloc_mode.For_applications.free_names my_alloc_mode in
        let! tmp3 :=
          NO.remove_continuation free_names_of_body return_continuation
        in
        let! tmp4 := NO.remove_continuation tmp3 exn_continuation in
        let! tmp5 := NO.remove_var tmp4 my_closure in
        let! tmp6 := NO.diff tmp5 tmp2 in
        let! tmp7 := NO.remove_var tmp6 my_depth in
        let! tmp8 := NO.diff tmp7 tmp1 in
        NO.diff tmp8 previously_free_depth_variables
      in
      (* 275-289 *)
      (let! tmp1 := NO.no_variables free_names_of_code in
       let! tmp2 := and_then tmp1 (NO.no_continuations free_names_of_code) in
       if negb tmp2
       then
         let! tmp3 := UA.are_rebuilding_terms uacc in
         let! tmp4 := papp1 RE.print tmp3 in
         fatal_errorf14
           "Unexpected free name(s):@ %a@ in:@ 
%a@ 
Simplified version:@ fun %a %a %a %a ->@ 
  %a"
           NO.print free_names_of_code Code_id.print code_id
           Bound_parameters.print params Variable_.print my_closure
           Alloc_mode.For_applications.print my_alloc_mode Variable_.print
           my_depth tmp4 body
       else ret tt) ;;
      ret
        {| params := params;
           params_and_body := params_and_body;
           body_is_cold := body_is_cold;
           dacc_at_function_entry := dacc_at_function_entry;
           dacc_after_body := dacc_after_body;
           free_names_of_code := free_names_of_code;
           return_cont_uses := return_cont_uses;
           is_my_closure_used := is_my_closure_used;
           recursive := recursive;
           uacc_after_upwards_traversal := uacc
        |}).

(* 315-367. In the compiler: [~is_a_functor ~is_opaque ~return_cont_uses
   ~dacc_after_body ~dacc_at_function_entry ~return_cont_params
   ~lifted_consts_this_function ~params]. *)
Definition compute_result_types (is_a_functor : bool) (is_opaque : bool)
    (return_cont_uses : option Continuation_uses.t) (dacc_after_body : DA.t)
    (dacc_at_function_entry : DA.t) (return_cont_params : Bound_parameters.t)
    (lifted_consts_this_function : LCS.t) (params : Bound_parameters.t)
    : M (Or_unknown_or_bottom.t Result_types.t) :=
  (* 318-322: the call that is one of the three values of the match is bound
     before it. *)
  let* function_result_types :=
    Flambda_features.function_result_types is_a_functor
  in
  match is_opaque, function_result_types, return_cont_uses with
  | true, _, _ => ret Or_unknown_or_bottom.Unknown
  | false, _, None => ret Or_unknown_or_bottom.Bottom
  | false, false, Some _ => ret Or_unknown_or_bottom.Unknown
  | false, true, Some uses =>
    let* env_at_fork :=
      (* We use [C.dacc_inside_functions] not [C.dacc_prior_to_sets] to
         ensure that the environment contains bindings for any symbols being
         defined by the set of closures. *)
      DA.denv dacc_at_function_entry
    in
    (* 333-340: the arguments are in the order of the interface. *)
    let* join :=
      let! tmp1 := Continuation_uses.get_uses uses in
      let! tmp2 := DE.get_continuation_scope env_at_fork in
      let! tmp3 := Scope.prev tmp2 in
      Join_points.compute_handler_env None (Some tmp3) tmp1 false env_at_fork
        lifted_consts_this_function return_cont_params EPA.empty
    in
    let* bound_params_and_results :=
      Bound_parameters.append params return_cont_params
    in
    let* params_and_results :=
      Bound_parameters.var_set bound_params_and_results
    in
    let* typing_env := DE.typing_env join.(Join_points.handler_env) in
    let* typing_env :=
      let! tmp1 := DA.typing_env dacc_after_body in
      let! tmp2 := TE.code_age_relation tmp1 in
      TE.with_code_age_relation typing_env tmp2
    in
    (* 352-360: [tmp1] is used after the function: the temporary inside the
       function is [tmp2]. *)
    let* results_and_types :=
      let! tmp1 := Bound_parameters.to_list bound_params_and_results in
      List.map
        (fun result_or_param =>
          let* name := BP.name result_or_param in
          let* kind :=
            let! tmp2 := BP.kind result_or_param in
            K.With_subkind.kind tmp2
          in
          let* ty := TE.find typing_env name (Some kind) in
          ret (name, ty))
        tmp1
    in
    let* env_extension :=
      (* This call is important for compilation time performance, to cut
         down the size of the return types. *)
      T.make_suitable_for_environment typing_env
        (T.All_variables_except params_and_results)
        results_and_types
    in
    let! tmp1 := Result_types.create params return_cont_params env_extension in
    ret (Or_unknown_or_bottom.Ok tmp1)
  end.

(* 369-371 *)
Inductive rebuilt_code : Type :=
| Rebuilding : Code.t -> rebuilt_code
| Not_rebuilding : rebuilt_code.

(* 373-378 *)
Record simplify_function_result : Type := {
  code_id : Code_id.t;
  code : option (rebuilt_code * Rebuilt_static_const.t);
  outer_dacc : DA.t;
  should_resimplify : bool
}.

(* 380-570. In the compiler: [context ~outer_dacc function_slot_opt code_id
   code ~closure_bound_names_inside_function]. *)
Definition simplify_function0 (context : C.t) (outer_dacc : DA.t)
    (function_slot_opt : option Function_slot.t) (code_id : Code_id.t)
    (code : Code.t)
    (closure_bound_names_inside_function : Function_slot.Map.t Bound_name.t)
    : M simplify_function_result :=
  let& original_outer_dacc := outer_dacc in
  let* denv_prior_to_sets :=
    let! tmp1 := C.dacc_prior_to_sets context in
    DA.denv tmp1
  in
  let* inlining_arguments_from_denv :=
    DE.inlining_arguments denv_prior_to_sets
  in
  (* 387-395: [a |> f b] is [f b a]. *)
  let* '(absolute_history, relative_history) :=
    let! tmp1 := DE.inlining_history_tracker denv_prior_to_sets in
    let! tmp2 :=
      match function_slot_opt with
      | Some function_slot => Function_slot.name function_slot
      | None => Code_id.name code_id
      end
    in
    let! tmp3 := Code.relative_history code in
    let! tmp4 := Code.dbg code in
    Inlining_history.Tracker.fundecl tmp4 tmp3 tmp2 tmp1
  in
  (* Compute the set of inlining_arguments used to define this function by
     taking the "least powerful" set between the one set in the environment
     and the one used to define the symbol previously. This way, functions
     that were imported from a foreign compilation unit after inlining will
     still be considered with a set of inlining arguments coherent with the
     one used to compile the current file when inlining. *)
  let* inlining_arguments :=
    let! tmp1 := Code.inlining_arguments code in
    Inlining_arguments.combine inlining_arguments_from_denv tmp1
  in
  let* result_arity := Code.result_arity code in
  (* 407-419: [a |> f] is [f a]. [tmp1] is used after the function: the
     temporaries inside the function are [tmp3] and [tmp4]. *)
  let* return_cont_params :=
    let! tmp1 := Flambda_arity.unarize result_arity in
    let! tmp2 :=
      List.mapi
        (fun i kind_with_subkind =>
          let* result_var :=
            let! tmp3 := KS.kind kind_with_subkind in
            let! tmp4 := Stdlib_.string_of_int i in
            Variable_.create None ("result" ++ tmp4) tmp3
          in
          let& result_var_duid := Flambda_debug_uid.none in
          BP.create result_var kind_with_subkind result_var_duid)
        tmp1
    in
    Bound_parameters.create tmp2
  in
  (* 420-437 *)
  let* '{| params := params;
           params_and_body := params_and_body;
           body_is_cold := body_is_cold;
           dacc_at_function_entry := dacc_at_function_entry;
           dacc_after_body := dacc_after_body;
           free_names_of_code := free_names_of_code;
           return_cont_uses := return_cont_uses;
           is_my_closure_used := is_my_closure_used;
           recursive := recursive;
           uacc_after_upwards_traversal := uacc_after_upwards_traversal
        |} :=
    let! tmp1 := Code.params_and_body code in
    Function_params_and_body.pattern_match tmp1
      (simplify_function_body context outer_dacc function_slot_opt
         closure_bound_names_inside_function inlining_arguments
         absolute_history code_id code)
  in
  let* should_resimplify := UA.resimplify uacc_after_upwards_traversal in
  let* '(outer_dacc, lifted_consts_this_function) :=
    extract_accumulators_from_function outer_dacc dacc_after_body
      uacc_after_upwards_traversal
  in
  let* cost_metrics := UA.cost_metrics uacc_after_upwards_traversal in
  let& old_code_id := code_id in
  (* 445-452 *)
  let* '(code_id, newer_version_of) :=
    let! tmp1 := C.old_to_new_code_ids_all_sets context in
    let! tmp2 := Code_id.Map.find_or_null old_code_id tmp1 in
    match tmp2 with
    | Or_null.This new_code_id => ret (new_code_id, Some old_code_id)
    | Or_null.Null => ret (old_code_id, None)
    end
  in
  (* 453-466: the arguments are in the order of the interfaces. *)
  let* inlining_decision :=
    let* decision :=
      let! tmp1 := Code.is_a_functor code in
      let! tmp2 := Code.stub code in
      let! tmp3 := Code.inline code in
      Function_decl_inlining_decision.make_decision inlining_arguments tmp3
        tmp2 cost_metrics tmp1 recursive
    in
    (let! tmp1 := DA.are_rebuilding_terms dacc_after_body in
     let! tmp2 := Code.code_metadata code in
     let! tmp3 := Code_metadata.with_cost_metrics cost_metrics tmp2 in
     Inlining_report.record_decision_at_function_definition absolute_history
       tmp3 Inlining_report.Pass.After_simplify tmp1 decision) ;;
    ret decision
  in
  let* is_a_functor := Code.is_a_functor code in
  let* is_opaque := Code.is_opaque code in
  let* result_types :=
    compute_result_types is_a_functor is_opaque return_cont_uses
      dacc_after_body dacc_at_function_entry return_cont_params
      lifted_consts_this_function params
  in
  (* 474-491 *)
  let* outer_dacc :=
    (* This is the complicated part about slot offsets. We just traversed
       the body of the function and have accumulated constraints (via
       [Expr_builder] when rebuilding expressions involving sets of
       closures). These constraints are only useful if we end up keeping
       the current code binding. The slot offsets are registered in a map
       from code IDs to offsets in [DA]. A global map of slot offsets is
       accumulated in [UA], using the information from [DA], according to
       whether particular code bindings do indeed get kept. This is how we
       avoid traversing the code in the upwards pass to extract offsets. *)
    let! tmp1 := UA.slot_offsets uacc_after_upwards_traversal in
    match tmp1 with
    | Or_unknown.Unknown => ret outer_dacc
    | Or_unknown.Known offsets =>
      let* slot_offsets :=
        let! tmp1 := DA.slot_offsets outer_dacc in
        Code_id.Map.add code_id offsets tmp1
      in
      DA.with_slot_offsets outer_dacc slot_offsets
    end
  in
  (* 492-504 *)
  let* loopify :=
    let! tmp1 := Code.loopify code in
    match tmp1 with
    | Loopify_attribute.Always_loopify =>
      ret Loopify_attribute.Always_loopify
    | Loopify_attribute.Never_loopify => ret Loopify_attribute.Never_loopify
    | Loopify_attribute.Already_loopified =>
      ret Loopify_attribute.Already_loopified
    | Loopify_attribute.Default_loopify_and_tailrec =>
      ret Loopify_attribute.Already_loopified
    | Loopify_attribute.Default_loopify_and_not_tailrec =>
      ret Loopify_attribute.Never_loopify
    end
  in
  (* 505-528: the arguments of [Rebuilt_static_const.create_code] are in the
     order of its interface and of [Code_metadata.create_type]. *)
  let* '(code_const, new_code) :=
    let* dbg :=
      let! tmp1 := Code.dbg code in
      let! tmp2 := DA.denv outer_dacc in
      DE.add_inlined_debuginfo tmp2 tmp1
    in
    let* cold :=
      let! tmp1 := Code.cold code in
      ret (tmp1 || body_is_cold)
    in
    let! tmp1 := Code.is_tupled code in
    let! tmp2 := Code.regalloc_param_attribute code in
    let! tmp3 := Code.regalloc_attribute code in
    let! tmp4 := Code.poll_attribute code in
    let! tmp5 := Code.zero_alloc_attribute code in
    let! tmp6 := Code.inline code in
    let! tmp7 := Code.stub code in
    let! tmp8 := Code.result_mode code in
    let! tmp9 := Code.first_complex_local_param code in
    let! tmp10 := Code.param_modes code in
    let! tmp11 := Code.params_arity code in
    let! tmp12 := DA.are_rebuilding_terms dacc_after_body in
    Rebuilt_static_const.create_code tmp12 params_and_body free_names_of_code
      code_id newer_version_of tmp11 tmp10 tmp9 result_arity result_types
      tmp8 tmp7 tmp6 tmp5 tmp4 tmp3 tmp2 cold is_a_functor is_opaque
      recursive cost_metrics inlining_arguments dbg tmp1 is_my_closure_used
      inlining_decision absolute_history relative_history loopify
  in
  (* 529-538 *)
  let* code :=
    let* are_rebuilding := DA.are_rebuilding_terms dacc_after_body in
    match new_code with
    | None =>
      (let! tmp1 := Are_rebuilding_terms.do_not_rebuild_terms are_rebuilding in
       assert_ tmp1) ;;
      ret Not_rebuilding
    | Some new_code =>
      (let! tmp1 := Are_rebuilding_terms.do_rebuild_terms are_rebuilding in
       assert_ tmp1) ;;
      ret (Rebuilding new_code)
    end
  in
  let* old_code_was_simplified :=
    (* Simplifying records some crucial information so we can't really use
       an unsimplified version *)
    let! tmp1 := DA.code_ids_never_simplified outer_dacc in
    let! tmp2 := Code_id.Set_.mem old_code_id tmp1 in
    ret (negb tmp2)
  in
  let* zero_improvements :=
    let* removed_ops := Cost_metrics.removed cost_metrics in
    Removed_operations.equal Removed_operations.zero removed_ops
  in
  (* 548-570 *)
  let! tmp1 :=
    and_then old_code_was_simplified
      (and_then (negb should_resimplify)
         (let! tmp2 := C.single_set_of_size_one context in
          ret (tmp2 && zero_improvements)))
  in
  if tmp1
  then
    (* If there are no improvements to the specialisation, we keep the old
       version.

       We can't do that if the function was never specialised at least
       once. *)
    (* If there is any potential use of the new code id (here the variable
       [code_id]) it must be defined. Keeping the old version would prevent
       that. Those uses could exist in functions from the same set of
       closures being simplified with the same context. So this is valid
       only whene there are no such functions. *)
    ret
      {| code_id := old_code_id;
         code := None;
         outer_dacc := original_outer_dacc;
         should_resimplify := should_resimplify
      |}
  else
    ret
      {| code_id := code_id;
         code := Some (code, code_const);
         outer_dacc := outer_dacc;
         should_resimplify := should_resimplify
      |}.

(* 572-575 *)
Definition introduce_code (dacc : DA.t) (code_id : Code_id.t)
    (code_const : Rebuilt_static_const.t) : M DA.t :=
  let* code := LC.create_code code_id code_const in
  let! tmp1 := LCS.singleton code in
  DA.add_to_lifted_constant_accumulator (Some tt) dacc tmp1.

(* 577-634. In the compiler: [context ~outer_dacc function_slot code_id
   ~closure_bound_names_inside_function]. *)
Definition simplify_function (context : C.t) (outer_dacc : DA.t)
    (function_slot : Function_slot.t) (code_id : Code_id.t)
    (closure_bound_names_inside_function : Function_slot.Map.t Bound_name.t)
    : M (tuple3 Code_id.t DA.t Code_id.Set_.t) :=
  let* code_or_metadata :=
    try_with
      (fun _ =>
        let! tmp1 := C.dacc_prior_to_sets context in
        let! tmp2 := DA.denv tmp1 in
        DE.find_code_exn tmp2 code_id)
      Not_found
      (fun _ =>
        fatal_errorf2 "Trying to simplify function %a but it has no code"
          Code_id.print code_id)
  in
  (* 586-623 *)
  let* '(code_id, outer_dacc) :=
    let! tmp1 := Code_or_metadata.view code_or_metadata in
    match tmp1 with
    | Code_or_metadata.View.Code_present code =>
      (* 589-590: the guard [when (not (Code.stub code)) ||
         C.stub_can_be_simplified (DA.denv outer_dacc)]. *)
      let! tmp1 := Code.stub code in
      let! tmp2 :=
        or_else (negb tmp1)
          (let! tmp3 := DA.denv outer_dacc in
           C.stub_can_be_simplified tmp3)
      in
      if tmp2
      then
        (* 591-617: a local [let rec]; in the compiler [run ~outer_dacc
           ~code count]. *)
        let run :=
          fix run (fuel : Port_monad.fuel) (outer_dacc : DA.t)
              (code : Code.t) (count : int) {struct fuel}
              : M (Code_id.t * DA.t) :=
            recursive! fuel in
            let* '{| code_id := code_id;
                     code := new_code;
                     outer_dacc := outer_dacc;
                     should_resimplify := should_resimplify
                  |} :=
              simplify_function0 context outer_dacc (Some function_slot)
                code_id code closure_bound_names_inside_function
            in
            match new_code with
            | None => ret (code_id, outer_dacc)
            | Some (Not_rebuilding, new_code_const) =>
              (* Not rebuilding: there is no code to resimplify *)
              let* outer_dacc :=
                introduce_code outer_dacc code_id new_code_const
              in
              ret (code_id, outer_dacc)
            | Some (Rebuilding new_code, new_code_const) =>
              let* max_function_simplify_run :=
                Flambda_features.Expert.max_function_simplify_run tt
              in
              (let! tmp4 :=
                 and_then should_resimplify
                   (let! tmp5 := Flambda_features.dump_flambda tt in
                    and_then tmp5 (debug tt))
               in
               if tmp4
               then
                 Format.eprintf6
                   "@
%tAfter a single simplify_set_of_closures:%t@
%a:@
%a@
@."
                   Flambda_colours.each_file Flambda_colours.pop
                   Code_id.print code_id Code.print new_code
               else ret tt) ;;
              if should_resimplify && (count <? max_function_simplify_run)
              then run fuel outer_dacc new_code (count + 1)
              else
                let* outer_dacc :=
                  introduce_code outer_dacc code_id new_code_const
                in
                ret (code_id, outer_dacc)
            end
        in
        let_fuel! fuel in
        run fuel outer_dacc code 0
      else
        (* No new code ID is created in this case: there is no function body
           to be simplified and all other code metadata will remain the
           same. *)
        ret (code_id, outer_dacc)
    | Code_or_metadata.View.Metadata_only _ => ret (code_id, outer_dacc)
    end
  in
  (* 624-633 *)
  let* code_ids_to_never_delete_this_set :=
    let* code_metadata := Code_or_metadata.code_metadata code_or_metadata in
    let* never_delete :=
      let! tmp1 := Code_metadata.zero_alloc_attribute code_metadata in
      match tmp1 with
      | Lambda.Default_zero_alloc => ret false
      | Lambda.Assume _ _ _ _ => ret false
      | Lambda.Check _ _ _ _ => ret true
      end
    in
    if never_delete
    then Code_id.Set_.singleton code_id
    else ret Code_id.Set_.empty
  in
  ret (T3 code_id outer_dacc code_ids_to_never_delete_this_set).

(* 636-639 *)
Record simplify_set_of_closures0_result : Type := {
  set_of_closures : Flambda.Set_of_closures.t;
  dacc : Downwards_acc.t
}.

(* 641-758. In the compiler: [outer_dacc context set_of_closures alloc_mode
   ~closure_bound_names ~closure_bound_names_inside ~value_slots
   ~value_slot_types]. *)
Definition simplify_set_of_closures0 (outer_dacc : DA.t) (context : C.t)
    (set_of_closures : Set_of_closures.t)
    (alloc_mode : Alloc_mode.For_types.t)
    (closure_bound_names : Function_slot.Map.t Bound_name.t)
    (closure_bound_names_inside : Function_slot.Map.t Bound_name.t)
    (value_slots : Value_slot.Map.t Simple.t)
    (value_slot_types : Value_slot.Map.t T.t)
    : M simplify_set_of_closures0_result :=
  let* dacc := C.dacc_prior_to_sets context in
  let* function_decls := Set_of_closures.function_decls set_of_closures in
  let* dbg :=
    let! tmp1 := Set_of_closures.debuginfo set_of_closures in
    let! tmp2 := DA.denv dacc in
    DE.add_inlined_debuginfo tmp2 tmp1
  in
  let* all_function_decls_in_set :=
    Function_declarations.funs_in_order function_decls
  in
  (let! tmp1 := DA.no_lifted_constants dacc in
   if negb tmp1
   then
     fatal_errorf2 "Did not expect lifted constants in [dacc]:@ %a" DA.print
       dacc
   else ret tt) ;;
  (* 657-695 *)
  let* '(T3 code_ids_to_never_delete_this_set fun_types outer_dacc,
         all_function_decls_in_set) :=
    Function_slot.Lmap.fold_left_map
      (fun '(T3 result_code_ids_to_never_delete_this_set fun_types outer_dacc)
           function_slot
           (old_code_id :
             Function_declarations.code_id_in_function_declaration) =>
        match old_code_id with
        | decl.Function_declarations.Deleted _ _ =>
          let! tmp1 :=
            Function_slot.Map.add function_slot Or_unknown.Unknown fun_types
          in
          ret
            ( T3 result_code_ids_to_never_delete_this_set tmp1 outer_dacc,
              old_code_id )
        | decl.Function_declarations.Code_id old_code_id
            only_full_applications =>
          let* '(T3 code_id outer_dacc code_ids_to_never_delete_this_set) :=
            simplify_function context outer_dacc function_slot old_code_id
              closure_bound_names_inside
          in
          let* function_type :=
            let* rec_info :=
              (* This is the intrinsic type of the function as seen outside
                 its own scope, so its [Rec_info] needs to say its depth is
                 zero *)
              T.this_rec_info Rec_info_expr.initial
            in
            C.function_decl_type None rec_info code_id
          in
          let* fun_types :=
            Function_slot.Map.add function_slot function_type fun_types
          in
          let* code_ids_to_never_delete_this_set :=
            Code_id.Set_.union code_ids_to_never_delete_this_set
              result_code_ids_to_never_delete_this_set
          in
          ret
            ( T3 code_ids_to_never_delete_this_set fun_types outer_dacc,
              decl.Function_declarations.Code_id code_id
                only_full_applications )
        end)
      (T3 Code_id.Set_.empty Function_slot.Map.empty outer_dacc)
      all_function_decls_in_set
  in
  (* 696-705 *)
  let* code_ids_to_remember_this_set :=
    Function_slot.Lmap.fold
      (fun _function_slot
           (code_id : Function_declarations.code_id_in_function_declaration)
           code_ids =>
        match code_id with
        | decl.Function_declarations.Deleted _ _ => ret code_ids
        | decl.Function_declarations.Code_id code_id _ =>
          Code_id.Set_.add code_id code_ids
        end)
      all_function_decls_in_set Code_id.Set_.empty
  in
  let* dacc :=
    DA.add_code_ids_to_remember outer_dacc code_ids_to_remember_this_set
  in
  let* dacc :=
    DA.add_code_ids_to_never_delete dacc code_ids_to_never_delete_this_set
  in
  (* 712-734 *)
  let* closure_types_by_bound_name :=
    let* closure_types_via_aliases :=
      Function_slot.Map.map
        (fun name =>
          let! tmp1 := Bound_name.name name in
          let! tmp2 := Simple.name tmp1 in
          T.alias_type_of K.value tmp2)
        closure_bound_names
    in
    Function_slot.Map.fold
      (fun function_slot _function_decl_type closure_types =>
        match_exn
          (fun _ => Function_slot.Map.find function_slot closure_bound_names)
          Not_found
          (fun _ =>
            fatal_errorf2 "No bound variable for function slot %a"
              Function_slot.print function_slot)
          (fun bound_name =>
            let* closure_type :=
              T.exactly_this_closure function_slot fun_types
                closure_types_via_aliases value_slot_types alloc_mode
            in
            ret ((bound_name, closure_type) :: closure_types)))
      fun_types []
  in
  (* 735-753 *)
  let* dacc :=
    DA.map_denv dacc
      (fun denv =>
        (* The types of each closure can refer to the other closures. The
           typing env expects equations to refer only to names already
           defined, so we first define all names then add all equations. *)
        let* denv_with_defined_symbols :=
          List.fold_left
            (fun denv '(bound_name, _closure_type) =>
              (* In the lifting case the symbols could be defined
                 already. *)
              DE.define_name_if_undefined denv bound_name K.value)
            denv closure_types_by_bound_name
        in
        List.fold_left
          (fun denv '(bound_name, closure_type) =>
            let! tmp1 := Bound_name.name bound_name in
            DE.add_equation_on_name denv tmp1 closure_type)
          denv_with_defined_symbols closure_types_by_bound_name)
  in
  (* 754-757: [a |> f b] is [f b a]. *)
  let* set_of_closures :=
    let! tmp1 := Function_declarations.create all_function_decls_in_set in
    Set_of_closures.create value_slots dbg tmp1
  in
  ret {| set_of_closures := set_of_closures; dacc := dacc |}.

(* 760-876. In the compiler: [dacc ~closure_bound_vars_inverse
   ~closure_bound_vars set_of_closures alloc_mode ~value_slots
   ~symbol_projections ~simplify_function_body]. *)
Definition simplify_and_lift_set_of_closures (dacc : DA.t)
    (closure_bound_vars_inverse : Variable_.Map.t Function_slot.t)
    (closure_bound_vars : Function_slot.Map.t Bound_var.t)
    (set_of_closures : Set_of_closures.t)
    (alloc_mode : Alloc_mode.For_allocations.t)
    (value_slots : Value_slot.Map.t Simple.t)
    (symbol_projections : Variable_.Map.t Symbol_projection.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    : M Simplify_named_result.t :=
  let* function_decls := Set_of_closures.function_decls set_of_closures in
  (* 764-770: [tmp1] is used after the function: the temporary inside the
     function is [tmp2]. *)
  let* closure_symbols :=
    let! tmp1 := Function_declarations.funs_in_order function_decls in
    Function_slot.Lmap.mapi
      (fun function_slot _func_decl =>
        let* name := Function_slot.canonical_name function_slot in
        let! tmp2 := Current_unit.get_cu_exn tt in
        Symbol.manufacture tmp2 name)
      tmp1
  in
  let* closure_symbols_map :=
    let! tmp1 := Function_slot.Lmap.bindings closure_symbols in
    Function_slot.Map.of_list tmp1
  in
  let* closure_bound_names :=
    Function_slot.Map.map Bound_name.create_symbol closure_symbols_map
  in
  (* 777-802: the functions given to [Simple.pattern_match] ([~name], then
     [~const]) and to [Name.pattern_match] ([~var], then [~symbol]) are in
     the order of the interfaces. *)
  let* value_slot_types :=
    Value_slot.Map.mapi
      (fun value_slot in_slot =>
        let* kind := Value_slot.kind value_slot in
        Simple.pattern_match in_slot
          (fun name coercion =>
            Name.pattern_match name
              (fun var =>
                let! tmp1 :=
                  Variable_.Map.find_or_null var closure_bound_vars_inverse
                in
                match tmp1 with
                | Or_null.Null =>
                  (let! tmp1 := DA.denv dacc in
                   let! tmp2 := DE.mem_variable tmp1 var in
                   assert_ tmp2) ;;
                  T.alias_type_of kind in_slot
                | Or_null.This function_slot =>
                  let* closure_symbol :=
                    Function_slot.Map.find function_slot closure_symbols_map
                  in
                  let* simple :=
                    let! tmp1 := Simple.symbol closure_symbol in
                    Simple.with_coercion tmp1 coercion
                  in
                  T.alias_type_of kind simple
                end)
              (fun _sym => T.alias_type_of kind in_slot))
          (fun _ => T.alias_type_of kind in_slot))
      value_slots
  in
  (* 803-809 *)
  let* context :=
    let! tmp1 := Alloc_mode.For_allocations.as_type alloc_mode in
    C.create dacc simplify_function_body
      [(set_of_closures, tmp1)]
      [closure_bound_names] [value_slot_types]
  in
  let* closure_bound_names_inside :=
    C.closure_bound_names_inside_functions_exactly_one_set context
  in
  (* 813-818 *)
  let* '{| set_of_closures := set_of_closures; dacc := dacc |} :=
    let! tmp1 := Alloc_mode.For_allocations.as_type alloc_mode in
    simplify_set_of_closures0 dacc context set_of_closures tmp1
      closure_bound_names closure_bound_names_inside value_slots
      value_slot_types
  in
  let* closure_symbols_set :=
    let! tmp1 := Function_slot.Lmap.data closure_symbols in
    Symbol.Set_.of_list tmp1
  in
  (let! tmp1 := Function_slot.Map.cardinal closure_symbols_map in
   let! tmp2 := Symbol.Set_.cardinal closure_symbols_set in
   assert_ (tmp2 =? tmp1)) ;;
  let* denv := DA.denv dacc in
  let* closure_symbols_with_types :=
    Function_slot.Lmap.map
      (fun symbol =>
        let* typ := DE.find_symbol denv symbol in
        ret (symbol, typ))
      closure_symbols
  in
  (* 833-839: [a |> f] is [f a]. *)
  let& find_code_metadata :=
    fun (code_id : Code_id.t) =>
    let* env := DA.denv dacc in
    let! tmp1 :=
      try_with
        (fun _ => DE.find_code_exn env code_id)
        Not_found
        (fun _ =>
          fatal_errorf2 "Could not find code for %a" Code_id.print code_id)
    in
    Code_or_metadata.code_metadata tmp1
  in
  (* 840-846: the arguments are in the order of the interfaces. *)
  let* set_of_closures_lifted_constant :=
    let! tmp1 := DE.are_rebuilding_terms denv in
    let! tmp2 :=
      Rebuilt_static_const.create_set_of_closures tmp1 find_code_metadata
        set_of_closures
    in
    let! tmp3 := DE.typing_env denv in
    LC.create_set_of_closures tmp3 closure_symbols_with_types
      symbol_projections tmp2
  in
  let* dacc :=
    let! tmp1 := LCS.singleton set_of_closures_lifted_constant in
    DA.add_to_lifted_constant_accumulator (Some tt) dacc tmp1
  in
  (* 851-868 *)
  let* '(denv, bindings) :=
    let! tmp1 := Function_slot.Lmap.bindings closure_symbols in
    let! tmp2 := DA.denv dacc in
    List.fold_left_map
      (fun denv '(function_slot, closure_symbol) =>
        match_exn
          (fun _ => Function_slot.Map.find function_slot closure_bound_vars)
          Not_found
          (fun _ =>
            fatal_errorf2 "No bound variable for function slot %a"
              Function_slot.print function_slot)
          (fun bound_var =>
            let* denv :=
              let* simple := Simple.symbol closure_symbol in
              let* typ := T.alias_type_of K.value simple in
              DE.add_variable denv bound_var typ
            in
            let& binding := (bound_var, closure_symbol) in
            ret (denv, binding)))
      tmp2 tmp1
  in
  (* 869-872: [DE.map_specialization_cost denv ~f], the arguments in the
     order of the interface. *)
  let* denv :=
    let! tmp1 :=
      papp1 Specialization_cost.add_lifted_set_of_closures set_of_closures
    in
    DE.map_specialization_cost tmp1 denv
  in
  let! tmp1 := Named.create_set_of_closures alloc_mode set_of_closures in
  let! tmp2 := DA.with_denv dacc denv in
  Simplify_named_result.create_have_lifted_set_of_closures tmp2 bindings tmp1.

(* 878-984. In the compiler: [dacc bound_vars ~closure_bound_vars
   set_of_closures alloc_mode ~value_slots ~value_slot_types
   ~simplify_function_body]. *)
Definition simplify_non_lifted_set_of_closures0 (dacc : DA.t)
    (bound_vars : Bound_pattern.t)
    (closure_bound_vars : Function_slot.Map.t Bound_var.t)
    (set_of_closures : Set_of_closures.t)
    (alloc_mode : Alloc_mode.For_allocations.t)
    (value_slots : Value_slot.Map.t Simple.t)
    (value_slot_types : Value_slot.Map.t T.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    : M Simplify_named_result.t :=
  let* closure_bound_names :=
    Function_slot.Map.map Bound_name.create_var closure_bound_vars
  in
  let* function_declarations_in_order :=
    let! tmp1 := Set_of_closures.function_decls set_of_closures in
    Function_declarations.funs_in_order tmp1
  in
  (* 888-894 *)
  let* context :=
    let! tmp1 := Alloc_mode.For_allocations.as_type alloc_mode in
    C.create dacc simplify_function_body
      [(set_of_closures, tmp1)]
      [closure_bound_names] [value_slot_types]
  in
  let* closure_bound_names_inside :=
    C.closure_bound_names_inside_functions_exactly_one_set context
  in
  (* 898-950 *)
  let* '{| set_of_closures := set_of_closures; dacc := dacc |} :=
    let! tmp1 := Bound_pattern.name_mode bound_vars in
    let! tmp2 := Name_mode.is_normal tmp1 in
    if tmp2
    then
      let! tmp1 := Alloc_mode.For_allocations.as_type alloc_mode in
      simplify_set_of_closures0 dacc context set_of_closures tmp1
        closure_bound_names closure_bound_names_inside value_slots
        value_slot_types
    else
      (* If the closure is to be phantomized, mark all code as deleted *)
      let* dacc :=
        DA.map_denv dacc
          (fun denv =>
            Bound_pattern.fold_all_bound_vars bound_vars denv
              (fun denv var => DE.define_variable denv var K.value))
      in
      let* set_of_closures :=
        (* 913-920: [tmp1] is used after the function: the temporaries
           inside the function are [tmp2] and [tmp3]. *)
        let* value_slots :=
          let! tmp1 := Set_of_closures.value_slots set_of_closures in
          Value_slot.Map.map
            (fun simple =>
              let! tmp2 := Bound_pattern.name_mode bound_vars in
              let! tmp3 := Simplify_simple.simplify_simple dacc simple tmp2 in
              Stdlib_.snd tmp3)
            tmp1
        in
        (* 921-941 *)
        let* function_decls :=
          Function_slot.Lmap.map
            (fun (func :
                   Function_declarations.code_id_in_function_declaration) =>
              match func with
              | decl.Function_declarations.Deleted _ _ => ret func
              | decl.Function_declarations.Code_id code_id _ =>
                let* code_metadata :=
                  let! tmp1 :=
                    try_with
                      (fun _ =>
                        let! tmp2 := DA.denv dacc in
                        DE.find_code_exn tmp2 code_id)
                      Not_found
                      (fun _ =>
                        fatal_errorf2 "Could not find code for %a"
                          Code_id.print code_id)
                  in
                  Code_or_metadata.code_metadata tmp1
                in
                (* PORT-GAP(record-order): 935-939, the two fields of the
                   inline record are calls: each is bound before the
                   constructor, in the order of the type, the last field
                   first.
                   VERDICT (record_order/README.md, place 20): COMMUTE. Two
                   readings of fields of one immutable record. *)
                let* dbg := Code_metadata.dbg code_metadata in
                let* function_slot_size :=
                  Code_metadata.function_slot_size code_metadata
                in
                ret (decl.Function_declarations.Deleted function_slot_size dbg)
              end)
            function_declarations_in_order
        in
        let* dbg :=
          let! tmp1 := Set_of_closures.debuginfo set_of_closures in
          let! tmp2 := DA.denv dacc in
          DE.add_inlined_debuginfo tmp2 tmp1
        in
        let! tmp1 := Function_declarations.create function_decls in
        Set_of_closures.create value_slots dbg tmp1
      in
      ret {| set_of_closures := set_of_closures; dacc := dacc |}
  in
  (* 951-969 *)
  let* defining_expr :=
    let* named := Named.create_set_of_closures alloc_mode set_of_closures in
    let& find_code_characteristics :=
      fun (code_id : Code_id.t) =>
      let* env := Downwards_acc.denv dacc in
      let* code_metadata :=
        let! tmp1 :=
          try_with
            (fun _ => DE.find_code_exn env code_id)
            Not_found
            (fun _ =>
              fatal_errorf2 "Could not find code for %a" Code_id.print
                code_id)
        in
        Code_or_metadata.code_metadata tmp1
      in
      (* PORT-GAP(record-order): 961-964, the two fields of the record are
         calls: each is bound before the record, in the order of the type,
         the last field first.
         VERDICT (record_order/README.md, place 21): COMMUTE. Two readings of
         fields of one immutable record. *)
      let* function_slot_size :=
        Code_metadata.function_slot_size code_metadata
      in
      let* cost_metrics := Code_metadata.cost_metrics code_metadata in
      ret
        {| Cost_metrics.cost_metrics := cost_metrics;
           Cost_metrics.function_slot_size := function_slot_size
        |}
    in
    let* machine_width :=
      let! tmp1 := DA.denv dacc in
      DE.machine_width tmp1
    in
    let! tmp1 := Named.free_names named in
    Simplified_named.create_with_known_free_names machine_width
      find_code_characteristics named tmp1
  in
  (* 970-975 *)
  let* dacc :=
    let! tmp1 :=
      papp1 Specialization_cost.add_set_of_closures set_of_closures
    in
    let! tmp2 := papp1 DE.map_specialization_cost tmp1 in
    DA.map_denv dacc tmp2
  in
  (* 976-984 *)
  let! tmp1 := Named.create_set_of_closures alloc_mode set_of_closures in
  Simplify_named_result.create dacc
    (Simplified_named.Keep_binding bound_vars defining_expr (Some tmp1)).

(* 986-991 *)
Record lifting_decision_result : Type := {
  can_lift : bool;
  value_slots : Value_slot.Map.t Simple.t;
  value_slot_types : Value_slot.Map.t T.t;
  symbol_projections : Variable_.Map.t Symbol_projection.t
}.

(* 993-1084. In the compiler: [dacc ~name_mode_of_bound_vars set_of_closures
   alloc_mode]. *)
Definition type_value_slots_and_make_lifting_decision_for_one_set
    (dacc : DA.t) (name_mode_of_bound_vars : Name_mode.t)
    (set_of_closures : Set_of_closures.t)
    (alloc_mode : Alloc_mode.For_types.t) : M lifting_decision_result :=
  (* By computing the types of the closure elements, attempt to show that
     the set of closures can be lifted, and hence statically allocated. Note
     that simplifying the bodies of the functions won't change the
     set-of-closures' eligibility for lifting. That this is so follows from
     the fact that closure elements cannot be deleted without an analysis
     across the whole source file, as an inlined function's body may
     reference them out of scope of the closure declaration. (Such deletions
     end up occurring during the upwards traversal and during [To_cmm], by
     which time the necessary information is available.) *)
  (* 1005-1037: the functions given to [Simple.pattern_match'] ([~var],
     [~symbol], [~const]) are in the order of the interface. [tmp1] is used
     after the function: the temporaries inside the function are [tmp2] and
     [tmp3]. *)
  let* '(T3 value_slots value_slot_types symbol_projections) :=
    let! tmp1 := Set_of_closures.value_slots set_of_closures in
    Value_slot.Map.fold
      (fun value_slot env_entry
           '(T3 value_slots value_slot_types symbol_projections) =>
        let* '(T3 env_entry ty symbol_projections) :=
          let* '(ty, simple) :=
            S.simplify_simple dacc env_entry name_mode_of_bound_vars
          in
          (* Note down separately if [simple] remains a variable and is
             known to be equal to a projection from a symbol. *)
          let* symbol_projections :=
            Simple.pattern_match' simple
              (fun var _ =>
                (* [var] will already be canonical, by virtue of the
                   semantics of [S.simplify_simple], as we require for the
                   symbol projections map. *)
                let! tmp2 := DA.denv dacc in
                let! tmp3 := DE.find_symbol_projection tmp2 var in
                match tmp3 with
                | None => ret symbol_projections
                | Some proj => Variable_.Map.add var proj symbol_projections
                end)
              (fun _ _ => ret symbol_projections)
              (fun _ => ret symbol_projections)
          in
          ret (T3 simple ty symbol_projections)
        in
        let* value_slots :=
          Value_slot.Map.add value_slot env_entry value_slots
        in
        let* value_slot_types :=
          Value_slot.Map.add value_slot ty value_slot_types
        in
        ret (T3 value_slots value_slot_types symbol_projections))
      tmp1
      (T3 Value_slot.Map.empty Value_slot.Map.empty Variable_.Map.empty)
  in
  let& can_lift_coercion :=
    fun (coercion : Coercion.t) =>
    let! tmp1 := Coercion.free_names coercion in
    NO.no_variables tmp1
  in
  (* Note that [closure_bound_vars_inverse] doesn't need to include
     variables binding closures in other mutually-recursive sets, since if
     we get here in the case where we are considering lifting a set that has
     not been lifted before, there are never any other mutually-recursive
     sets ([Named.t] does not allow them). *)
  (* PORT-GAP(loose): 1046, the attribute [@inline] is not kept. *)
  let& variable_permits_lifting :=
    fun (var : Variable_.t) =>
    (* Variables (excluding ones bound to symbol projections; see below) in
       the definition of the set of closures will currently prevent lifting
       if the allocation mode is [Local] and we cannot show that such
       variables never hold locally-allocated blocks (pointers to which from
       statically-allocated blocks are forbidden). Also see comment in
       types/reify.ml.

       If [var] is known to be a symbol projection, it doesn't matter if it
       isn't in scope at the place where we will eventually insert the "let
       symbol", as the binding to the projection from the relevant symbol
       can always be rematerialised. Likewise no
       [never_holds_locally_allocated_values] check is needed in the symbol
       projection case, since we are projecting from a value that has
       already been deemed eligible for lifting. *)
    let! tmp1 := Variable_.Map.mem var symbol_projections in
    or_else tmp1
      (let! tmp2 := DA.denv dacc in
       let! tmp3 := DE.is_defined_at_toplevel tmp2 var in
       and_then tmp3
         (match alloc_mode with
          | Alloc_mode.For_types.Local | Alloc_mode.For_types.Heap_or_local =>
            let! tmp4 := DA.typing_env dacc in
            let! tmp5 := T.never_holds_locally_allocated_values tmp4 var in
            match tmp5 with
            | T.Proved tt => ret true
            | T.Unknown => ret false
            end
          | Alloc_mode.For_types.Heap => ret true
          end))
  in
  let& value_slot_permits_lifting :=
    fun (_value_slot : Value_slot.t) (simple : Simple.t) =>
    let! tmp1 := Simple.coercion simple in
    let! tmp2 := can_lift_coercion tmp1 in
    and_then tmp2
      (Simple.pattern_match' simple
         (fun var _ => variable_permits_lifting var)
         (fun _ _ => ret true)
         (fun _ => ret true))
  in
  let* can_lift :=
    let! tmp1 := Name_mode.is_normal name_mode_of_bound_vars in
    and_then tmp1
      (Value_slot.Map.for_all value_slot_permits_lifting value_slots)
  in
  ret
    {| can_lift := can_lift;
       value_slots := value_slots;
       value_slot_types := value_slot_types;
       symbol_projections := symbol_projections
    |}.

(* 1086-1115 *)
(* PORT-GAP(loose): 1086-1087, the compiler's function has four parameters
   and ends with two functions that wait for [~simplify_function_body]
   (lines 1110 and 1114); here that argument is the fifth parameter. *)
Definition simplify_non_lifted_set_of_closures (dacc : DA.t)
    (bound_vars : Bound_pattern.t) (set_of_closures : Set_of_closures.t)
    (alloc_mode : Alloc_mode.For_allocations.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    : M Simplify_named_result.t :=
  let* closure_bound_vars :=
    Bound_pattern.must_be_set_of_closures bound_vars
  in
  let* name_mode_of_bound_vars := Bound_pattern.name_mode bound_vars in
  (* 1092-1102: [a |> f] is [f a]. [tmp3] is used after the function: the
     temporaries inside the function begin at [tmp4]. The two values of the
     pair are calls: the second is made first. *)
  let* '(closure_bound_vars, closure_bound_vars_inverse) :=
    let! tmp1 := Set_of_closures.function_decls set_of_closures in
    let! tmp2 := Function_declarations.funs_in_order tmp1 in
    let! tmp3 := Function_slot.Lmap.keys tmp2 in
    List.fold_left2
      (fun '(closure_bound_vars, closure_bound_vars_inverse) function_slot
           var =>
        let! tmp4 := Bound_var.var var in
        let! tmp5 :=
          Variable_.Map.add tmp4 function_slot closure_bound_vars_inverse
        in
        let! tmp6 :=
          Function_slot.Map.add function_slot var closure_bound_vars
        in
        ret (tmp6, tmp5))
      (Function_slot.Map.empty, Variable_.Map.empty)
      tmp3 closure_bound_vars
  in
  (* 1103-1107 *)
  let* '{| can_lift := can_lift;
           value_slots := value_slots;
           value_slot_types := value_slot_types;
           symbol_projections := symbol_projections
        |} :=
    let! tmp1 := Alloc_mode.For_allocations.as_type alloc_mode in
    type_value_slots_and_make_lifting_decision_for_one_set dacc
      name_mode_of_bound_vars set_of_closures tmp1
  in
  if can_lift
  then
    simplify_and_lift_set_of_closures dacc closure_bound_vars_inverse
      closure_bound_vars set_of_closures alloc_mode value_slots
      symbol_projections simplify_function_body
  else
    simplify_non_lifted_set_of_closures0 dacc bound_vars closure_bound_vars
      set_of_closures alloc_mode value_slots value_slot_types
      simplify_function_body.

(* 1117-1149. In the compiler: [dacc context ~closure_symbols
   ~closure_bound_names_inside ~value_slots ~value_slot_types
   set_of_closures]. *)
Definition simplify_lifted_set_of_closures0 (dacc : DA.t) (context : C.t)
    (closure_symbols : Function_slot.Lmap.t Symbol.t)
    (closure_bound_names_inside : Function_slot.Map.t Bound_name.t)
    (value_slots : Value_slot.Map.t Simple.t)
    (value_slot_types : Value_slot.Map.t T.t)
    (set_of_closures : Set_of_closures.t)
    : M (tuple3 Bound_static.Pattern.t Rebuilt_static_const.t DA.t) :=
  (* 1119-1122: [a |> f] is [f a]. *)
  let* closure_bound_names :=
    let! tmp1 :=
      Function_slot.Lmap.map Bound_name.create_symbol closure_symbols
    in
    let! tmp2 := Function_slot.Lmap.bindings tmp1 in
    Function_slot.Map.of_list tmp2
  in
  let* '{| set_of_closures := set_of_closures; dacc := dacc |} :=
    simplify_set_of_closures0 dacc context set_of_closures
      Alloc_mode.For_types.heap closure_bound_names
      closure_bound_names_inside value_slots value_slot_types
  in
  (* 1128-1134: [a |> f] is [f a]. *)
  let& find_code_metadata :=
    fun (code_id : Code_id.t) =>
    let* env := DA.denv dacc in
    let! tmp1 :=
      try_with
        (fun _ => Downwards_env.find_code_exn env code_id)
        Not_found
        (fun _ =>
          fatal_errorf2 "Could not find code for %a" Code_id.print code_id)
    in
    Code_or_metadata.code_metadata tmp1
  in
  let* set_of_closures_pattern :=
    Bound_static.Pattern.set_of_closures closure_symbols
  in
  let* set_of_closures_static_const :=
    let! tmp1 := DA.are_rebuilding_terms dacc in
    Rebuilt_static_const.create_set_of_closures tmp1 find_code_metadata
      set_of_closures
  in
  (* 1143-1148 *)
  let* dacc :=
    let! tmp1 :=
      papp1 Specialization_cost.add_lifted_set_of_closures set_of_closures
    in
    let! tmp2 := papp1 DE.map_specialization_cost tmp1 in
    DA.map_denv dacc tmp2
  in
  ret (T3 set_of_closures_pattern set_of_closures_static_const dacc).

(* 1151-1159 *)
(* PORT-GAP(loose): the compiler's file makes a module [List] that includes
   OCaml's [List] and adds [fold_left3]; here the module is [List_] and has
   that function only, and the other functions of [List] are OCaml's. *)
Module List_.
  (* 1154-1158. The recursion is on the structure of [l1]. *)
  Fixpoint fold_left3 {Acc A1 A2 A3 : Type}
      (f : Acc -> A1 -> A2 -> A3 -> M Acc) (accu : Acc) (l1 : list A1)
      (l2 : list A2) (l3 : list A3) {struct l1} : M Acc :=
    match l1, l2, l3 with
    | [], [], [] => ret accu
    | a1 :: l1, a2 :: l2, a3 :: l3 =>
      let! tmp1 := f accu a1 a2 a3 in
      fold_left3 f tmp1 l1 l2 l3
    | _, _, _ => Stdlib_.invalid_arg "List.fold_left3"
    end.
End List_.

(* 1161-1211. In the compiler: [dacc ~all_sets_of_closures_and_symbols
   ~closure_bound_names_all_sets ~simplify_function_body]. *)
Definition simplify_lifted_sets_of_closures (dacc : DA.t)
    (all_sets_of_closures_and_symbols :
      list (Function_slot.Lmap.t Symbol.t * Set_of_closures.t))
    (closure_bound_names_all_sets : list (Function_slot.Map.t Bound_name.t))
    (simplify_function_body : Simplify_common.simplify_function_body)
    : M (tuple3 Bound_static.t Rebuilt_static_const.Group.t DA.t) :=
  let* all_sets_of_closures :=
    List.map
      (fun '(_symbols, set_of_closures) =>
        ret (set_of_closures, Alloc_mode.For_types.heap))
      all_sets_of_closures_and_symbols
  in
  (* 1169-1182 *)
  let* value_slots_and_types_all_sets :=
    List.map
      (fun '(set_of_closures, alloc_mode) =>
        let* '{| can_lift := _;
                 value_slots := value_slots;
                 value_slot_types := value_slot_types;
                 symbol_projections := _
              |} :=
          type_value_slots_and_make_lifting_decision_for_one_set dacc
            Name_mode.normal set_of_closures alloc_mode
        in
        ret (value_slots, value_slot_types))
      all_sets_of_closures
  in
  let* value_slot_types_all_sets :=
    List.map Stdlib_.snd value_slots_and_types_all_sets
  in
  let* context :=
    C.create dacc simplify_function_body all_sets_of_closures
      closure_bound_names_all_sets value_slot_types_all_sets
  in
  let* closure_bound_names_inside_functions_all_sets :=
    C.closure_bound_names_inside_functions_all_sets context
  in
  (* 1192-1211 *)
  List_.fold_left3
    (fun '(T3 patterns_acc static_consts_acc dacc)
         '(closure_symbols, set_of_closures) closure_bound_names_inside
         '(value_slots, value_slot_types) =>
      let* '(T3 pattern static_const dacc) :=
        simplify_lifted_set_of_closures0 dacc context closure_symbols
          closure_bound_names_inside value_slots value_slot_types
          set_of_closures
      in
      (* The order doesn't matter here -- see comment in
         [Simplify_static_const] where this function is called from. *)
      let* static_const_group :=
        Rebuilt_static_const.Group.add static_const static_consts_acc
      in
      let! tmp1 := Bound_static.singleton pattern in
      let! tmp2 := Bound_static.concat tmp1 patterns_acc in
      ret (T3 tmp2 static_const_group dacc))
    (T3 Bound_static.empty Rebuilt_static_const.Group.empty dacc)
    all_sets_of_closures_and_symbols
    closure_bound_names_inside_functions_all_sets
    value_slots_and_types_all_sets.

(* 1213-1230. In the compiler: [dacc code ~all_code
   ~simplify_function_body]. *)
Definition simplify_static_stub_function (dacc : DA.t) (code : Code.t)
    (all_code : Code_id.Map.t Code.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    : M (Rebuilt_static_const.t * DA.t) :=
  let* context :=
    C.create_for_static_stub dacc all_code simplify_function_body
  in
  let& closure_bound_names_inside_function :=
    (* Unused, the type of the value slot is going to be unknown *)
    (Function_slot.Map.empty : Function_slot.Map.t Bound_name.t)
  in
  let* '{| code_id := _;
           code := code;
           outer_dacc := outer_dacc;
           should_resimplify := _
        |} :=
    let! tmp1 := Code.code_id code in
    simplify_function0 context dacc None tmp1 code
      closure_bound_names_inside_function
  in
  let* code :=
    match code with
    | None => assert_false
    | Some (_, code_constant) => ret code_constant
    end
  in
  ret (code, outer_dacc).
