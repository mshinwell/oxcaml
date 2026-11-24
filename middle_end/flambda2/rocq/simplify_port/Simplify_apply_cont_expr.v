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

(* This file follows middle_end/flambda2/simplify/simplify_apply_cont_expr.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Apply_cont_expr Apply_cont_rewrite_id
  Bound_parameters Code_size Continuation Continuation_callsite_map
  Continuation_in_env Cost_metrics Flow List ListLabels Name_occurrences
  Option Simple Simplified_named Simplify_common.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 19-70 *)
Definition inline_linearly_used_continuation (uacc : UA.t)
    (params' : Bound_parameters.t) (handler : RE.t)
    (free_names_of_handler : Name_occurrences.t)
    (cost_metrics_of_handler : Cost_metrics.t) (apply_cont : AC.t)
    : M (tuple3 RE.t Cost_metrics.t Name_occurrences.t) :=
  let* params := Bound_parameters.to_list params' in
  (* 26 *)
  (let! tmp1 := AC.trap_action apply_cont in
   let! tmp2 := Option.is_none tmp1 in
   assert_ tmp2) ;;
  let* args := AC.args apply_cont in
  (* 33-41 *)
  (let! tmp1 := List.compare_lengths params args in
   if tmp1 <>? 0
   then
     let! tmp2 := UA.are_rebuilding_terms uacc in
     (* PORT-GAP(papp): [RE.print] is given its first argument only. *)
     let! tmp3 := papp1 RE.print tmp2 in
     fatal_errorf8
       "Parameter list@ [%a]@ does not match argument list@ [%a]@ when inlining at [Apply_cont]:@ %a@ Handler to inline:@ %a"
       Bound_parameters.print params' Simple.List.print args Apply_cont.print
       apply_cont tmp3 handler
   else ret tt) ;;
  (* 42-62. [ListLabels.map2 params args ~f]: the arguments are in the order
     of the interface. *)
  let* bindings_outermost_first :=
    ListLabels.map2
      (fun (param : BP.t) (arg : Simple.t) =>
        let* '(param_var, param_uid) := BP.var_and_uid param in
        let* named := Named.create_simple arg in
        (* Get rid of useless [let x = x] bindings from dataflow. *)
        let! tmp1 := Simple.var param_var in
        let! tmp2 := Simple.equal arg tmp1 in
        if tmp2
        then ret (Simplified_named.Delete_binding (Some named))
        else
          let* let_bound :=
            let! tmp1 :=
              Bound_var.create param_var param_uid Name_mode.normal
            in
            Bound_pattern.singleton tmp1
          in
          let* machine_width :=
            let! tmp1 := UA.uenv uacc in
            UE.machine_width tmp1
          in
          let! tmp1 := Simplified_named.create machine_width named in
          ret (Simplified_named.Keep_binding let_bound tmp1 (Some named)))
      params args
  in
  (* 63-70 *)
  let* '(expr, uacc) :=
    let* uacc :=
      let! tmp1 := UA.with_name_occurrences uacc free_names_of_handler in
      UA.with_cost_metrics cost_metrics_of_handler tmp1
    in
    EB.make_new_let_bindings uacc bindings_outermost_first handler
  in
  let! tmp1 := UA.name_occurrences uacc in
  let! tmp2 := UA.cost_metrics uacc in
  ret (T3 expr tmp2 tmp1).

(* 72-174. In the compiler: [~args ~rewrite_id apply_cont uacc
   ~after_rebuild]. *)
Definition rebuild_apply_cont (args : list Simple.t)
    (rewrite_id : Apply_cont_rewrite_id.t) (apply_cont : Apply_cont_expr.t)
    (uacc : UA.t) (after_rebuild : Simplify_common.after_rebuild)
    : M (RE.t * UA.t) :=
  let* uenv := UA.uenv uacc in
  (* 74-82 *)
  let* '(cont, apply_cont) :=
    let* cont := AC.continuation apply_cont in
    match_exn
      (fun _ =>
        let! tmp1 := UA.specialization_map uacc in
        Continuation_callsite_map.find cont rewrite_id tmp1)
      Not_found
      (fun _ => ret (cont, apply_cont))
      (fun specialized =>
        let! tmp1 := AC.with_continuation apply_cont specialized in
        ret (specialized, tmp1))
  in
  (* 86-88 *)
  let* is_cold :=
    let! tmp1 := UA.uenv uacc in
    UE.is_cold_continuation tmp1 cont
  in
  let* apply_cont := AC.update_args apply_cont args in
  let* rewrite := UE.find_apply_cont_rewrite uenv cont in
  (* 89-118 *)
  let& create_apply_cont :=
    fun (apply_cont_to_expr :
          Apply_cont.t -> M (tuple3 RE.t Cost_metrics.t Name_occurrences.t)) =>
    let* rewrite_use_result :=
      let* apply_cont :=
        Simplify_common.clear_demoted_trap_action_and_patch_unused_exn_bucket
          uacc apply_cont
      in
      match rewrite with
      | None =>
        let! tmp1 := UA.uenv uacc in
        EB.no_rewrite_apply_cont tmp1 apply_cont
      | Some rewrite => EB.rewrite_apply_cont uacc rewrite rewrite_id apply_cont
      end
    in
    let* '(T3 expr cost_metrics free_names) :=
      match rewrite_use_result with
      | EB.Invalid message =>
        let! tmp1 := RE.create_invalid (Flambda.Invalid.Message message) in
        ret (T3 tmp1 Cost_metrics.zero Name_occurrences.empty)
      | EB.Apply_cont apply_cont => apply_cont_to_expr apply_cont
      | EB.Expr build_expr => build_expr apply_cont_to_expr
      end
    in
    let* uacc :=
      let! tmp1 := UA.add_free_names uacc free_names in
      UA.add_cost_metrics cost_metrics tmp1
    in
    after_rebuild expr uacc
  in
  (* 119-173 *)
  let& apply_cont_to_expr :=
    fun (apply_cont : Apply_cont.t) =>
    let* cont := AC.continuation apply_cont in
    let! tmp1 := UE.find_continuation uenv cont in
    match tmp1 with
    | Continuation_in_env.Linearly_used_and_inlinable params handler
        free_names_of_handler cost_metrics_of_handler =>
      let* handler := if is_cold then RE.mark_as_cold handler else ret handler in
      inline_linearly_used_continuation uacc params handler
        free_names_of_handler cost_metrics_of_handler apply_cont
    | Continuation_in_env.Invalid _ =>
      let! tmp1 :=
        RE.create_invalid
          (Flambda.Invalid.Apply_cont_of_unreachable_continuation cont)
      in
      ret (T3 tmp1 Cost_metrics.zero Name_occurrences.empty)
    | Continuation_in_env.Non_inlinable_zero_arity _
    | Continuation_in_env.Non_inlinable_non_zero_arity _
    | Continuation_in_env.Toplevel_or_function_return_or_exn_continuation _ =>
      let* is_cold :=
        or_else is_cold
          (let! tmp1 := Apply_cont.continuation apply_cont in
           let! tmp2 := UA.uenv uacc in
           UE.is_cold_continuation tmp2 tmp1)
      in
      let! tmp1 := Apply_cont.free_names apply_cont in
      let! tmp2 := Code_size.apply_cont apply_cont in
      let! tmp3 := Cost_metrics.from_size tmp2 in
      let! tmp4 := RE.create_apply_cont is_cold apply_cont in
      ret (T3 tmp4 tmp3 tmp1)
    end
  in
  create_apply_cont apply_cont_to_expr.

(* 176-199 *)
Definition simplify_apply_cont (dacc : DA.t) (apply_cont : Apply_cont.t)
    (down_to_up : Simplify_common.down_to_up SE.t) : M (SE.t * DA.t) :=
  (* 177-179 *)
  let* '{| S.simples := args; S.simple_tys := arg_types |} :=
    let! tmp1 := AC.args apply_cont in
    S.simplify_simples dacc tmp1
  in
  let* use_kind :=
    Simplify_common.apply_cont_use_kind Simplify_common.Apply_cont_expr
      apply_cont
  in
  (* 183-187 *)
  let* '(dacc, rewrite_id) :=
    let! tmp1 := DA.denv dacc in
    let! tmp2 := AC.continuation apply_cont in
    DA.record_continuation_use dacc tmp2 use_kind tmp1 arg_types
  in
  (* 188-195 *)
  let* dacc :=
    let& record_args_for_data_flow :=
      fun (data_flow : Flow.Acc.t) =>
      let! tmp1 := AC.continuation apply_cont in
      Flow.Acc.add_apply_cont_args rewrite_id tmp1 args data_flow
    in
    DA.map_flow_acc dacc record_args_for_data_flow
  in
  let* dbg := AC.debuginfo apply_cont in
  let* dbg :=
    let! tmp1 := DA.denv dacc in
    DE.add_inlined_debuginfo tmp1 dbg
  in
  let* apply_cont := AC.with_debuginfo apply_cont dbg in
  let! tmp1 := SE.simplified_apply_cont apply_cont args rewrite_id in
  down_to_up dacc tmp1.
