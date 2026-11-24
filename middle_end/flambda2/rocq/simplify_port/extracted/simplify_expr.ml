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
   middle_end/flambda2/rocq/simplify_port/Simplify_expr.v, which follows
   middle_end/flambda2/simplify/simplify_expr.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Simplify_import
open Port_monad

(** val rebuild_terminator : Simplified_expr.simplified_terminator -> UA.t ->
    Simplify_common.after_rebuild -> (RE.t * UA.t) coq_M **)

let rebuild_terminator terminator uacc after_rebuild =
  match terminator with
  | Simplified_expr.Simplified_apply simplified_apply ->
    Simplify_apply_expr.rebuild_apply simplified_apply uacc after_rebuild
  | Simplified_expr.Simplified_apply_cont simplified_apply_cont ->
    (fun x__0 f__1 ->
      let { Simplified_expr.apply_cont = x__1; args = x__2; rewrite_id = x__3 }
          =
        x__0
      in
      f__1 x__1 x__2 x__3) simplified_apply_cont
      (fun apply_cont args rewrite_id ->
        Simplify_apply_cont_expr.rebuild_apply_cont args rewrite_id apply_cont
          uacc after_rebuild)
  | Simplified_expr.Simplified_switch simplified_switch ->
    Simplify_switch_expr.rebuild_switch simplified_switch uacc after_rebuild
  | Simplified_expr.Simplified_invalid invalid ->
    EB.rebuild_invalid uacc invalid after_rebuild

(** val rebuild_expr : Simplified_expr.t -> UA.t ->
    Simplify_common.after_rebuild -> (RE.t * UA.t) coq_M **)

let rec rebuild_expr expr uacc after_rebuild =
  (fun x__0 f__1 ->
    let { Simplified_expr.simplified_lets_and_let_conts = x__1;
          simplified_terminator = x__2;
          removed_operations = x__3;
          is_cold = x__4
        } =
      x__0
    in
    f__1 x__1 x__2 x__3 x__4) expr
    (fun
      simplified_lets_and_let_conts
      simplified_terminator
      removed_operations
      is_cold
    ->
      let rec rebuild_lets_and_let_conts simplified_lets_and_let_conts0 uacc0
          after_rebuild0 =
        match simplified_lets_and_let_conts0 with
        | SE.Simplified_terminator ->
          rebuild_terminator simplified_terminator uacc0 (fun expr0 uacc1 ->
              let uacc2 = UA.notify_removed removed_operations uacc1 in
              let expr1 = if is_cold then RE.mark_as_cold expr0 else expr0 in
              after_rebuild0 expr1 uacc2)
        | SE.Simplified_let (simplified_let, simplified_lets_and_let_conts1) ->
          rebuild_lets_and_let_conts simplified_lets_and_let_conts1 uacc0
            (fun body uacc1 ->
              Simplify_let_expr.rebuild_let (simplified_let, body) uacc1
                after_rebuild0)
        | SE.Simplified_let_cont (let_cont, simplified_lets_and_let_conts1) ->
          Simplify_let_cont_expr.rebuild_let_cont rebuild_lets_and_let_conts
            rebuild_expr
            (let_cont, simplified_lets_and_let_conts1)
            uacc0 after_rebuild0
      in
      rebuild_lets_and_let_conts simplified_lets_and_let_conts uacc
        after_rebuild)

(** val simplify_toplevel_common : DA.t -> (DA.t -> SE.t
    Simplify_common.down_to_up -> (SE.t * DA.t) coq_M) -> Bound_parameters.t ->
    Bound_parameters.t -> Continuation.t -> (_) Flambda_arity.t ->
    Continuation.t -> (RE.t * UA.t) coq_M **)

let simplify_toplevel_common dacc simplify params implicit_params
    return_continuation return_arity exn_continuation =
  let dummy_toplevel_cont =
    (fun x__1 x__2 x__3 -> Continuation.create ?sort:x__1 ?name:x__2 x__3)
      None (Some "dummy_toplevel_continuation") ()
  in
  let dacc0 =
    DA.with_flow_acc
      (Flow.Acc.init_toplevel dummy_toplevel_cont
         (Bound_parameters.append params implicit_params))
      (DA.with_are_lifting_conts dacc
         (Are_lifting_conts.no_lifting At_toplevel))
  in
  let dacc1 =
    DA.record_continuation dacc0 return_continuation
      (Flambda_arity.unarize_t return_arity)
  in
  let dacc2 =
    DA.record_continuation dacc1 exn_continuation
      (Flambda_arity.create
         ((fun x__1 -> Flambda_arity.Component_for_creation.Singleton x__1)
            K.With_subkind.any_value
         :: []))
  in
  let expr, dacc3 = simplify dacc2 (fun dacc3 expr -> expr, dacc3) in
  let expr0, uacc =
    let dacc4 =
      DA.map_flow_acc dacc3 (Flow.Acc.exit_continuation dummy_toplevel_cont)
    in
    let data_flow = DA.flow_acc dacc4 in
    let closure_info = DE.closure_info (DA.denv dacc4) in
    let code_age_relation, used_value_slots, print_name =
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
        (fun _ ->
          ( DA.code_age_relation dacc4,
            Or_unknown.Known (DA.used_value_slots dacc4),
            "toplevel" ))
        (fun _ -> assert false)
        (fun code_id _ _ _ _ ->
          T.Code_age_relation.empty, Or_unknown.Unknown, Code_id.name code_id)
        closure_info
    in
    let flow_result =
      (fun x__1 x__2 x__3 x__4 x__5 x__6 x__7 x__8 x__9 x__10 ->
        Flow.Analysis.analyze ?speculative:x__1 ?print_name:x__2 x__3 x__4 x__5
          x__6 x__7 x__8 x__9 x__10)
        None (Some print_name)
        (DE.machine_width (DA.denv dacc4))
        return_continuation exn_continuation code_age_relation used_value_slots
        (DA.code_ids_to_never_delete dacc4)
        (DA.specialization_map dacc4)
        data_flow
    in
    let continuation_is_cold =
     fun cont ->
      match CUE.get_continuation_uses (DA.continuation_uses_env dacc4) cont with
      | Some uses ->
        List.for_all
          (fun use -> DE.is_cold (One_continuation_use.env_at_use use))
          (Continuation_uses.get_uses uses)
      | None -> false
    in
    let uenv =
      UE.add_function_return_or_exn_continuation
        (UE.create
           (DA.are_rebuilding_terms dacc4)
           (DE.machine_width (DA.denv dacc4)))
        return_continuation
        (continuation_is_cold return_continuation)
        (Flambda_arity.unarize_t return_arity)
    in
    let uenv0 =
      UE.add_function_return_or_exn_continuation uenv exn_continuation
        (continuation_is_cold exn_continuation)
        (Flambda_arity.create_singletons (K.With_subkind.any_value :: []))
    in
    let uacc = UA.create flow_result true uenv0 dacc4 in
    let uacc0 =
      if
        Flow.Analysis.did_perform_mutable_unboxing flow_result
        || Flow.Analysis.added_useful_alias_in_loop (DA.typing_env dacc4)
             data_flow flow_result
      then UA.set_resimplify uacc
      else uacc
    in
    rebuild_expr expr uacc0 (fun expr0 uacc1 -> expr0, uacc1)
  in
  let () =
    NO.fold_continuations_including_in_trap_actions (UA.name_occurrences uacc)
      () (fun _ cont ->
        if
          (not (Continuation.equal cont return_continuation))
          && not (Continuation.equal cont exn_continuation)
        then
          Misc.fatal_errorf
            "Continuation %a should not be free in toplevel expression after \
             simplification (return continuation %a, exn continuation %a):@ %a"
            Continuation.print cont
            (RE.print (UA.are_rebuilding_terms uacc))
            expr0 Continuation.print return_continuation Continuation.print
            exn_continuation
        else ())
  in
  expr0, uacc

(** val simplify_expr : DA.t -> Expr.t -> SE.t Simplify_common.down_to_up ->
    (Simplified_expr.t * Downwards_acc.t) coq_M **)

let rec simplify_expr dacc expr down_to_up0 =
  (fun f__1 f__2 f__3 f__4 f__5 f__6 x__0 ->
    match (x__0 : Flambda.expr_descr) with
    | Flambda.Let x__1 -> f__1 x__1
    | Flambda.Let_cont x__1 -> f__2 x__1
    | Flambda.Apply x__1 -> f__3 x__1
    | Flambda.Apply_cont x__1 -> f__4 x__1
    | Flambda.Switch x__1 -> f__5 x__1
    | Flambda.Invalid { message = x__1 } -> f__6 x__1)
    (fun let_expr -> simplify_let dacc let_expr down_to_up0)
    (fun let_cont ->
      Simplify_let_cont_expr.simplify_let_cont simplify_expr dacc let_cont
        down_to_up0)
    (fun apply ->
      Simplify_apply_expr.simplify_apply simplify_expr rebuild_expr dacc apply
        down_to_up0)
    (fun apply_cont ->
      Simplify_apply_cont_expr.simplify_apply_cont dacc apply_cont down_to_up0)
    (fun switch -> Simplify_switch_expr.simplify_switch dacc switch down_to_up0)
    (fun message ->
      down_to_up0 dacc (Simplified_expr.simplified_invalid (Message message)))
    (Expr.descr expr)

(** val simplify_function_body : DA.t -> Expr.t -> Continuation.t -> (_)
    Flambda_arity.t -> Continuation.t -> Loopify_state.t -> Bound_parameters.t
    -> Bound_parameters.t -> (RE.t * UA.t) coq_M **)

and simplify_function_body dacc expr return_continuation return_arity
    exn_continuation loopify_state params implicit_params =
  match loopify_state with
  | Loopify_state.Do_not_loopify ->
    simplify_toplevel_common dacc
      (fun dacc0 down_to_up0 -> simplify_expr dacc0 expr down_to_up0)
      params implicit_params return_continuation return_arity exn_continuation
  | Loopify_state.Loopify cont ->
    let call_self_cont_expr =
      let args = Bound_parameters.simples params in
      Expr.create_apply_cont
        ((fun x__1 x__2 x__3 x__4 ->
           Apply_cont_expr.create ?trap_action:x__1 x__2 x__3 x__4)
           None cont args Debuginfo.none)
    in
    let handlers =
      Continuation.Lmap.singleton cont
        (Continuation_handler.create params expr Or_unknown.Unknown false false)
    in
    simplify_toplevel_common dacc
      (fun dacc0 down_to_up0 ->
        Simplify_let_cont_expr.simplify_as_recursive_let_cont simplify_expr
          dacc0
          (call_self_cont_expr, handlers)
          down_to_up0)
      params implicit_params return_continuation return_arity exn_continuation

(** val simplify_let : DA.t -> Let.t -> SE.t Simplify_common.down_to_up ->
    (Simplified_expr.t * Downwards_acc.t) coq_M **)

and simplify_let dacc let_expr down_to_up0 =
  Simplify_let_expr.simplify_let simplify_expr simplify_function_body dacc
    let_expr down_to_up0

(** val simplify_toplevel : DA.t -> Expr.t -> Continuation.t -> (_)
    Flambda_arity.t -> Continuation.t -> (RE.t * UA.t) coq_M **)

let simplify_toplevel dacc expr return_continuation return_arity
    exn_continuation =
  let params = Bound_parameters.empty in
  let implicit_params = Bound_parameters.empty in
  simplify_toplevel_common dacc
    (fun dacc0 down_to_up0 -> simplify_expr dacc0 expr down_to_up0)
    params implicit_params return_continuation return_arity exn_continuation
