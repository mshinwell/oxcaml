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

(* This file follows middle_end/flambda2/simplify/simplify_expr.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order, the fuel of the recursive functions) is that of
   GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Apply_cont_expr Are_lifting_conts
  Bound_parameters Closure_info Code_id Continuation Continuation_uses
  Debuginfo Flambda_arity Flow List Loopify_state One_continuation_use
  Or_unknown Simplify_apply_cont_expr Simplify_apply_expr Simplify_common
  Simplify_let_cont_expr Simplify_let_expr Simplify_switch_expr.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 19-29 *)
Definition rebuild_terminator
    (terminator : Simplified_expr.simplified_terminator_) (uacc : UA.t)
    (after_rebuild : Simplify_common.after_rebuild) : M (RE.t * UA.t) :=
  match terminator with
  | Simplified_expr.Simplified_apply simplified_apply =>
    Simplify_apply_expr.rebuild_apply simplified_apply uacc after_rebuild
  | Simplified_expr.Simplified_apply_cont simplified_apply_cont =>
    (* PORT-GAP(type): 25, [Simplified_expr.simplified_apply_cont] is
       abstract in decl/: its eliminator stands for the compiler's record
       pattern [{ apply_cont; args; rewrite_id }]. 26-27,
       [rebuild_apply_cont apply_cont ~args ~rewrite_id uacc
       ~after_rebuild]: the arguments are in the order of the interface. *)
    Simplified_expr.match_simplified_apply_cont_ simplified_apply_cont
      (fun apply_cont args rewrite_id =>
        Simplify_apply_cont_expr.rebuild_apply_cont args rewrite_id apply_cont
          uacc after_rebuild)
  | Simplified_expr.Simplified_switch simplified_switch =>
    Simplify_switch_expr.rebuild_switch simplified_switch uacc after_rebuild
  | Simplified_expr.Simplified_invalid invalid =>
    EB.rebuild_invalid uacc invalid after_rebuild
  end.

(* 31-61 *)
Fixpoint rebuild_expr (fuel : fuel) (expr : Simplified_expr.t) (uacc : UA.t)
    (after_rebuild : Simplify_common.after_rebuild) {struct fuel}
    : M (RE.t * UA.t) :=
  recursive! fuel in
  (* PORT-GAP(type): 32-39, [Simplified_expr.t] is abstract in decl/: its
     eliminator stands for the compiler's record pattern. *)
  Simplified_expr.match_t expr
    (fun simplified_lets_and_let_conts simplified_terminator
         removed_operations is_cold =>
      (* 40: a local [let rec] is Rocq's own [let] of a [fix]. *)
      let rebuild_lets_and_let_conts :=
        fix rebuild_lets_and_let_conts (fuel : Port_monad.fuel)
            (simplified_lets_and_let_conts : SE.simplified_lets_and_let_conts_)
            (uacc : UA.t) (after_rebuild : Simplify_common.after_rebuild)
            {struct fuel} : M (RE.t * UA.t) :=
          recursive! fuel in
          match simplified_lets_and_let_conts with
          | SE.Simplified_terminator =>
            rebuild_terminator simplified_terminator uacc
              (fun expr uacc =>
                let* uacc := UA.notify_removed removed_operations uacc in
                let* expr :=
                  if is_cold then RE.mark_as_cold expr else ret expr
                in
                after_rebuild expr uacc)
          | SE.Simplified_let simplified_let simplified_lets_and_let_conts =>
            rebuild_lets_and_let_conts fuel simplified_lets_and_let_conts uacc
              (fun body uacc =>
                Simplify_let_expr.rebuild_let (simplified_let, body) uacc
                  after_rebuild)
          | SE.Simplified_let_cont let_cont simplified_lets_and_let_conts =>
            (* 56-59: the two functions are passed as values. *)
            let! tmp1 := papp1 rebuild_expr fuel in
            let! tmp2 := papp1 rebuild_lets_and_let_conts fuel in
            Simplify_let_cont_expr.rebuild_let_cont tmp2 tmp1
              (let_cont, simplified_lets_and_let_conts)
              uacc after_rebuild
          end
      in
      rebuild_lets_and_let_conts fuel simplified_lets_and_let_conts uacc
        after_rebuild).

(* 63-168 *)
Definition simplify_toplevel_common (dacc : DA.t)
    (simplify : DA.t -> Simplify_common.down_to_up SE.t -> M (SE.t * DA.t))
    (params implicit_params : Bound_parameters.t)
    (return_continuation : Continuation.t) (return_arity : Flambda_arity.t)
    (exn_continuation : Continuation.t) : M (RE.t * UA.t) :=
  (* 68-70 *)
  let* dummy_toplevel_cont :=
    Continuation.create None (Some "dummy_toplevel_continuation") tt
  in
  (* 71-76: [a |> f b] is [f b a] *)
  let* dacc :=
    let! tmp1 := Are_lifting_conts.no_lifting Are_lifting_conts.At_toplevel in
    let! tmp2 := DA.with_are_lifting_conts dacc tmp1 in
    let! tmp3 := Bound_parameters.append params implicit_params in
    let! tmp4 := Flow.Acc.init_toplevel dummy_toplevel_cont tmp3 in
    DA.with_flow_acc tmp4 tmp2
  in
  (* 77-84 *)
  let* dacc :=
    let! tmp1 := Flambda_arity.unarize_t return_arity in
    DA.record_continuation dacc return_continuation tmp1
  in
  let* dacc :=
    let! tmp1 :=
      Flambda_arity.create
        [Flambda_arity.Component_for_creation.mk_Singleton
           K.With_subkind.any_value]
    in
    DA.record_continuation dacc exn_continuation tmp1
  in
  (* 85 *)
  let* '(expr, dacc) := simplify dacc (fun dacc expr => ret (expr, dacc)) in
  (* 86-150 *)
  let* '(expr, uacc) :=
    let* dacc :=
      (* PORT-GAP(papp): [Flow.Acc.exit_continuation] is given its first
         argument only. *)
      let! tmp1 := papp1 Flow.Acc.exit_continuation dummy_toplevel_cont in
      DA.map_flow_acc dacc tmp1
    in
    let* data_flow := DA.flow_acc dacc in
    let* closure_info :=
      let! tmp1 := DA.denv dacc in
      DE.closure_info tmp1
    in
    (* 98-107 *)
    let* '(T3 code_age_relation used_value_slots print_name) :=
      match closure_info with
      | Closure_info.Closure code_id _ _ _ _ =>
        let! tmp1 := Code_id.name code_id in
        ret (T3 T.Code_age_relation.empty Or_unknown.Unknown tmp1)
      | Closure_info.In_a_set_of_closures_but_not_yet_in_a_specific_closure =>
        assert_false
      | Closure_info.Not_in_a_closure =>
        let! tmp1 := DA.used_value_slots dacc in
        let! tmp2 := DA.code_age_relation dacc in
        ret (T3 tmp2 (Or_unknown.Known tmp1) "toplevel")
      end
    in
    (* 108-115: the arguments are in the order of the interface. *)
    let* flow_result :=
      let! tmp1 := DA.specialization_map dacc in
      let! tmp2 := DA.code_ids_to_never_delete dacc in
      let! tmp3 := DA.denv dacc in
      let! tmp4 := DE.machine_width tmp3 in
      Flow.Analysis.analyze None (Some print_name) tmp4 return_continuation
        exn_continuation code_age_relation used_value_slots tmp2 tmp1
        data_flow
    in
    (* 118-125 *)
    let& continuation_is_cold :=
      fun (cont : Continuation.t) =>
      let! tmp1 := DA.continuation_uses_env dacc in
      let! tmp2 := CUE.get_continuation_uses tmp1 cont in
      match tmp2 with
      | None => (* never returned *) ret false
      | Some uses =>
        let! tmp1 := Continuation_uses.get_uses uses in
        List.for_all
          (fun use =>
            let! tmp2 := One_continuation_use.env_at_use use in
            DE.is_cold tmp2)
          tmp1
      end
    in
    (* 126-139 *)
    let* uenv :=
      let! tmp1 := Flambda_arity.unarize_t return_arity in
      let! tmp2 := continuation_is_cold return_continuation in
      let! tmp3 := DA.denv dacc in
      let! tmp4 := DE.machine_width tmp3 in
      let! tmp5 := DA.are_rebuilding_terms dacc in
      let! tmp6 := UE.create tmp5 tmp4 in
      UE.add_function_return_or_exn_continuation tmp6 return_continuation tmp2
        tmp1
    in
    let* uenv :=
      let! tmp1 := Flambda_arity.create_singletons [K.With_subkind.any_value] in
      let! tmp2 := continuation_is_cold exn_continuation in
      UE.add_function_return_or_exn_continuation uenv exn_continuation tmp2
        tmp1
    in
    (* 140-148 *)
    let* uacc := UA.create flow_result true uenv dacc in
    let* uacc :=
      let! tmp1 := Flow.Analysis.did_perform_mutable_unboxing flow_result in
      let! tmp2 :=
        or_else tmp1
          (let! tmp3 := DA.typing_env dacc in
           Flow.Analysis.added_useful_alias_in_loop tmp3 data_flow flow_result)
      in
      if tmp2 then UA.set_resimplify uacc else ret uacc
    in
    (* 149 *)
    let_fuel! fuel in
    rebuild_expr fuel expr uacc (fun expr uacc => ret (expr, uacc))
  in
  (* 155-167 *)
  (let! tmp1 := UA.name_occurrences uacc in
   NO.fold_continuations_including_in_trap_actions tmp1 tt
     (fun (_ : unit) cont =>
       let! tmp1 := Continuation.equal cont return_continuation in
       let! tmp2 :=
         and_then (negb tmp1)
           (let! tmp3 := Continuation.equal cont exn_continuation in
            ret (negb tmp3))
       in
       if tmp2
       then
         let! tmp3 := UA.are_rebuilding_terms uacc in
         (* PORT-GAP(papp): [RE.print] is given its first argument only. *)
         let! tmp4 := papp1 RE.print tmp3 in
         fatal_errorf8
           "Continuation %a should not be free in toplevel expression after simplification (return continuation %a, exn continuation %a):@ %a"
           Continuation.print cont tmp4 expr Continuation.print
           return_continuation Continuation.print exn_continuation
       else ret tt)) ;;
  ret (expr, uacc).

(* 173-222 *)
Fixpoint simplify_expr (fuel : fuel) (dacc : DA.t) (expr : Expr.t)
    (down_to_up : Simplify_common.down_to_up SE.t) {struct fuel}
    : M (Simplified_expr.t * Downwards_acc.t) :=
  recursive! fuel in
  let! tmp1 := Expr.descr expr in
  match tmp1 with
  | Flambda.Let let_expr => simplify_let fuel dacc let_expr down_to_up
  | Flambda.Let_cont let_cont =>
    let! tmp1 := papp1 simplify_expr fuel in
    Simplify_let_cont_expr.simplify_let_cont tmp1 dacc let_cont down_to_up
  | Flambda.Apply apply =>
    let! tmp1 := papp1 rebuild_expr fuel in
    let! tmp2 := papp1 simplify_expr fuel in
    Simplify_apply_expr.simplify_apply tmp2 tmp1 dacc apply down_to_up
  | Flambda.Apply_cont apply_cont =>
    Simplify_apply_cont_expr.simplify_apply_cont dacc apply_cont down_to_up
  | Flambda.Switch switch =>
    Simplify_switch_expr.simplify_switch dacc switch down_to_up
  | Flambda.Invalid message =>
    let! tmp1 :=
      Simplified_expr.simplified_invalid (Flambda.Invalid.Message message)
    in
    down_to_up dacc tmp1
  end

with simplify_function_body (fuel : fuel) (dacc : DA.t) (expr : Expr.t)
    (return_continuation : Continuation.t) (return_arity : Flambda_arity.t)
    (exn_continuation : Continuation.t) (loopify_state : Loopify_state.t)
    (params implicit_params : Bound_parameters.t) {struct fuel}
    : M (RE.t * UA.t) :=
  recursive! fuel in
  match loopify_state with
  | Loopify_state.Do_not_loopify =>
    (* 197: [(fun dacc -> simplify_expr dacc expr)] *)
    simplify_toplevel_common dacc
      (fun dacc down_to_up => simplify_expr fuel dacc expr down_to_up)
      params implicit_params return_continuation return_arity
      exn_continuation
  | Loopify_state.Loopify cont =>
    let* call_self_cont_expr :=
      let* args := Bound_parameters.simples params in
      let! tmp1 := Apply_cont_expr.create None cont args Debuginfo.none in
      Expr.create_apply_cont tmp1
    in
    let* handlers :=
      let! tmp1 :=
        Continuation_handler.create params expr Or_unknown.Unknown false false
      in
      Continuation.Lmap.singleton cont tmp1
    in
    simplify_toplevel_common dacc
      (fun dacc down_to_up =>
        let! tmp1 := papp1 simplify_expr fuel in
        Simplify_let_cont_expr.simplify_as_recursive_let_cont tmp1 dacc
          (call_self_cont_expr, handlers)
          down_to_up)
      params implicit_params return_continuation return_arity
      exn_continuation
  end

(* PORT-GAP(loose): 216, the attribute [@inline always] is not kept. *)
with simplify_let (fuel : fuel) (dacc : DA.t) (let_expr : Let.t)
    (down_to_up : Simplify_common.down_to_up SE.t) {struct fuel}
    : M (Simplified_expr.t * Downwards_acc.t) :=
  recursive! fuel in
  let! tmp1 := papp1 simplify_function_body fuel in
  let! tmp2 := papp1 simplify_expr fuel in
  Simplify_let_expr.simplify_let tmp2 tmp1 dacc let_expr down_to_up.

(* 224-231 *)
Definition simplify_toplevel (dacc : DA.t) (expr : Expr.t)
    (return_continuation : Continuation.t) (return_arity : Flambda_arity.t)
    (exn_continuation : Continuation.t) : M (RE.t * UA.t) :=
  let& params := Bound_parameters.empty in
  let& implicit_params := Bound_parameters.empty in
  let_fuel! fuel in
  simplify_toplevel_common dacc
    (fun dacc down_to_up => simplify_expr fuel dacc expr down_to_up)
    params implicit_params return_continuation return_arity exn_continuation.
