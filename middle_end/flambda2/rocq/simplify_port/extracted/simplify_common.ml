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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Simplify_common.v, which follows
   middle_end/flambda2/simplify/simplify_common.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Simplify_import
open Port_monad

type after_rebuild =
  Rebuilt_expr.t -> Upwards_acc.t -> Rebuilt_expr.t * Upwards_acc.t

type 'a rebuild =
  'a ->
  Upwards_acc.t ->
  after_rebuild:after_rebuild ->
  Rebuilt_expr.t * Upwards_acc.t

type 'a down_to_up =
  Downwards_acc.t -> 'a -> Simplified_expr.t * Downwards_acc.t

type 'a expr_simplifier =
  Downwards_acc.t ->
  'a ->
  down_to_up:Simplified_expr.t down_to_up ->
  Simplified_expr.t * Downwards_acc.t

type simplify_toplevel =
  Downwards_acc.t ->
  Expr.t ->
  return_continuation:Continuation.t ->
  return_arity:[`Complex] Flambda_arity.t ->
  exn_continuation:Continuation.t ->
  Rebuilt_expr.t * Upwards_acc.t

type simplify_function_body =
  Downwards_acc.t ->
  Expr.t ->
  return_continuation:Continuation.t ->
  return_arity:[`Complex] Flambda_arity.t ->
  exn_continuation:Continuation.t ->
  loopify_state:Loopify_state.t ->
  params:Bound_parameters.t ->
  implicit_params:Bound_parameters.t ->
  Rebuilt_expr.t * Upwards_acc.t

(** val simplify_projection : DA.t -> Named.t -> T.t -> T.t -> Bound_var.t ->
    K.t -> Simplify_primitive_result.t coq_M **)

let simplify_projection dacc original_term deconstructing shape result_var
    result_kind =
  let denv = DA.denv dacc in
  let denv0 = DE.define_variable denv result_var result_kind in
  let env = DE.typing_env denv0 in
  match T.meet_shape env deconstructing shape with
  | Or_bottom.Ok env0 ->
    let denv1 = DE.with_typing_env denv0 env0 in
    let dacc0 = DA.with_denv dacc denv1 in
    Simplify_primitive_result.create original_term true dacc0
  | Or_bottom.Bottom ->
    let denv1 =
      DE.add_equation_on_variable denv0 (Bound_var.var result_var)
        (T.bottom result_kind)
    in
    let dacc0 = DA.with_denv dacc denv1 in
    Simplify_primitive_result.create_invalid dacc0

(** val update_exn_continuation_extra_args : UA.t -> Apply_cont_rewrite_id.t ->
    Apply.t -> Apply.t coq_M **)

let update_exn_continuation_extra_args uacc exn_cont_use_id apply =
  let exn_cont_rewrite =
    UE.find_apply_cont_rewrite (UA.uenv uacc)
      (Exn_continuation.exn_handler (Apply.exn_continuation apply))
  in
  match exn_cont_rewrite with
  | Some rewrite ->
    Apply.with_exn_continuation apply
      (Expr_builder.rewrite_exn_continuation rewrite exn_cont_use_id
         (Apply.exn_continuation apply))
  | None -> apply

(** val project_tuple : Target_system.Machine_width.t -> Debuginfo.t -> int ->
    int -> Simple.t -> Named.t coq_M **)

let project_tuple machine_width dbg size field tuple =
  let bak =
    (fun (x__1, x__2, x__3) ->
      (P.Block_access_kind.Values { tag = x__1; size = x__2; field_kind = x__3 }
        : P.Block_access_kind.t))
      ( Known Tag.Scannable.zero,
        Known (Target_ocaml_int.of_int machine_width size),
        Any_value )
  in
  let mutability = Mutability.Immutable in
  let field0 = Target_ocaml_int.of_int machine_width field in
  let prim =
    P.Unary
      ( (fun (x__1, x__2, x__3) ->
          (P.Block_load { kind = x__1; mut = x__2; field = x__3 }
            : P.unary_primitive))
          (bak, mutability, field0),
        tuple )
  in
  Named.create_prim prim dbg

(** val split_direct_over_application : Apply.t -> Code_id.t -> Code_metadata.t
    -> Expr.t coq_M **)

let split_direct_over_application apply callee's_code_id callee's_code_metadata
    =
  let apply_alloc_mode = Apply.return_mode apply in
  let callee's_params_arity =
    Code_metadata.params_arity callee's_code_metadata
  in
  let num_non_unarized_params =
    Flambda_arity.num_params callee's_params_arity
  in
  let args_arity = Apply.args_arity apply in
  let num_non_unarized_args = Flambda_arity.num_params args_arity in
  let () = assert (num_non_unarized_params < num_non_unarized_args) in
  let args = Apply.args apply in
  let first_args, remaining_args =
    Misc.Stdlib.List.split_at
      (Flambda_arity.cardinal_unarized callee's_params_arity)
      args
  in
  let remaining_arity =
    Flambda_arity.partially_apply args_arity num_non_unarized_params
  in
  let () =
    assert (
      List.compare_length_with remaining_args
        (Flambda_arity.cardinal_unarized remaining_arity)
      = 0)
  in
  let func_var =
    (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
      None "full_apply" K.value
  in
  let func_var_duid = Flambda_debug_uid.none in
  let result_mode = Code_metadata.result_mode callee's_code_metadata in
  let outer_apply_alloc_mode = apply_alloc_mode in
  let needs_region, inner_apply_alloc_mode =
    match result_mode with
    | Maybe_alloc_stack ->
      (fun f__1 f__2 x__0 ->
        match (x__0 : Alloc_mode.For_applications.t) with
        | Alloc_mode.For_applications.Not_alloc_stack { alloc_region = x__1 } ->
          f__1 x__1
        | Alloc_mode.For_applications.Maybe_alloc_stack
            { alloc_region = x__1; region = x__2; ghost_region = x__3 } ->
          f__2 x__1 x__2 x__3)
        (fun alloc_region ->
          let region =
            (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
              None "over_app_region" K.region
          in
          let ghost_region =
            (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
              None "over_app_ghost_region" K.region
          in
          ( Some
              ( region,
                ghost_region,
                (fun x__1 x__2 x__3 ->
                  Continuation.create ?sort:x__1 ?name:x__2 x__3)
                  None None () ),
            Alloc_mode.For_applications.maybe_alloc_stack alloc_region region
              ghost_region ))
        (fun _ _ _ -> None, apply_alloc_mode)
        apply_alloc_mode
    | Not_alloc_stack ->
      ( None,
        Alloc_mode.For_applications.not_alloc_stack
          ((fun f__1 f__2 x__0 ->
             match (x__0 : Alloc_mode.For_applications.t) with
             | Alloc_mode.For_applications.Not_alloc_stack
                 { alloc_region = x__1 } ->
               f__1 x__1
             | Alloc_mode.For_applications.Maybe_alloc_stack
                 { alloc_region = x__1; region = x__2; ghost_region = x__3 } ->
               f__2 x__1 x__2 x__3)
             (fun alloc_region -> alloc_region)
             (fun alloc_region _ _ -> alloc_region)
             apply_alloc_mode) )
  in
  let perform_over_application =
    let continuation =
      match needs_region with
      | Some t ->
        let _, _, cont = t in
        Apply_expr.Result_continuation.Return cont
      | None -> Apply.continuation apply
    in
    Apply.create
      (Some (Simple.var func_var))
      continuation
      (Apply.exn_continuation apply)
      remaining_args remaining_arity (Apply.return_arity apply)
      Call_kind.indirect_function_call_unknown_arity outer_apply_alloc_mode
      (Apply.dbg apply) (Apply.inlined apply)
      (Apply.inlining_state apply)
      (Apply.probe apply) (Apply.position apply)
      (Apply.relative_history apply)
  in
  let perform_over_application_free_names =
    Apply.free_names perform_over_application
  in
  let perform_over_application0 =
    match needs_region with
    | Some t ->
      let region, ghost_region, after_over_application = t in
      let over_application_results =
        List.mapi
          (fun i kind ->
            let result_var =
              (fun x__1 x__2 x__3 ->
                Variable.create ?user_visible:x__1 x__2 x__3)
                None
                ("result" ^ string_of_int i)
                (KS.kind kind)
            in
            let result_var_duid = Flambda_debug_uid.none in
            BP.create result_var kind result_var_duid)
          (Flambda_arity.unarize (Apply.return_arity apply))
      in
      let call_return_continuation, call_return_continuation_free_names =
        match Apply.continuation apply with
        | Apply_expr.Result_continuation.Return return_cont ->
          let apply_cont =
            (fun x__1 x__2 x__3 x__4 ->
              Apply_cont.create ?trap_action:x__1 x__2 x__3 x__4)
              None return_cont
              (List.map BP.simple over_application_results)
              (Apply.dbg apply)
          in
          Expr.create_apply_cont apply_cont, Apply_cont.free_names apply_cont
        | Apply_expr.Result_continuation.Never_returns ->
          Expr.create_invalid (Over_application_never_returns apply), NO.empty
      in
      let handler_expr =
        Expr.create_let
          (Let.create
             (Bound_pattern.singleton
                (Bound_var.create
                   ((fun x__1 x__2 x__3 ->
                      Variable.create ?user_visible:x__1 x__2 x__3)
                      None "unit" K.value)
                   Flambda_debug_uid.none Name_mode.normal))
             (Named.create_prim
                (P.Unary
                   ( (fun x__1 ->
                       (P.End_region { ghost = x__1 } : P.unary_primitive))
                       false,
                     Simple.var region ))
                (Apply.dbg apply))
             (Expr.create_let
                (Let.create
                   (Bound_pattern.singleton
                      (Bound_var.create
                         ((fun x__1 x__2 x__3 ->
                            Variable.create ?user_visible:x__1 x__2 x__3)
                            None "unit" K.value)
                         Flambda_debug_uid.none Name_mode.normal))
                   (Named.create_prim
                      (P.Unary
                         ( (fun x__1 ->
                             (P.End_region { ghost = x__1 } : P.unary_primitive))
                             true,
                           Simple.var ghost_region ))
                      (Apply.dbg apply))
                   call_return_continuation
                   (Known call_return_continuation_free_names)))
             (Known
                (NO.remove_var call_return_continuation_free_names ghost_region)))
      in
      let handler_expr_free_names =
        NO.add_variable call_return_continuation_free_names region
          Name_mode.normal
      in
      let handler =
        Continuation_handler.create
          (Bound_parameters.create over_application_results)
          handler_expr (Known handler_expr_free_names) false false
      in
      Let_cont.create_non_liftable after_over_application handler
        (Expr.create_apply perform_over_application)
        (Known perform_over_application_free_names)
    | None -> Expr.create_apply perform_over_application
  in
  let after_full_application =
    (fun x__1 x__2 x__3 -> Continuation.create ?sort:x__1 ?name:x__2 x__3)
      None None ()
  in
  let full_apply_result_arity =
    Code_metadata.result_arity callee's_code_metadata
  in
  let after_full_application_handler =
    if not (Flambda_arity.is_one_param_of_kind_value full_apply_result_arity)
    then
      let params =
        Bound_parameters.create
          (List.map
             (fun kind ->
               Bound_parameter.create
                 ((fun x__1 x__2 x__3 ->
                    Variable.create ?user_visible:x__1 x__2 x__3)
                    None "over_app_result" (KS.kind kind))
                 kind Flambda_debug_uid.none)
             (Flambda_arity.unarize full_apply_result_arity))
      in
      Continuation_handler.create params
        (Expr.create_invalid (Over_application_never_returns apply))
        (Known Name_occurrences.empty) false true
    else
      let func_param =
        BP.create func_var K.With_subkind.any_value func_var_duid
      in
      Continuation_handler.create
        (Bound_parameters.create (func_param :: []))
        perform_over_application0 (Known perform_over_application_free_names)
        false false
  in
  let full_apply =
    Apply.create (Apply.callee apply)
      (Apply_expr.Result_continuation.Return after_full_application)
      (Apply.exn_continuation apply)
      first_args callee's_params_arity
      (Code_metadata.result_arity callee's_code_metadata)
      (Call_kind.direct_function_call callee's_code_id)
      inner_apply_alloc_mode (Apply.dbg apply) (Apply.inlined apply)
      (Apply.inlining_state apply)
      (Apply.probe apply) (Apply.position apply)
      (Apply.relative_history apply)
  in
  let both_applications =
    Let_cont.create_non_liftable after_full_application
      after_full_application_handler
      (Expr.create_apply full_apply)
      (Known (Apply.free_names full_apply))
  in
  match needs_region with
  | Some t ->
    let region, ghost_region, _ = t in
    let free_names_of_body =
      NO.union (Apply.free_names full_apply) perform_over_application_free_names
    in
    let region_duid = Flambda_debug_uid.none in
    let ghost_region_duid = Flambda_debug_uid.none in
    Expr.create_let
      (Let.create
         (Bound_pattern.singleton
            (Bound_var.create region region_duid Name_mode.normal))
         (Named.create_prim
            (P.Variadic
               ( (fun x__1 ->
                   (P.Begin_region { ghost = x__1 } : P.variadic_primitive))
                   false,
                 [] ))
            (Apply.dbg apply))
         (Expr.create_let
            (Let.create
               (Bound_pattern.singleton
                  (Bound_var.create ghost_region ghost_region_duid
                     Name_mode.normal))
               (Named.create_prim
                  (P.Variadic
                     ( (fun x__1 ->
                         (P.Begin_region { ghost = x__1 }
                           : P.variadic_primitive))
                         false,
                       [] ))
                  (Apply.dbg apply))
               both_applications (Known free_names_of_body)))
         (Known (NO.remove_var free_names_of_body ghost_region)))
  | None -> both_applications

type apply_cont_context =
  | Apply_cont_expr
  | Switch_branch

(** val apply_cont_use_kind : apply_cont_context -> Apply_cont.t ->
    Continuation_use_kind.t coq_M **)

let apply_cont_use_kind context apply_cont =
  let default =
    match context with
    | Apply_cont_expr -> Continuation_use_kind.Inlinable
    | Switch_branch ->
      (fun x__1 ->
        (Continuation_use_kind.Non_inlinable { escaping = x__1 }
          : Continuation_use_kind.t))
        false
  in
  match Continuation.sort (AC.continuation apply_cont) with
  | Continuation.Sort.Normal_or_exn -> (
    match Apply_cont.trap_action apply_cont with
    | Some t ->
      (fun f__1 f__2 x__0 ->
        match (x__0 : Trap_action.t) with
        | Trap_action.Push { exn_handler = x__1 } -> f__1 x__1
        | Trap_action.Pop { exn_handler = x__1; raise_kind = x__2 } ->
          f__2 x__1 x__2)
        (fun _ ->
          (fun x__1 ->
            (Continuation_use_kind.Non_inlinable { escaping = x__1 }
              : Continuation_use_kind.t))
            false)
        (fun _ raise_kind ->
          match raise_kind with
          | Some t0 -> (
            match t0 with
            | Regular ->
              if Flambda_features.debug ()
              then
                (fun x__1 ->
                  (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                    : Continuation_use_kind.t))
                  true
              else
                (fun x__1 ->
                  (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                    : Continuation_use_kind.t))
                  false
            | Reraise ->
              if Flambda_features.debug ()
              then
                (fun x__1 ->
                  (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                    : Continuation_use_kind.t))
                  true
              else
                (fun x__1 ->
                  (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                    : Continuation_use_kind.t))
                  false
            | No_trace ->
              (fun x__1 ->
                (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                  : Continuation_use_kind.t))
                false)
          | None ->
            if Flambda_features.debug ()
            then
              (fun x__1 ->
                (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                  : Continuation_use_kind.t))
                true
            else
              (fun x__1 ->
                (Continuation_use_kind.Non_inlinable { escaping = x__1 }
                  : Continuation_use_kind.t))
                false)
        t
    | None -> default)
  | Continuation.Sort.Return ->
    (fun x__1 ->
      (Continuation_use_kind.Non_inlinable { escaping = x__1 }
        : Continuation_use_kind.t))
      false
  | Continuation.Sort.Define_root_symbol ->
    let () = assert (Option.is_none (Apply_cont.trap_action apply_cont)) in
    default
  | Continuation.Sort.Toplevel_return ->
    (fun x__1 ->
      (Continuation_use_kind.Non_inlinable { escaping = x__1 }
        : Continuation_use_kind.t))
      false

(** val clear_demoted_trap_action : UA.t -> AC.t -> AC.t coq_M **)

let clear_demoted_trap_action uacc apply_cont =
  match AC.trap_action apply_cont with
  | Some t ->
    (fun f__1 f__2 x__0 ->
      match (x__0 : Trap_action.t) with
      | Trap_action.Push { exn_handler = x__1 } -> f__1 x__1
      | Trap_action.Pop { exn_handler = x__1; raise_kind = x__2 } ->
        f__2 x__1 x__2)
      (fun exn_handler ->
        if
          UE.mem_continuation (UA.uenv uacc) exn_handler
          && not (UA.is_demoted_exn_handler uacc exn_handler)
        then apply_cont
        else AC.clear_trap_action apply_cont)
      (fun exn_handler _ ->
        if
          UE.mem_continuation (UA.uenv uacc) exn_handler
          && not (UA.is_demoted_exn_handler uacc exn_handler)
        then apply_cont
        else AC.clear_trap_action apply_cont)
      t
  | None -> apply_cont

(** val patch_unused_exn_bucket : UA.t -> AC.t -> AC.t coq_M **)

let patch_unused_exn_bucket uacc apply_cont =
  if AC.is_raise apply_cont
  then
    match AC.args apply_cont with
    | [] -> assert false
    | exn_value :: other_args ->
      let exn_value_is_used =
        Simple.pattern_match exn_value
          (fun name _ -> Name.Set.mem name (UA.required_names uacc))
          (fun _ -> true)
      in
      if exn_value_is_used
      then apply_cont
      else
        let dummy_value = Simple.const_zero (UE.machine_width (UA.uenv uacc)) in
        AC.update_args apply_cont (dummy_value :: other_args)
  else apply_cont

(** val clear_demoted_trap_action_and_patch_unused_exn_bucket : UA.t -> AC.t ->
    AC.t coq_M **)

let clear_demoted_trap_action_and_patch_unused_exn_bucket uacc apply_cont =
  let apply_cont0 = clear_demoted_trap_action uacc apply_cont in
  patch_unused_exn_bucket uacc apply_cont0

(** val specialise_array_kind : DA.t -> P.Array_kind.t -> T.t -> P.Array_kind.t
    Or_bottom.t coq_M **)

let specialise_array_kind dacc array_kind array_ty =
  let typing_env = DA.typing_env dacc in
  let for_naked_number =
   fun kind ->
    (fun f__1 f__2 f__3 x__0 ->
      match (x__0 : _ T.meet_shortcut) with
      | T.Known_result x__1 -> f__1 x__1
      | T.Need_meet -> f__2 ()
      | T.Invalid -> f__3 ())
      (fun u ->
        let () = u in
        Or_bottom.Ok array_kind)
      (fun _ -> Or_bottom.Ok array_kind)
      (fun _ -> Or_bottom.Bottom)
      (T.meet_is_non_empty_naked_number_array kind typing_env array_ty)
  in
  match array_kind with
  | P.Array_kind.Immediates ->
    (fun f__1 f__2 f__3 x__0 ->
      match (x__0 : _ T.meet_shortcut) with
      | T.Known_result x__1 -> f__1 x__1
      | T.Need_meet -> f__2 ()
      | T.Invalid -> f__3 ())
      (fun b -> if b then Or_bottom.Bottom else Or_bottom.Ok array_kind)
      (fun _ -> Or_bottom.Ok array_kind)
      (fun _ -> Or_bottom.Bottom)
      (T.meet_is_flat_float_array typing_env array_ty)
  | P.Array_kind.Gc_ignorable_values -> (
    match T.prove_is_immediates_array typing_env array_ty with
    | Proved u ->
      let () = u in
      Or_bottom.Ok P.Array_kind.Immediates
    | Unknown ->
      (fun f__1 f__2 f__3 x__0 ->
        match (x__0 : _ T.meet_shortcut) with
        | T.Known_result x__1 -> f__1 x__1
        | T.Need_meet -> f__2 ()
        | T.Invalid -> f__3 ())
        (fun b -> if b then Or_bottom.Bottom else Or_bottom.Ok array_kind)
        (fun _ -> Or_bottom.Ok array_kind)
        (fun _ -> Or_bottom.Bottom)
        (T.meet_is_flat_float_array typing_env array_ty))
  | P.Array_kind.Values -> (
    match T.prove_is_immediates_array typing_env array_ty with
    | Proved u ->
      let () = u in
      Or_bottom.Ok P.Array_kind.Immediates
    | Unknown ->
      (fun f__1 f__2 f__3 x__0 ->
        match (x__0 : _ T.meet_shortcut) with
        | T.Known_result x__1 -> f__1 x__1
        | T.Need_meet -> f__2 ()
        | T.Invalid -> f__3 ())
        (fun b -> if b then Or_bottom.Bottom else Or_bottom.Ok array_kind)
        (fun _ -> Or_bottom.Ok array_kind)
        (fun _ -> Or_bottom.Bottom)
        (T.meet_is_flat_float_array typing_env array_ty))
  | P.Array_kind.Naked_floats -> for_naked_number Naked_float
  | P.Array_kind.Naked_float32s -> for_naked_number Naked_float32
  | P.Array_kind.Naked_ints -> for_naked_number Naked_immediate
  | P.Array_kind.Naked_int8s -> for_naked_number Naked_int8
  | P.Array_kind.Naked_int16s -> for_naked_number Naked_int16
  | P.Array_kind.Naked_int32s -> for_naked_number Naked_int32
  | P.Array_kind.Naked_int64s -> for_naked_number Naked_int64
  | P.Array_kind.Naked_nativeints -> for_naked_number Naked_nativeint
  | P.Array_kind.Naked_vec128s -> for_naked_number Naked_vec128
  | P.Array_kind.Naked_vec256s -> for_naked_number Naked_vec256
  | P.Array_kind.Naked_vec512s -> for_naked_number Naked_vec512
  | P.Array_kind.Naked_masks -> for_naked_number Naked_mask
  | P.Array_kind.Unboxed_product _ -> Or_bottom.Ok array_kind

(** val add_symbol_projection : DA.t -> Simple.t ->
    Symbol_projection.Projection.t -> Bound_var.t -> K.With_subkind.t -> DA.t
    coq_M **)

let add_symbol_projection dacc projected_from projection projection_bound_to
    kind =
  if DE.at_unit_toplevel (DA.denv dacc)
  then dacc
  else
    Simple.pattern_match' projected_from
      (fun _ _ -> dacc)
      (fun symbol_projected_from _ ->
        let proj =
          Symbol_projection.create symbol_projected_from projection kind
        in
        let var = Bound_var.var projection_bound_to in
        DA.map_denv dacc (fun denv -> DE.add_symbol_projection denv var proj))
      (fun _ -> dacc)
