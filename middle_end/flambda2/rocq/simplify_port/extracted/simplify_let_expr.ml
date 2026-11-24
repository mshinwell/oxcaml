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
   middle_end/flambda2/rocq/simplify_port/Simplify_let_expr.v, which follows
   middle_end/flambda2/simplify/simplify_let_expr.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Simplify_import
open Port_monad

(** val keep_lifted_constant_only_if_used : Upwards_acc.t ->
    Lifted_constant_state.t -> Lifted_constant.t -> Lifted_constant_state.t
    coq_M **)

let keep_lifted_constant_only_if_used uacc acc lifted_constant =
  let bound = Lifted_constant.bound_static lifted_constant in
  let code_ids_live =
    match Upwards_acc.reachable_code_ids uacc with
    | Or_unknown.Known t ->
      let { Flow_types.Reachable_code_ids.live_code_ids = _;
            Flow_types.Reachable_code_ids.ancestors_of_live_code_ids =
              ancestors_of_live_code_ids0
          } =
        t
      in
      not
        (Code_id.Set.disjoint
           (Bound_static.code_being_defined bound)
           ancestors_of_live_code_ids0)
    | Or_unknown.Unknown -> Bound_static.binds_code bound
  in
  let symbols_live =
    not
      (Name.Set.disjoint
         (Name.set_of_symbol_set (Bound_static.symbols_being_defined bound))
         (Upwards_acc.required_names uacc))
  in
  if symbols_live || code_ids_live
  then Lifted_constant_state.add acc lifted_constant
  else acc

(** val rebuild_let : (Simplify_import.SE.simplified_defining_expr *
    Rebuilt_expr.t) -> Upwards_acc.t -> Simplify_common.after_rebuild ->
    (Rebuilt_expr.t * Upwards_acc.t) coq_M **)

let rebuild_let arg uacc after_rebuild =
  let s, body = arg in
  let { Simplify_import.SE.bindings_to_place = bindings_to_place0;
        Simplify_import.SE.removed_operations = removed_operations0;
        Simplify_import.SE.lifted_constants_from_defining_expr =
          lifted_constants_from_defining_expr0;
        Simplify_import.SE.at_unit_toplevel = at_unit_toplevel0;
        Simplify_import.SE.closure_info = closure_info0;
        Simplify_import.SE.rewrite_id = rewrite_id0
      } =
    s
  in
  let lifted_constants_from_defining_expr1 =
    match Closure_info.in_or_out_of_closure closure_info0 with
    | Closure_info.In_a_closure -> lifted_constants_from_defining_expr0
    | Closure_info.Not_in_a_closure ->
      Lifted_constant_state.fold lifted_constants_from_defining_expr0
        Lifted_constant_state.empty
        (keep_lifted_constant_only_if_used uacc)
  in
  let no_constants_from_defining_expr =
    Lifted_constant_state.is_empty lifted_constants_from_defining_expr1
  in
  let no_constants_to_place =
    no_constants_from_defining_expr && Upwards_acc.no_lifted_constants uacc
  in
  let put_bindings_around_body =
   fun uacc0 body0 ->
    let uacc1 = Upwards_acc.notify_removed removed_operations0 uacc0 in
    let bindings =
      List.map
        (fun binding ->
          (fun f__1 f__2 x__0 ->
            match (x__0 : Simplified_named.binding_to_place) with
            | Simplified_named.Keep_binding
                { let_bound = x__1;
                  simplified_defining_expr = x__2;
                  original_defining_expr = x__3
                } ->
              f__1 x__1 x__2 x__3
            | Simplified_named.Delete_binding { original_defining_expr = x__1 }
              ->
              f__2 x__1)
            (fun let_bound simplified_defining_expr0 original_defining_expr ->
              match simplified_defining_expr0.Simplified_named.named with
              | Simplified_named.Simple _ -> binding
              | Simplified_named.Prim (prim, _) -> (
                match Bound_pattern.must_be_singleton_opt let_bound with
                | Some bound_var -> (
                  let simple = Simple.var (Bound_var.var bound_var) in
                  match
                    Downwards_acc.find_debuginfo_rewrite
                      (Upwards_acc.creation_dacc uacc1)
                      simple
                  with
                  | Some dbg ->
                    let machine_width =
                      Upwards_env.machine_width (Upwards_acc.uenv uacc1)
                    in
                    (fun (x__1, x__2, x__3) ->
                      (Simplified_named.Keep_binding
                         { let_bound = x__1;
                           simplified_defining_expr = x__2;
                           original_defining_expr = x__3
                         }
                        : Simplified_named.binding_to_place))
                      ( let_bound,
                        Simplified_named.create machine_width
                          (Flambda.Named.create_prim prim dbg),
                        original_defining_expr )
                  | None -> binding)
                | None -> binding)
              | Simplified_named.Set_of_closures (_, _) -> binding
              | Simplified_named.Rec_info _ -> binding)
            (fun _ -> binding)
            binding)
        bindings_to_place0
    in
    let generate_phantom_lets = Upwards_acc.generate_phantom_lets uacc1 in
    let free_names_of_body = Upwards_acc.name_occurrences uacc1 in
    let compute_greatest_name_mode =
     fun bound_vars ->
      match bound_vars with
      | Bound_pattern.Singleton bound_var ->
        Name_occurrences.greatest_name_mode_var free_names_of_body
          (Bound_var.var bound_var)
      | Bound_pattern.Set_of_closures _ ->
        Bound_pattern.fold_all_bound_vars bound_vars Name_mode.Or_absent.absent
          (fun greatest_name_mode bound_var ->
            Name_mode.Or_absent.join_in_terms greatest_name_mode
              (Name_occurrences.greatest_name_mode_var free_names_of_body
                 (Bound_var.var bound_var)))
      | Bound_pattern.Static _ -> assert false
    in
    let bindings0 =
      List.map
        (fun binding_to_place ->
          (fun f__1 f__2 x__0 ->
            match (x__0 : Simplified_named.binding_to_place) with
            | Simplified_named.Keep_binding
                { let_bound = x__1;
                  simplified_defining_expr = x__2;
                  original_defining_expr = x__3
                } ->
              f__1 x__1 x__2 x__3
            | Simplified_named.Delete_binding { original_defining_expr = x__1 }
              ->
              f__2 x__1)
            (fun bound_vars simplified_defining_expr0 original_defining_expr ->
              let greatest_name_mode = compute_greatest_name_mode bound_vars in
              let declared_name_mode = Bound_pattern.name_mode bound_vars in
              let mismatched_modes =
                match
                  Name_mode.Or_absent.compare_partial_order greatest_name_mode
                    (Name_mode.Or_absent.present declared_name_mode)
                with
                | Some c -> c > 0
                | None -> true
              in
              let defining_expr =
                Simplified_named.to_named
                  simplified_defining_expr0.Simplified_named.named
              in
              let () =
                if mismatched_modes
                then
                  Misc.fatal_errorf
                    "[Let]-binding declares variable(s) %a (mode %a) to be \
                     bound to@ %a,@ but there exist occurrences for such \
                     variable(s) at incompatible mode(s)@ (compared to %a)@ in \
                     the body (free names %a):@ %a"
                    Bound_pattern.print bound_vars Name_mode.print
                    declared_name_mode Flambda.Named.print defining_expr
                    Name_mode.Or_absent.print greatest_name_mode
                    Name_occurrences.print free_names_of_body
                    (Rebuilt_expr.print
                       (Upwards_acc.are_rebuilding_terms uacc1))
                    body0
                else ()
              in
              let is_end_region =
                match defining_expr with
                | Flambda.Simple _ -> None
                | Flambda.Prim (prim, _) -> Flambda_primitive.is_end_region prim
                | Flambda.Set_of_closures (_, _) -> None
                | Flambda.Static_consts _ -> None
                | Flambda.Rec_info _ -> None
              in
              let is_end_region_for_unused_region, is_end_region_for_used_region
                  =
                match is_end_region with
                | Some region ->
                  let is_used =
                    Name.Set.mem (Name.var region)
                      (Upwards_acc.required_names uacc1)
                  in
                  not is_used, is_used
                | None -> false, false
              in
              let must_be_kept_for_its_effects =
                is_end_region_for_used_region
                || (not is_end_region_for_unused_region)
                   && not
                        (Flambda.Named.at_most_generative_effects defining_expr)
              in
              if must_be_kept_for_its_effects
              then
                let () =
                  if not (Name_mode.is_normal declared_name_mode)
                  then
                    Misc.fatal_errorf
                      "Cannot [Let]-bind non-normal variable(s) to a [Named] \
                       that has more than generative effects:@ %a@ =@ %a"
                      Bound_pattern.print bound_vars Flambda.Named.print
                      defining_expr
                  else ()
                in
                binding_to_place
              else
                let is_depth =
                  match defining_expr with
                  | Flambda.Simple _ -> false
                  | Flambda.Prim (_, _) -> false
                  | Flambda.Set_of_closures (_, _) -> false
                  | Flambda.Static_consts _ -> false
                  | Flambda.Rec_info _ -> true
                in
                let has_uses =
                  Name_mode.Or_absent.is_present greatest_name_mode
                in
                let can_phantomise =
                  (not is_depth)
                  && Bound_pattern.exists_all_bound_vars bound_vars
                       (fun bound_var ->
                         Variable.user_visible (Bound_var.var bound_var))
                in
                let will_delete_binding =
                  if is_end_region_for_unused_region
                  then true
                  else
                    not (has_uses || (generate_phantom_lets && can_phantomise))
                in
                if will_delete_binding
                then
                  (fun x__1 ->
                    (Simplified_named.Delete_binding
                       { original_defining_expr = x__1 }
                      : Simplified_named.binding_to_place))
                    original_defining_expr
                else
                  let name_mode =
                    match greatest_name_mode with
                    | Name_mode.Or_absent.Absent -> Name_mode.phantom
                    | Name_mode.Or_absent.Present name_mode -> name_mode
                  in
                  let () = assert (Name_mode.can_be_in_terms name_mode) in
                  let bound_vars0 =
                    Bound_pattern.with_name_mode bound_vars name_mode
                  in
                  (fun (x__1, x__2, x__3) ->
                    (Simplified_named.Keep_binding
                       { let_bound = x__1;
                         simplified_defining_expr = x__2;
                         original_defining_expr = x__3
                       }
                      : Simplified_named.binding_to_place))
                    ( bound_vars0,
                      simplified_defining_expr0,
                      original_defining_expr ))
            (fun _ -> binding_to_place)
            binding_to_place)
        bindings
    in
    let uacc2, bindings1 =
      let { Flow_types.Mutable_unboxing_result.did_unbox_a_mutable_block = _;
            Flow_types.Mutable_unboxing_result.additional_epa = _;
            Flow_types.Mutable_unboxing_result.let_rewrites = let_rewrites0
          } =
        Upwards_acc.mutable_unboxing_result uacc1
      in
      Port_monad.match_exn
        (fun _ -> Named_rewrite_id.Map.find rewrite_id0 let_rewrites0)
        Port_monad.not_found
        (fun _ -> uacc1, bindings0)
        (fun rewrite ->
          match bindings0 with
          | [] -> uacc1, []
          | binding :: l -> (
            match l with
            | [] ->
              (fun f__1 f__2 x__0 ->
                match (x__0 : Simplified_named.binding_to_place) with
                | Simplified_named.Keep_binding
                    { let_bound = x__1;
                      simplified_defining_expr = x__2;
                      original_defining_expr = x__3
                    } ->
                  f__1 x__1 x__2 x__3
                | Simplified_named.Delete_binding
                    { original_defining_expr = x__1 } ->
                  f__2 x__1)
                (fun let_bound simplified_defining_expr0 original_defining_expr
                   ->
                  let (Named_rewrite.Prim_rewrite prim_rewrite) = rewrite in
                  match original_defining_expr with
                  | Some t -> (
                    match t with
                    | Flambda.Simple _ ->
                      Misc.fatal_errorf
                        "Prim_rewrite applied to a non-prim Named.t"
                    | Flambda.Prim (original_prim, dbg) ->
                      let uacc2 =
                        Upwards_acc.notify_removed
                          (Removed_operations.prim original_prim)
                          uacc1
                      in
                      let machine_width =
                        Upwards_env.machine_width (Upwards_acc.uenv uacc2)
                      in
                      let new_bindings =
                        (fun f__1 f__2 f__3 x__0 ->
                          match (x__0 : Named_rewrite.Prim_rewrite.t) with
                          | Named_rewrite.Prim_rewrite.Remove_prim -> f__1 ()
                          | Named_rewrite.Prim_rewrite.Invalid x__1 -> f__2 x__1
                          | Named_rewrite.Prim_rewrite.Replace_by_binding
                              { var = x__1; bound_to = x__2 } ->
                            f__3 x__1 x__2)
                          (fun _ ->
                            let greatest_name_mode =
                              compute_greatest_name_mode let_bound
                            in
                            match greatest_name_mode with
                            | Name_mode.Or_absent.Absent ->
                              (fun x__1 ->
                                (Simplified_named.Delete_binding
                                   { original_defining_expr = x__1 }
                                  : Simplified_named.binding_to_place))
                                original_defining_expr
                              :: []
                            | Name_mode.Or_absent.Present name_mode ->
                              if Name_mode.is_phantom name_mode
                              then
                                let let_bound0 =
                                  Bound_pattern.with_name_mode let_bound
                                    name_mode
                                in
                                (fun (x__1, x__2, x__3) ->
                                  (Simplified_named.Keep_binding
                                     { let_bound = x__1;
                                       simplified_defining_expr = x__2;
                                       original_defining_expr = x__3
                                     }
                                    : Simplified_named.binding_to_place))
                                  ( let_bound0,
                                    simplified_defining_expr0,
                                    original_defining_expr )
                                :: []
                              else
                                Misc.fatal_errorf
                                  "Binding for %a was supposed to be removed \
                                   but occurs in free names:@ %a"
                                  Bound_pattern.print let_bound
                                  Name_occurrences.print free_names_of_body)
                          (fun k ->
                            let prim =
                              Flambda_primitive.Nullary
                                (Flambda_primitive.Invalid k)
                            in
                            let simplified_defining_expr1 =
                              Simplified_named.create machine_width
                                (Flambda.Named.create_prim prim dbg)
                            in
                            (fun (x__1, x__2, x__3) ->
                              (Simplified_named.Keep_binding
                                 { let_bound = x__1;
                                   simplified_defining_expr = x__2;
                                   original_defining_expr = x__3
                                 }
                                : Simplified_named.binding_to_place))
                              ( let_bound,
                                simplified_defining_expr1,
                                original_defining_expr )
                            :: [])
                          (fun var bound_to ->
                            let bv =
                              Bound_pattern.must_be_singleton let_bound
                            in
                            let var' = Bound_var.var bv in
                            let () = assert (Variable.equal var var') in
                            let simplified_defining_expr1 =
                              Simplified_named.create machine_width
                                (Flambda.Named.create_simple bound_to)
                            in
                            (fun (x__1, x__2, x__3) ->
                              (Simplified_named.Keep_binding
                                 { let_bound = x__1;
                                   simplified_defining_expr = x__2;
                                   original_defining_expr = x__3
                                 }
                                : Simplified_named.binding_to_place))
                              ( let_bound,
                                simplified_defining_expr1,
                                original_defining_expr )
                            :: [])
                          prim_rewrite
                      in
                      uacc2, new_bindings
                    | Flambda.Set_of_closures (_, _) ->
                      Misc.fatal_errorf
                        "Prim_rewrite applied to a non-prim Named.t"
                    | Flambda.Static_consts _ ->
                      Misc.fatal_errorf
                        "Prim_rewrite applied to a non-prim Named.t"
                    | Flambda.Rec_info _ ->
                      Misc.fatal_errorf
                        "Prim_rewrite applied to a non-prim Named.t")
                  | None ->
                    Misc.fatal_errorf
                      "Prim_rewrite applied to a non-prim Named.t")
                (fun _ -> uacc1, binding :: [])
                binding
            | _ :: _ -> assert false))
    in
    Expr_builder.make_new_let_bindings uacc2 bindings1 body0
  in
  if no_constants_to_place || not at_unit_toplevel0
  then
    let uacc0 =
      if no_constants_from_defining_expr
      then uacc
      else
        let lifted_constants_from_body = Upwards_acc.lifted_constants uacc in
        Upwards_acc.with_lifted_constants uacc
          (Lifted_constant_state.union lifted_constants_from_body
             lifted_constants_from_defining_expr1)
    in
    let body0, uacc1 = put_bindings_around_body uacc0 body in
    after_rebuild body0 uacc1
  else
    let uacc0, lifted_constants_from_body =
      Upwards_acc.get_and_clear_lifted_constants uacc
    in
    let body0, uacc1 =
      Expr_builder.place_lifted_constants uacc0
        lifted_constants_from_defining_expr1 lifted_constants_from_body
        put_bindings_around_body body
    in
    after_rebuild body0 uacc1

(** val record_new_defining_expression_binding_for_data_flow : Downwards_acc.t
    -> Named_rewrite_id.t -> Flow.Acc.t -> Simplified_named.binding_to_place ->
    Flow.Acc.t coq_M **)

let record_new_defining_expression_binding_for_data_flow dacc rewrite_id0
    data_flow binding =
  let generate_phantom_lets =
    Downwards_env.generate_phantom_lets (Downwards_acc.denv dacc)
  in
  (fun f__1 f__2 x__0 ->
    match (x__0 : Simplified_named.binding_to_place) with
    | Simplified_named.Keep_binding
        { let_bound = x__1;
          simplified_defining_expr = x__2;
          original_defining_expr = x__3
        } ->
      f__1 x__1 x__2 x__3
    | Simplified_named.Delete_binding { original_defining_expr = x__1 } ->
      f__2 x__1)
    (fun let_bound simplified_defining_expr0 _ ->
      Flow.Acc.record_let_binding rewrite_id0 generate_phantom_lets let_bound
        simplified_defining_expr0 data_flow)
    (fun _ -> data_flow)
    binding

(** val update_data_flow : Downwards_acc.t -> Closure_info.t ->
    Lifted_constant_state.t -> Simplify_named_result.t -> Named_rewrite_id.t ->
    Flow.Acc.t -> Flow.Acc.t coq_M **)

let update_data_flow dacc closure_info0 lifted_constants_from_defining_expr0
    simplify_named_result rewrite_id0 data_flow =
  let data_flow0 =
    match Closure_info.in_or_out_of_closure closure_info0 with
    | Closure_info.In_a_closure -> data_flow
    | Closure_info.Not_in_a_closure ->
      Flow.Acc.record_lifted_constants lifted_constants_from_defining_expr0
        data_flow
  in
  ListLabels.fold_left
    (record_new_defining_expression_binding_for_data_flow dacc rewrite_id0)
    data_flow0
    (Simplify_named_result.bindings_to_place simplify_named_result)

(** val simplify_let0 : Flambda.Expr.t Simplify_common.expr_simplifier ->
    Simplify_common.simplify_function_body -> Downwards_acc.t -> Flambda.Let.t
    -> Simplified_expr.t Simplify_common.down_to_up -> Bound_pattern.t ->
    Flambda.Expr.t -> (Simplified_expr.t * Downwards_acc.t) coq_M **)

let simplify_let0 simplify_expr simplify_function_body dacc let_expr down_to_up0
    bound_pattern body =
  let original_dacc = dacc in
  let dacc0, prior_lifted_constants =
    Downwards_acc.get_and_clear_lifted_constants dacc
  in
  let defining_expr = Flambda.Let.defining_expr let_expr in
  match
    Simplify_named.simplify_named dacc0 bound_pattern defining_expr
      simplify_function_body
  with
  | Simplified_named.Simplified p -> (
    let simplify_named_result, removed_operations0 = p in
    match simplify_named_result with
    | Or_invalid.Ok simplify_named_result0 ->
      let dacc1 = Simplify_named_result.dacc simplify_named_result0 in
      let closure_info0 =
        Downwards_env.closure_info (Downwards_acc.denv dacc1)
      in
      let lifted_constants_from_defining_expr0 =
        Downwards_acc.get_lifted_constants dacc1
      in
      let dacc2 =
        (fun x__1 x__2 x__3 ->
          Downwards_acc.add_to_lifted_constant_accumulator ?also_add_to_env:x__1
            x__2 x__3)
          None dacc1 prior_lifted_constants
      in
      let rewrite_id0 = Named_rewrite_id.create () in
      let dacc3 =
        Downwards_acc.map_flow_acc dacc2 (fun data_flow ->
            update_data_flow dacc2 closure_info0
              lifted_constants_from_defining_expr0 simplify_named_result0
              rewrite_id0 data_flow)
      in
      let at_unit_toplevel0 =
        Downwards_env.at_unit_toplevel (Downwards_acc.denv dacc3)
      in
      let down_to_up1 =
       fun dacc4 simplified_body ->
        down_to_up0 dacc4
          (Simplified_expr.simplified_let
             (Simplify_named_result.bindings_to_place simplify_named_result0)
             removed_operations0 lifted_constants_from_defining_expr0
             at_unit_toplevel0 closure_info0 rewrite_id0 simplified_body)
      in
      simplify_expr dacc3 body down_to_up1
    | Or_invalid.Invalid ->
      down_to_up0 original_dacc
        (Simplified_expr.notify_removed removed_operations0
           (Simplified_expr.simplified_invalid
              (Flambda.Invalid.Defining_expr_of_let
                 (bound_pattern, defining_expr)))))
  | Simplified_named.Rewritten f -> simplify_expr dacc0 (f body) down_to_up0

(** val simplify_let : Flambda.Expr.t Simplify_common.expr_simplifier ->
    Simplify_common.simplify_function_body -> Downwards_acc.t -> Flambda.Let.t
    -> Simplified_expr.t Simplify_common.down_to_up -> (Simplified_expr.t *
    Downwards_acc.t) coq_M **)

let simplify_let simplify_expr simplify_function_body dacc let_expr down_to_up0
    =
  Flambda.Let.pattern_match let_expr (fun bound_pattern body ->
      simplify_let0 simplify_expr simplify_function_body dacc let_expr
        down_to_up0 bound_pattern body)
