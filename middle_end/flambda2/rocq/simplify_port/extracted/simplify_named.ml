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
   middle_end/flambda2/rocq/simplify_port/Simplify_named.v, which follows
   middle_end/flambda2/simplify/simplify_named.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Simplify_import
open Port_monad

(** val create_lifted_constant : (DA.t * LC.t list) -> Bound_static.Pattern.t ->
    Rebuilt_static_const.t -> (DA.t * LC.t list) coq_M **)

let create_lifted_constant acc pat static_const =
  let dacc0, lifted_constants = acc in
  match pat with
  | Bound_static.Pattern.Code code_id ->
    let lifted_constant = LC.create_code code_id static_const in
    dacc0, lifted_constant :: lifted_constants
  | Bound_static.Pattern.Set_of_closures closure_symbols ->
    let closure_symbols_with_types =
      Function_slot.Lmap.map
        (fun symbol ->
          let typ =
            TE.find (DA.typing_env dacc0) (Name.symbol symbol) (Some K.value)
          in
          symbol, typ)
        closure_symbols
    in
    let lifted_constant =
      LC.create_set_of_closures (DA.typing_env dacc0) closure_symbols_with_types
        Variable.Map.empty static_const
    in
    dacc0, lifted_constant :: lifted_constants
  | Bound_static.Pattern.Block_like symbol ->
    let typ =
      TE.find (DA.typing_env dacc0) (Name.symbol symbol) (Some K.value)
    in
    let lifted_constant =
      LC.create_block_like symbol Variable.Map.empty static_const
        (DA.typing_env dacc0) typ
    in
    let dacc1 =
      match Rebuilt_static_const.to_const static_const with
      | Some t -> (
        match t with
        | Code _ -> dacc0
        | Deleted_code -> dacc0
        | Static_const static_const0 ->
          DA.consider_constant_for_sharing dacc0 symbol static_const0)
      | None -> dacc0
    in
    dacc1, lifted_constant :: lifted_constants

(** val simplify_named0 : DA.t -> Bound_pattern.t -> Named.t ->
    Simplify_common.simplify_function_body -> Simplify_named_result.t
    Or_invalid.t Simplified_named.or_rewritten coq_M **)

let simplify_named0 dacc0 bound_pattern named0 simplify_function_body =
  let ok = fun result -> Simplified_named.Simplified (Or_invalid.Ok result) in
  let invalid = Simplified_named.Simplified Or_invalid.Invalid in
  let machine_width = DE.machine_width (DA.denv dacc0) in
  match named0 with
  | Flambda.Simple simple ->
    let bound_var = Bound_pattern.must_be_singleton bound_pattern in
    let min_name_mode = Bound_var.name_mode bound_var in
    let ty, new_simple = S.simplify_simple dacc0 simple min_name_mode in
    let dacc1 = DA.add_variable dacc0 bound_var ty in
    let defining_expr =
      if simple == new_simple
      then Simplified_named.create machine_width named0
      else
        Simplified_named.create machine_width (Named.create_simple new_simple)
    in
    ok
      (Simplify_named_result.create dacc1
         ((fun (x__1, x__2, x__3) ->
            (Simplified_named.Keep_binding
               { let_bound = x__1;
                 simplified_defining_expr = x__2;
                 original_defining_expr = x__3
               }
              : Simplified_named.binding_to_place))
            (bound_pattern, defining_expr, Some named0)))
  | Flambda.Prim (prim, dbg) -> (
    if not (Name_mode.is_normal (Bound_pattern.name_mode bound_pattern))
    then
      let min_name_mode = Bound_pattern.name_mode bound_pattern in
      let defining_expr =
        Named.create_prim
          (P.map_args
             (fun simple -> snd (S.simplify_simple dacc0 simple min_name_mode))
             prim)
          dbg
      in
      let bound_var = Bound_pattern.must_be_singleton bound_pattern in
      let dacc1 =
        DA.map_denv dacc0 (fun denv ->
            DE.define_variable denv bound_var (P.result_kind' prim))
      in
      ok
        (Simplify_named_result.create dacc1
           ((fun (x__1, x__2, x__3) ->
              (Simplified_named.Keep_binding
                 { let_bound = x__1;
                   simplified_defining_expr = x__2;
                   original_defining_expr = x__3
                 }
                : Simplified_named.binding_to_place))
              ( bound_pattern,
                Simplified_named.create machine_width defining_expr,
                Some named0 )))
    else
      let bound_var = Bound_pattern.must_be_singleton bound_pattern in
      let dacc1 =
        DA.map_denv dacc0
          (DE.map_specialization_cost
             (Specialization_cost.add_prim bound_var prim))
      in
      let dbg0 = DE.add_inlined_debuginfo (DA.denv dacc1) dbg in
      match Simplify_primitive.simplify_primitive dacc1 prim dbg0 bound_var with
      | Simplified_named.Simplified t -> (
        let { Simplify_primitive_result.simplified_named = simplified_named0;
              Simplify_primitive_result.try_reify = try_reify0;
              Simplify_primitive_result.dacc = dacc2
            } =
          t
        in
        match simplified_named0 with
        | Or_invalid.Ok simplified_named1 ->
          let () =
            if
              Flambda_features.check_invariants ()
              && not
                   ((fun x__1 x__2 x__3 -> TE.mem ?min_name_mode:x__1 x__2 x__3)
                      None (DA.typing_env dacc2)
                      (Name.var (Bound_var.var bound_var)))
            then
              Misc.fatal_errorf "Primitive %a = %a did not yield a result var"
                Bound_var.print bound_var P.print prim
            else ()
          in
          if not try_reify0
          then
            ok
              (Simplify_named_result.create dacc2
                 ((fun (x__1, x__2, x__3) ->
                    (Simplified_named.Keep_binding
                       { let_bound = x__1;
                         simplified_defining_expr = x__2;
                         original_defining_expr = x__3
                       }
                      : Simplified_named.binding_to_place))
                    (bound_pattern, simplified_named1, Some named0)))
          else
            let allow_lifting =
              P.only_generative_effects prim
              && Name_mode.is_normal (Bound_var.name_mode bound_var)
            in
            let defining_expr, dacc3 =
              Reification.try_to_reify dacc2 dbg0 simplified_named1 bound_var
                (P.result_kind' prim) allow_lifting
            in
            let result =
              Or_invalid.map defining_expr (fun defining_expr0 ->
                  Simplify_named_result.create dacc3
                    ((fun (x__1, x__2, x__3) ->
                       (Simplified_named.Keep_binding
                          { let_bound = x__1;
                            simplified_defining_expr = x__2;
                            original_defining_expr = x__3
                          }
                         : Simplified_named.binding_to_place))
                       (bound_pattern, defining_expr0, Some named0)))
            in
            Simplified_named.Simplified result
        | Or_invalid.Invalid -> invalid)
      | Simplified_named.Rewritten f -> Simplified_named.Rewritten f)
  | Flambda.Set_of_closures (set_of_closures, alloc_mode) ->
    ok
      (Simplify_set_of_closures.simplify_non_lifted_set_of_closures dacc0
         bound_pattern set_of_closures alloc_mode simplify_function_body)
  | Flambda.Static_consts static_consts ->
    let bound_static = Bound_pattern.must_be_static bound_pattern in
    let binds_symbols = Bound_static.binds_symbols bound_static in
    let () =
      if binds_symbols && not (DE.at_unit_toplevel (DA.denv dacc0))
      then
        Misc.fatal_errorf
          "[Let] binding symbols is only allowed at the toplevel of \
           compilation units (not even at the toplevel of function bodies):@ \
           %a@ =@ %a"
          Bound_pattern.print bound_pattern Named.print named0
      else ()
    in
    let bound_static0, static_consts0, dacc1 =
      Port_monad.try_with
        (fun _ ->
          Simplify_static_const.simplify_static_consts dacc0 bound_static
            static_consts simplify_function_body)
        Port_monad.fatal_error_exception
        (fun _ ->
          let bt = Printexc.get_raw_backtrace () in
          let () =
            Format.eprintf
              "\n\
               %tContext is:%t simplifying 'let symbol' binding of@ %a@ with \
               downwards accumulator:@ %a\n"
              Flambda_colours.error Flambda_colours.pop Bound_static.print
              bound_static DA.print dacc0
          in
          Printexc.raise_with_backtrace
            (Port_monad.exn_make Port_monad.fatal_error_exception ())
            bt)
    in
    let dacc2, lifted_constants =
      ListLabels.fold_left2 create_lifted_constant (dacc1, [])
        (Bound_static.to_list bound_static0)
        (Rebuilt_static_const.Group.to_list static_consts0)
    in
    let dacc3 =
      (fun x__1 x__2 x__3 ->
        DA.add_to_lifted_constant_accumulator ?also_add_to_env:x__1 x__2 x__3)
        None dacc2
        (LCS.singleton (LC.concat lifted_constants))
    in
    ok (Simplify_named_result.create_empty dacc3)
  | Flambda.Rec_info rec_info_expr ->
    let bound_var = Bound_pattern.must_be_singleton bound_pattern in
    let new_rec_info_expr =
      Simplify_rec_info_expr.simplify_rec_info_expr dacc0 rec_info_expr
    in
    let ty = T.this_rec_info new_rec_info_expr in
    let dacc1 = DA.add_variable dacc0 bound_var ty in
    let machine_width0 = DE.machine_width (DA.denv dacc1) in
    let defining_expr =
      if rec_info_expr == new_rec_info_expr
      then Simplified_named.create machine_width0 named0
      else
        Simplified_named.create machine_width0
          (Named.create_rec_info new_rec_info_expr)
    in
    ok
      (Simplify_named_result.create dacc1
         ((fun (x__1, x__2, x__3) ->
            (Simplified_named.Keep_binding
               { let_bound = x__1;
                 simplified_defining_expr = x__2;
                 original_defining_expr = x__3
               }
              : Simplified_named.binding_to_place))
            (bound_pattern, defining_expr, Some named0)))

(** val removed_operations : Name_mode.t -> Named.t -> DA.t ->
    Simplify_named_result.t Or_invalid.t -> Removed_operations.t coq_M **)

let removed_operations min_name_mode original dacc0 result =
  let zero = Removed_operations.zero in
  match result with
  | Or_invalid.Ok result0 -> (
    match original with
    | Flambda.Simple _ -> zero
    | Flambda.Prim (original_prim, _) ->
      if
        List.exists
          (fun binding ->
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
              (fun _ t0 _ ->
                let { Simplified_named.named = named0;
                      Simplified_named.cost_metrics = _;
                      Simplified_named.free_names = _
                    } =
                  t0
                in
                match named0 with
                | Simple _ -> false
                | Prim (rewritten_prim, _) ->
                  let c =
                    Flambda_primitive.compare_primitive_application
                      (fun original_simple rewritten_simple ->
                        let _, original_simple0 =
                          S.simplify_simple dacc0 original_simple min_name_mode
                        in
                        let _, rewritten_simple0 =
                          S.simplify_simple dacc0 rewritten_simple min_name_mode
                        in
                        Simple.compare original_simple0 rewritten_simple0)
                      original_prim rewritten_prim
                  in
                  c = 0
                | Set_of_closures (_, _) -> false
                | Rec_info _ -> false)
              (fun _ -> false)
              binding)
          (Simplify_named_result.bindings_to_place result0)
      then zero
      else Removed_operations.prim original_prim
    | Flambda.Set_of_closures (_, _) ->
      if
        Simplify_named_result.was_lifted_set_of_closures result0
        || Simplify_named_result.no_bindings result0
      then Removed_operations.alloc
      else zero
    | Flambda.Static_consts _ -> zero
    | Flambda.Rec_info _ -> zero)
  | Or_invalid.Invalid -> zero

(** val simplify_named : DA.t -> Bound_pattern.t -> Named.t ->
    Simplify_common.simplify_function_body -> (Simplify_named_result.t
    Or_invalid.t * Removed_operations.t) Simplified_named.or_rewritten coq_M **)

let simplify_named dacc0 bound_pattern named0 simplify_function_body =
  Port_monad.match_exn
    (fun _ -> simplify_named0 dacc0 bound_pattern named0 simplify_function_body)
    Port_monad.fatal_error_exception
    (fun _ ->
      let bt = Printexc.get_raw_backtrace () in
      let () =
        Format.eprintf
          "\n\
           %tContext is:%t simplifying [Let] binding@ %a =@ %a@ with downwards \
           accumulator:@ %a\n"
          Flambda_colours.error Flambda_colours.pop Bound_pattern.print
          bound_pattern Named.print named0 DA.print dacc0
      in
      Printexc.raise_with_backtrace
        (Port_monad.exn_make Port_monad.fatal_error_exception ())
        bt)
    (fun x ->
      match x with
      | Simplified_named.Simplified result ->
        let min_name_mode = Bound_pattern.name_mode bound_pattern in
        Simplified_named.Simplified
          (result, removed_operations min_name_mode named0 dacc0 result)
      | Simplified_named.Rewritten f -> Simplified_named.Rewritten f)
