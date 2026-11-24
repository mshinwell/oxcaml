(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Simplify_primitive.v, which follows
   middle_end/flambda2/simplify/simplify_primitive.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Simplify_import
open Port_monad

type cse_result =
  | Applied of Simplify_primitive_result.t
  | Not_applied of Downwards_acc.t

(** val apply_cse : Downwards_acc.t -> Flambda_primitive.t -> Simple.t option
    coq_M **)

let apply_cse dacc original_prim =
  match Flambda_primitive.Eligible_for_cse.create original_prim with
  | Some with_fixed_value -> (
    match Downwards_env.find_cse (Downwards_acc.denv dacc) with_fixed_value with
    | Some simple ->
      Port_monad.match_exn
        (fun _ ->
          (fun x__1 x__2 x__3 x__4 ->
            Flambda2_types.Typing_env.get_canonical_simple_exn x__1
              ?min_name_mode:x__2 ?name_mode_of_existing_simple:x__3 x__4)
            (Downwards_acc.typing_env dacc)
            (Some Name_mode.normal) (Some Name_mode.normal) simple)
        Port_monad.not_found
        (fun _ ->
          Misc.fatal_errorf "No canonical simple for the CSE candidate: %a"
            Simple.print simple)
        (fun canonical -> Some canonical)
    | None -> None)
  | None -> None

(** val try_cse : Downwards_acc.t -> Debuginfo.t -> Flambda_primitive.t ->
    Name_mode.t -> Bound_var.t -> cse_result coq_M **)

let try_cse dacc dbg original_prim min_name_mode result_var =
  if not (Name_mode.equal min_name_mode Name_mode.normal)
  then Not_applied dacc
  else
    let result_var' = Bound_var.var result_var in
    match apply_cse dacc original_prim with
    | Some replace_with ->
      let dacc0 = Downwards_acc.merge_debuginfo_rewrite dacc replace_with dbg in
      let named = Flambda.Named.create_simple replace_with in
      let ty =
        Flambda2_types.alias_type_of
          (Flambda_primitive.result_kind' original_prim)
          replace_with
      in
      let dacc1 = Downwards_acc.add_variable dacc0 result_var ty in
      let result =
        let cost_metrics =
          Cost_metrics.notify_removed
            (Removed_operations.prim original_prim)
            Cost_metrics.zero
        in
        let machine_width =
          Downwards_env.machine_width (Downwards_acc.denv dacc1)
        in
        let simplified_named =
          Simplified_named.update_cost_metrics cost_metrics
            (Simplified_named.create machine_width named)
        in
        Simplify_primitive_result.create_simplified simplified_named true dacc1
      in
      Applied result
    | None ->
      let dacc0 =
        match Flambda_primitive.Eligible_for_cse.create original_prim with
        | Some eligible_prim ->
          let bound_to = Simple.var result_var' in
          let dacc0 =
            Downwards_acc.map_denv dacc (fun denv ->
                Downwards_env.add_cse denv eligible_prim bound_to min_name_mode)
          in
          Downwards_acc.merge_debuginfo_rewrite dacc0 bound_to dbg
        | None -> dacc
      in
      Not_applied dacc0

(** val arg_kind_mismatch : Flambda_primitive.t -> (Flambda2_types.t *
    Flambda_kind.t) list -> bool coq_M **)

let arg_kind_mismatch prim arg_tys_with_expected_kinds =
  let found_mismatch = ref false in
  let () =
    List.iter
      (fun pat ->
        let arg_ty, expected_kind = pat in
        let arg_kind = Flambda2_types.kind arg_ty in
        if not (Flambda_kind.equal arg_kind expected_kind)
        then
          if Flambda_features.kind_checks ()
          then
            Misc.fatal_errorf
              "Argument type %a has wrong kind (%a), expected kind %a for \
               primitive: %a"
              Flambda2_types.print arg_ty Flambda_kind.print arg_kind
              Flambda_kind.print expected_kind Flambda_primitive.print prim
          else found_mismatch := true
        else ())
      arg_tys_with_expected_kinds
  in
  !found_mismatch

(** val simplify_primitive : Downwards_acc.t -> Flambda_primitive.t ->
    Debuginfo.t -> Bound_var.t -> Simplify_primitive_result.t coq_M **)

let simplify_primitive dacc prim dbg result_var =
  let min_name_mode = Bound_var.name_mode result_var in
  match prim with
  | Flambda_primitive.Nullary prim' ->
    Simplify_nullary_primitive.simplify_nullary_primitive dacc prim prim' dbg
      result_var
  | Flambda_primitive.Unary (unary_prim, orig_arg) -> (
    let arg_ty, arg =
      Simplify_simple.simplify_simple dacc orig_arg min_name_mode
    in
    let arg_kind = Flambda_primitive.arg_kind_of_unary_primitive unary_prim in
    if arg_kind_mismatch prim ((arg_ty, arg_kind) :: [])
    then Simplify_primitive_result.create_invalid dacc
    else
      let original_prim =
        if orig_arg == arg
        then prim
        else Flambda_primitive.Unary (unary_prim, arg)
      in
      match try_cse dacc dbg original_prim min_name_mode result_var with
      | Applied result -> result
      | Not_applied dacc0 ->
        Simplify_unary_primitive.simplify_unary_primitive dacc0 original_prim
          unary_prim arg arg_ty dbg result_var)
  | Flambda_primitive.Binary (binary_prim, orig_arg1, orig_arg2) -> (
    let arg1_ty, arg1 =
      Simplify_simple.simplify_simple dacc orig_arg1 min_name_mode
    in
    let arg2_ty, arg2 =
      Simplify_simple.simplify_simple dacc orig_arg2 min_name_mode
    in
    let arg1_kind, arg2_kind =
      Flambda_primitive.args_kind_of_binary_primitive binary_prim
    in
    if arg_kind_mismatch prim [arg1_ty, arg1_kind; arg2_ty, arg2_kind]
    then Simplify_primitive_result.create_invalid dacc
    else
      let original_prim =
        if orig_arg1 == arg1 && orig_arg2 == arg2
        then prim
        else Flambda_primitive.Binary (binary_prim, arg1, arg2)
      in
      match try_cse dacc dbg original_prim min_name_mode result_var with
      | Applied result -> result
      | Not_applied dacc0 ->
        Simplify_binary_primitive.simplify_binary_primitive dacc0 original_prim
          binary_prim arg1 arg1_ty arg2 arg2_ty dbg result_var)
  | Flambda_primitive.Ternary (ternary_prim, orig_arg1, orig_arg2, orig_arg3)
    -> (
    let arg1_ty, arg1 =
      Simplify_simple.simplify_simple dacc orig_arg1 min_name_mode
    in
    let arg2_ty, arg2 =
      Simplify_simple.simplify_simple dacc orig_arg2 min_name_mode
    in
    let arg3_ty, arg3 =
      Simplify_simple.simplify_simple dacc orig_arg3 min_name_mode
    in
    let arg1_kind, arg2_kind, arg3_kind =
      Flambda_primitive.args_kind_of_ternary_primitive ternary_prim
    in
    if
      arg_kind_mismatch prim
        [arg1_ty, arg1_kind; arg2_ty, arg2_kind; arg3_ty, arg3_kind]
    then Simplify_primitive_result.create_invalid dacc
    else
      let original_prim =
        if orig_arg1 == arg1 && orig_arg2 == arg2 && orig_arg3 == arg3
        then prim
        else Flambda_primitive.Ternary (ternary_prim, arg1, arg2, arg3)
      in
      match try_cse dacc dbg original_prim min_name_mode result_var with
      | Applied result -> result
      | Not_applied dacc0 ->
        Simplify_ternary_primitive.simplify_ternary_primitive dacc0
          original_prim ternary_prim arg1 arg1_ty arg2 arg2_ty arg3 arg3_ty dbg
          result_var)
  | Flambda_primitive.Quaternary
      (quaternary_prim, orig_arg1, orig_arg2, orig_arg3, orig_arg4) -> (
    let arg1_ty, arg1 =
      Simplify_simple.simplify_simple dacc orig_arg1 min_name_mode
    in
    let arg2_ty, arg2 =
      Simplify_simple.simplify_simple dacc orig_arg2 min_name_mode
    in
    let arg3_ty, arg3 =
      Simplify_simple.simplify_simple dacc orig_arg3 min_name_mode
    in
    let arg4_ty, arg4 =
      Simplify_simple.simplify_simple dacc orig_arg4 min_name_mode
    in
    let arg1_kind, arg2_kind, arg3_kind, arg4_kind =
      Flambda_primitive.args_kind_of_quaternary_primitive quaternary_prim
    in
    if
      arg_kind_mismatch prim
        [ arg1_ty, arg1_kind;
          arg2_ty, arg2_kind;
          arg3_ty, arg3_kind;
          arg4_ty, arg4_kind ]
    then Simplify_primitive_result.create_invalid dacc
    else
      let original_prim =
        if
          orig_arg1 == arg1 && orig_arg2 == arg2 && orig_arg3 == arg3
          && orig_arg4 == arg4
        then prim
        else
          Flambda_primitive.Quaternary (quaternary_prim, arg1, arg2, arg3, arg4)
      in
      match try_cse dacc dbg original_prim min_name_mode result_var with
      | Applied result -> result
      | Not_applied dacc0 ->
        Simplify_quaternary_primitive.simplify_quaternary_primitive dacc0
          original_prim quaternary_prim arg1 arg1_ty arg2 arg2_ty arg3 arg3_ty
          arg4 arg4_ty dbg result_var)
  | Flambda_primitive.Variadic (variadic_prim, orig_args) -> (
    let args_with_tys =
      ListLabels.fold_right
        (fun arg args_rev ->
          let arg_ty, arg0 =
            Simplify_simple.simplify_simple dacc arg min_name_mode
          in
          (arg0, arg_ty) :: args_rev)
        orig_args []
    in
    let arg_tys = List.map snd args_with_tys in
    let arg_tys_and_expected_kinds =
      match Flambda_primitive.args_kind_of_variadic_primitive variadic_prim with
      | Flambda_primitive.Variadic_mixed arg_kinds ->
        List.combine arg_tys
          (Array.to_list (Flambda_kind.Mixed_block_shape.field_kinds arg_kinds))
      | Flambda_primitive.Variadic_all_of_kind kind ->
        List.map (fun arg_ty -> arg_ty, kind) arg_tys
      | Flambda_primitive.Variadic_zero_or_one kind ->
        let () =
          match arg_tys with
          | [] -> ()
          | _ :: l -> (
            match l with
            | [] -> ()
            | _ :: _ ->
              Misc.fatal_errorf "Too many arguments for primitive %a"
                Flambda_primitive.print prim)
        in
        List.map (fun arg_ty -> arg_ty, kind) arg_tys
      | Flambda_primitive.Variadic_unboxed_product kinds ->
        let num_arg_tys = List.length arg_tys in
        let num_kinds = List.length kinds in
        let () =
          if num_arg_tys mod num_kinds <> 0
          then
            Misc.fatal_errorf
              "Number of arguments %d is not a multiple of the number of kinds \
               %d for:@ %a"
              num_arg_tys num_kinds Flambda_primitive.print prim
          else ()
        in
        let num_repeats = num_arg_tys / num_kinds in
        let kinds0 = List.concat (List.init num_repeats (fun _ -> kinds)) in
        List.combine arg_tys kinds0
    in
    if arg_kind_mismatch prim arg_tys_and_expected_kinds
    then Simplify_primitive_result.create_invalid dacc
    else
      let original_prim =
        Flambda_primitive.Variadic (variadic_prim, List.map fst args_with_tys)
      in
      match try_cse dacc dbg original_prim min_name_mode result_var with
      | Applied result -> result
      | Not_applied dacc0 ->
        Simplify_variadic_primitive.simplify_variadic_primitive dacc0
          original_prim variadic_prim args_with_tys dbg result_var)
