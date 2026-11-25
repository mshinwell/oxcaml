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

(* This file follows middle_end/flambda2/simplify/simplify_primitive.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Array Bound_var Cost_metrics Debuginfo
  Flambda_features List ListLabels Name_mode Removed_operations Simple
  Simplified_named Simplify_binary_primitive Simplify_nullary_primitive
  Simplify_primitive_result Simplify_quaternary_primitive
  Simplify_ternary_primitive Simplify_unary_primitive
  Simplify_variadic_primitive Stdlib_.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda_primitive.arg_kinds *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
(*OCAML
open! Simplify_import
OCAML*)

(* 19-21 *)
Inductive cse_result : Type :=
| Applied : Simplify_primitive_result.t -> cse_result
| Not_applied : DA.t -> cse_result.

(* 23-37 *)
Definition apply_cse (dacc : DA.t) (original_prim : P.t)
    : M (option Simple.t) :=
  let! tmp1 := P.Eligible_for_cse.create original_prim in
  match tmp1 with
  | None => ret None
  | Some with_fixed_value =>
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.find_cse tmp1 with_fixed_value in
    match tmp2 with
    | None => ret None
    | Some simple =>
      (* 30-37. [TE.get_canonical_simple_exn env simple ~min_name_mode
         ~name_mode_of_existing_simple]: the arguments are in the order of
         the interface. *)
      match_exn
        (fun _ =>
          let! tmp1 := DA.typing_env dacc in
          TE.get_canonical_simple_exn tmp1 (Some NM.normal) (Some NM.normal)
            simple)
        Not_found
        (fun _ =>
          fatal_errorf2 "No canonical simple for the CSE candidate: %a"
            Simple.print simple)
        (fun canonical => ret (Some canonical))
    end
  end.

(* 39-80 *)
Definition try_cse (dacc : DA.t) (dbg : Debuginfo.t) (original_prim : P.t)
    (min_name_mode : Name_mode.t) (result_var : Bound_var.t)
    : M cse_result :=
  let! tmp1 := Name_mode.equal min_name_mode Name_mode.normal in
  if negb tmp1
  then ret (Not_applied dacc)
  else
    let* result_var' := VB.var result_var in
    let! tmp1 := apply_cse dacc original_prim in
    match tmp1 with
    | Some replace_with =>
      (* 49-66 *)
      let* dacc := DA.merge_debuginfo_rewrite dacc replace_with dbg in
      let* named := Named.create_simple replace_with in
      let* ty :=
        let! tmp1 := P.result_kind' original_prim in
        T.alias_type_of tmp1 replace_with
      in
      let* dacc := DA.add_variable dacc result_var ty in
      let* result :=
        let* cost_metrics :=
          let! tmp1 := Removed_operations.prim original_prim in
          Cost_metrics.notify_removed tmp1 Cost_metrics.zero
        in
        let* machine_width :=
          let! tmp1 := DA.denv dacc in
          DE.machine_width tmp1
        in
        (* 60-61: [a |> f b] is [f b a] *)
        let* simplified_named :=
          let! tmp1 := Simplified_named.create machine_width named in
          Simplified_named.update_cost_metrics cost_metrics tmp1
        in
        Simplify_primitive_result.create_simplified simplified_named true
          dacc
      in
      ret (Applied result)
    | None =>
      (* 68-80 *)
      let* dacc :=
        let! tmp1 := P.Eligible_for_cse.create original_prim in
        match tmp1 with
        | None => ret dacc
        | Some eligible_prim =>
          let* bound_to := Simple.var result_var' in
          let* dacc :=
            DA.map_denv dacc
              (fun denv =>
                DE.add_cse denv eligible_prim bound_to min_name_mode)
          in
          DA.merge_debuginfo_rewrite dacc bound_to dbg
        end
      in
      ret (Not_applied dacc)
    end.

(* 82-98 *)
Definition arg_kind_mismatch (prim : P.t)
    (arg_tys_with_expected_kinds : list (T.t * K.t)) : M bool :=
  let* found_mismatch := mk_ref false in
  List.iter
    (fun '(arg_ty, expected_kind) =>
      let* arg_kind := T.kind arg_ty in
      let! tmp1 := K.equal arg_kind expected_kind in
      if negb tmp1
      then
        let! tmp1 := Flambda_features.kind_checks tt in
        if tmp1
        then
          fatal_errorf8
            "Argument type %a has wrong kind (%a), expected kind %a for primitive: %a"
            T.print arg_ty K.print arg_kind K.print expected_kind P.print
            prim
        else set found_mismatch true
      else ret tt)
    arg_tys_with_expected_kinds ;;
  get found_mismatch.

(* 100-235 *)
Definition simplify_primitive (dacc : DA.t) (prim : P.t) (dbg : Debuginfo.t)
    (result_var : Bound_var.t) : M Simplify_primitive_result.t :=
  let* min_name_mode := Bound_var.name_mode result_var in
  match prim with
  | P.Nullary prim' =>
    Simplify_nullary_primitive.simplify_nullary_primitive dacc prim prim' dbg
      result_var
  | P.Unary unary_prim orig_arg =>
    (* 106-120 *)
    let* '(arg_ty, arg) := S.simplify_simple dacc orig_arg min_name_mode in
    let* arg_kind := P.arg_kind_of_unary_primitive unary_prim in
    let! tmp1 := arg_kind_mismatch prim [(arg_ty, arg_kind)] in
    if tmp1
    then SPR.create_invalid dacc
    else
      let* original_prim :=
        let! tmp1 := phys_equal orig_arg arg in
        if tmp1 then ret prim else ret (P.Unary unary_prim arg)
      in
      let! tmp1 := try_cse dacc dbg original_prim min_name_mode result_var in
      match tmp1 with
      | Applied result => ret result
      | Not_applied dacc =>
        Simplify_unary_primitive.simplify_unary_primitive dacc original_prim
          unary_prim arg arg_ty dbg result_var
      end
  | P.Binary binary_prim orig_arg1 orig_arg2 =>
    (* 121-138 *)
    let* '(arg1_ty, arg1) := S.simplify_simple dacc orig_arg1 min_name_mode in
    let* '(arg2_ty, arg2) := S.simplify_simple dacc orig_arg2 min_name_mode in
    let* '(arg1_kind, arg2_kind) :=
      P.args_kind_of_binary_primitive binary_prim
    in
    let! tmp1 :=
      arg_kind_mismatch prim [(arg1_ty, arg1_kind); (arg2_ty, arg2_kind)]
    in
    if tmp1
    then SPR.create_invalid dacc
    else
      let* original_prim :=
        let! tmp1 := phys_equal orig_arg1 arg1 in
        let! tmp2 := and_then tmp1 (phys_equal orig_arg2 arg2) in
        if tmp2 then ret prim else ret (P.Binary binary_prim arg1 arg2)
      in
      let! tmp1 := try_cse dacc dbg original_prim min_name_mode result_var in
      match tmp1 with
      | Applied result => ret result
      | Not_applied dacc =>
        Simplify_binary_primitive.simplify_binary_primitive dacc original_prim
          binary_prim arg1 arg1_ty arg2 arg2_ty dbg result_var
      end
  | P.Ternary ternary_prim orig_arg1 orig_arg2 orig_arg3 =>
    (* 139-162 *)
    let* '(arg1_ty, arg1) := S.simplify_simple dacc orig_arg1 min_name_mode in
    let* '(arg2_ty, arg2) := S.simplify_simple dacc orig_arg2 min_name_mode in
    let* '(arg3_ty, arg3) := S.simplify_simple dacc orig_arg3 min_name_mode in
    let* '(T3 arg1_kind arg2_kind arg3_kind) :=
      P.args_kind_of_ternary_primitive ternary_prim
    in
    let! tmp1 :=
      arg_kind_mismatch prim
        [(arg1_ty, arg1_kind); (arg2_ty, arg2_kind); (arg3_ty, arg3_kind)]
    in
    if tmp1
    then SPR.create_invalid dacc
    else
      let* original_prim :=
        let! tmp1 := phys_equal orig_arg1 arg1 in
        let! tmp2 :=
          and_then tmp1
            (let! tmp3 := phys_equal orig_arg2 arg2 in
             and_then tmp3 (phys_equal orig_arg3 arg3))
        in
        if tmp2
        then ret prim
        else ret (P.Ternary ternary_prim arg1 arg2 arg3)
      in
      let! tmp1 := try_cse dacc dbg original_prim min_name_mode result_var in
      match tmp1 with
      | Applied result => ret result
      | Not_applied dacc =>
        Simplify_ternary_primitive.simplify_ternary_primitive dacc
          original_prim ternary_prim arg1 arg1_ty arg2 arg2_ty arg3 arg3_ty
          dbg result_var
      end
  | P.Quaternary quaternary_prim orig_arg1 orig_arg2 orig_arg3 orig_arg4 =>
    (* 163-193 *)
    let* '(arg1_ty, arg1) := S.simplify_simple dacc orig_arg1 min_name_mode in
    let* '(arg2_ty, arg2) := S.simplify_simple dacc orig_arg2 min_name_mode in
    let* '(arg3_ty, arg3) := S.simplify_simple dacc orig_arg3 min_name_mode in
    let* '(arg4_ty, arg4) := S.simplify_simple dacc orig_arg4 min_name_mode in
    let* '(T4 arg1_kind arg2_kind arg3_kind arg4_kind) :=
      P.args_kind_of_quaternary_primitive quaternary_prim
    in
    let! tmp1 :=
      arg_kind_mismatch prim
        [(arg1_ty, arg1_kind); (arg2_ty, arg2_kind); (arg3_ty, arg3_kind);
         (arg4_ty, arg4_kind)]
    in
    if tmp1
    then SPR.create_invalid dacc
    else
      let* original_prim :=
        let! tmp1 := phys_equal orig_arg1 arg1 in
        let! tmp2 :=
          and_then tmp1
            (let! tmp3 := phys_equal orig_arg2 arg2 in
             and_then tmp3
               (let! tmp4 := phys_equal orig_arg3 arg3 in
                and_then tmp4 (phys_equal orig_arg4 arg4)))
        in
        if tmp2
        then ret prim
        else ret (P.Quaternary quaternary_prim arg1 arg2 arg3 arg4)
      in
      let! tmp1 := try_cse dacc dbg original_prim min_name_mode result_var in
      match tmp1 with
      | Applied result => ret result
      | Not_applied dacc =>
        Simplify_quaternary_primitive.simplify_quaternary_primitive dacc
          original_prim quaternary_prim arg1 arg1_ty arg2 arg2_ty arg3 arg3_ty
          arg4 arg4_ty dbg result_var
      end
  | P.Variadic variadic_prim orig_args =>
    (* 194-199. [ListLabels.fold_right orig_args ~init:[] ~f]: the arguments
       are in the order of the interface. *)
    let* args_with_tys :=
      ListLabels.fold_right
        (fun (arg : Simple.t) (args_rev : list (Simple.t * T.t)) =>
          let* '(arg_ty, arg) := S.simplify_simple dacc arg min_name_mode in
          ret ((arg, arg_ty) :: args_rev))
        orig_args []
    in
    let* arg_tys := List.map Stdlib_.snd args_with_tys in
    (* 201-224 *)
    let* arg_tys_and_expected_kinds :=
      let! tmp1 := P.args_kind_of_variadic_primitive variadic_prim in
      match tmp1 with
      | P.Variadic_mixed arg_kinds =>
        let! tmp1 := K.Mixed_block_shape.field_kinds arg_kinds in
        let! tmp2 := Array.to_list tmp1 in
        List.combine arg_tys tmp2
      | P.Variadic_all_of_kind kind =>
        List.map (fun arg_ty => ret (arg_ty, kind)) arg_tys
      | P.Variadic_zero_or_one kind =>
        match arg_tys with
        | [] | [_] => ret tt
        | _ :: _ :: _ =>
          fatal_errorf2 "Too many arguments for primitive %a" P.print prim
        end ;;
        List.map (fun arg_ty => ret (arg_ty, kind)) arg_tys
      | P.Variadic_unboxed_product kinds =>
        let* num_arg_tys := List.length arg_tys in
        let* num_kinds := List.length kinds in
        (let! tmp1 := int_mod num_arg_tys num_kinds in
         if tmp1 <>? 0
         then
           fatal_errorf4
             "Number of arguments %d is not a multiple of the number of kinds %d for:@ %a"
             num_arg_tys num_kinds P.print prim
         else ret tt) ;;
        let* num_repeats := int_div num_arg_tys num_kinds in
        (* 223: [a |> f] is [f a] *)
        let* kinds :=
          let! tmp1 := List.init num_repeats (fun _ => ret kinds) in
          List.concat tmp1
        in
        List.combine arg_tys kinds
      end
    in
    (* 226-235 *)
    let! tmp1 := arg_kind_mismatch prim arg_tys_and_expected_kinds in
    if tmp1
    then SPR.create_invalid dacc
    else
      let* original_prim :=
        let! tmp1 := List.map Stdlib_.fst args_with_tys in
        ret (P.Variadic variadic_prim tmp1)
      in
      let! tmp1 := try_cse dacc dbg original_prim min_name_mode result_var in
      match tmp1 with
      | Applied result => ret result
      | Not_applied dacc =>
        Simplify_variadic_primitive.simplify_variadic_primitive dacc
          original_prim variadic_prim args_with_tys dbg result_var
      end
  end.
