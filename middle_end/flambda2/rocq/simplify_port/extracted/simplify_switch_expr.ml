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
   middle_end/flambda2/rocq/simplify_port/Simplify_switch_expr.v, which follows
   middle_end/flambda2/simplify/simplify_switch_expr.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Simplify_import

exception Argument_cannot_be_used_in_lookup_table

open Expr_builder
open Flambda2_types
open Port_monad
open Reg_width_const
open Simplify_common
open Simplify_import
open Static_const
open Target_ocaml_int
module TE = Typing_env
module TI = Target_ocaml_int
module Alias_set = TE.Alias_set
module RWC = Reg_width_const

type alias_set =
  | Aliases of Flambda2_types.Typing_env.Alias_set.t
  | Poison of Flambda_kind.t

type mergeable_arms =
  | No_arms
  | Mergeable of
      { cont : Continuation.t;
        args : alias_set TI.Map.t list
      }
  | Not_mergeable

(** val inter_alias_set : alias_set -> alias_set -> alias_set coq_M **)

let inter_alias_set alias1 alias2 =
  match alias1 with
  | Aliases alias -> (
    match alias2 with
    | Aliases alias3 ->
      Aliases (Flambda2_types.Typing_env.Alias_set.inter alias alias3)
    | Poison _ -> Aliases alias)
  | Poison kind1 -> (
    match alias2 with
    | Aliases alias -> Aliases alias
    | Poison kind2 ->
      if Flambda_kind.equal kind1 kind2
      then Poison kind1
      else
        Misc.fatal_errorf
          "[inter_alias_set]: intersection of poison with different kinds %a \
           and %a"
          Flambda_kind.print kind1 Flambda_kind.print kind2)

(** val find_all_aliases : Flambda2_types.Typing_env.t -> Simple.t -> alias_set
    coq_M **)

let find_all_aliases env arg =
  let find_all_aliases0 =
   fun _ ->
    Aliases
      (Flambda2_types.Typing_env.aliases_of_simple env Name_mode.normal arg)
  in
  Simple.pattern_match' arg
    (fun _ _ -> Aliases (Flambda2_types.Typing_env.Alias_set.singleton arg))
    (fun _ _ -> find_all_aliases0 ())
    (fun cst ->
      match Reg_width_const.is_poison cst with
      | Some p ->
        let kind, _ = p in
        Poison kind
      | None -> find_all_aliases0 ())

(** val rebuild_arm : Upwards_acc.t -> Target_ocaml_int.t -> (Apply_cont_expr.t,
    Branch_annotations.t, Apply_cont_rewrite_id.t, [ `Unarized ]
    Flambda_arity.t, Flambda2_types.Typing_env.t) Port_monad.tuple5 ->
    (EB.new_let_cont list, Switch_arm.t TI.Map.t, mergeable_arms)
    Port_monad.tuple3 -> (EB.new_let_cont list, Switch_arm.t TI.Map.t,
    mergeable_arms) Port_monad.tuple3 coq_M **)

let rebuild_arm uacc arm pat pat0 =
  (fun x__0 f__1 ->
    let x__1, ~annotations:x__2, x__3, x__4, x__5 = x__0 in
    f__1 x__1 x__2 x__3 x__4 x__5) pat
    (fun action annotations use_id arity env_at_use ->
      let new_let_conts, arms0, mergeable_arms0 = pat0 in
      let action0 =
        Simplify_common.clear_demoted_trap_action_and_patch_unused_exn_bucket
          uacc action
      in
      let create_arm =
       fun action1 ->
        let annotations0 =
          if
            Upwards_env.is_cold_continuation (Upwards_acc.uenv uacc)
              (Flambda.Apply_cont.continuation action1)
          then Branch_annotations.with_likelihood annotations Likelihood.cold
          else annotations
        in
        Switch_arm.create annotations0 action1
      in
      (fun f__1 f__2 f__3 x__0 ->
        match (x__0 : Expr_builder.rewrite_switch_arm_result) with
        | Expr_builder.Invalid { message = x__1 } -> f__1 x__1
        | Expr_builder.Apply_cont x__1 -> f__2 x__1
        | Expr_builder.New_wrapper x__1 -> f__3 x__1)
        (fun _ -> new_let_conts, arms0, mergeable_arms0)
        (fun action1 ->
          let action2 =
            let cont0 = Flambda.Apply_cont.continuation action1 in
            let cont_info_from_uenv =
              Upwards_env.find_continuation (Upwards_acc.uenv uacc) cont0
            in
            (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
              match (x__0 : Continuation_in_env.t) with
              | Continuation_in_env.Linearly_used_and_inlinable
                  { params = x__1;
                    handler = x__2;
                    free_names_of_handler = x__3;
                    cost_metrics_of_handler = x__4
                  } ->
                f__1 x__1 x__2 x__3 x__4
              | Continuation_in_env.Non_inlinable_zero_arity { handler = x__1 }
                ->
                f__2 x__1
              | Continuation_in_env.Non_inlinable_non_zero_arity
                  { arity = x__1 } ->
                f__3 x__1
              | Continuation_in_env
                .Toplevel_or_function_return_or_exn_continuation
                  { arity = x__1 } ->
                f__4 x__1
              | Continuation_in_env.Invalid { arity = x__1 } -> f__5 x__1)
              (fun _ _ _ _ ->
                if not (Flambda.Apply_cont.is_goto action1)
                then Some action1
                else
                  let check_handler =
                   fun handler action2 ->
                    match Rebuilt_expr.to_apply_cont handler with
                    | Some action3 -> Some action3
                    | None -> Some action2
                  in
                  (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
                    match (x__0 : Continuation_in_env.t) with
                    | Continuation_in_env.Linearly_used_and_inlinable
                        { params = x__1;
                          handler = x__2;
                          free_names_of_handler = x__3;
                          cost_metrics_of_handler = x__4
                        } ->
                      f__1 x__1 x__2 x__3 x__4
                    | Continuation_in_env.Non_inlinable_zero_arity
                        { handler = x__1 } ->
                      f__2 x__1
                    | Continuation_in_env.Non_inlinable_non_zero_arity
                        { arity = x__1 } ->
                      f__3 x__1
                    | Continuation_in_env
                      .Toplevel_or_function_return_or_exn_continuation
                        { arity = x__1 } ->
                      f__4 x__1
                    | Continuation_in_env.Invalid { arity = x__1 } -> f__5 x__1)
                    (fun params handler _ _ ->
                      let () = assert (Bound_parameters.is_empty params) in
                      check_handler handler action1)
                    (fun t0 ->
                      match t0 with
                      | Or_unknown.Known handler ->
                        check_handler handler action1
                      | Or_unknown.Unknown -> Some action1)
                    (fun _ ->
                      Misc.fatal_errorf
                        "Inconsistency for %a between [Apply_cont.is_goto] and \
                         continuation environment in [UA]:@ %a"
                        Continuation.print cont0 Upwards_acc.print uacc)
                    (fun _ -> Some action1)
                    (fun _ -> None)
                    cont_info_from_uenv)
              (fun _ ->
                if not (Flambda.Apply_cont.is_goto action1)
                then Some action1
                else
                  let check_handler =
                   fun handler action2 ->
                    match Rebuilt_expr.to_apply_cont handler with
                    | Some action3 -> Some action3
                    | None -> Some action2
                  in
                  (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
                    match (x__0 : Continuation_in_env.t) with
                    | Continuation_in_env.Linearly_used_and_inlinable
                        { params = x__1;
                          handler = x__2;
                          free_names_of_handler = x__3;
                          cost_metrics_of_handler = x__4
                        } ->
                      f__1 x__1 x__2 x__3 x__4
                    | Continuation_in_env.Non_inlinable_zero_arity
                        { handler = x__1 } ->
                      f__2 x__1
                    | Continuation_in_env.Non_inlinable_non_zero_arity
                        { arity = x__1 } ->
                      f__3 x__1
                    | Continuation_in_env
                      .Toplevel_or_function_return_or_exn_continuation
                        { arity = x__1 } ->
                      f__4 x__1
                    | Continuation_in_env.Invalid { arity = x__1 } -> f__5 x__1)
                    (fun params handler _ _ ->
                      let () = assert (Bound_parameters.is_empty params) in
                      check_handler handler action1)
                    (fun t0 ->
                      match t0 with
                      | Or_unknown.Known handler ->
                        check_handler handler action1
                      | Or_unknown.Unknown -> Some action1)
                    (fun _ ->
                      Misc.fatal_errorf
                        "Inconsistency for %a between [Apply_cont.is_goto] and \
                         continuation environment in [UA]:@ %a"
                        Continuation.print cont0 Upwards_acc.print uacc)
                    (fun _ -> Some action1)
                    (fun _ -> None)
                    cont_info_from_uenv)
              (fun _ ->
                if not (Flambda.Apply_cont.is_goto action1)
                then Some action1
                else
                  let check_handler =
                   fun handler action2 ->
                    match Rebuilt_expr.to_apply_cont handler with
                    | Some action3 -> Some action3
                    | None -> Some action2
                  in
                  (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
                    match (x__0 : Continuation_in_env.t) with
                    | Continuation_in_env.Linearly_used_and_inlinable
                        { params = x__1;
                          handler = x__2;
                          free_names_of_handler = x__3;
                          cost_metrics_of_handler = x__4
                        } ->
                      f__1 x__1 x__2 x__3 x__4
                    | Continuation_in_env.Non_inlinable_zero_arity
                        { handler = x__1 } ->
                      f__2 x__1
                    | Continuation_in_env.Non_inlinable_non_zero_arity
                        { arity = x__1 } ->
                      f__3 x__1
                    | Continuation_in_env
                      .Toplevel_or_function_return_or_exn_continuation
                        { arity = x__1 } ->
                      f__4 x__1
                    | Continuation_in_env.Invalid { arity = x__1 } -> f__5 x__1)
                    (fun params handler _ _ ->
                      let () = assert (Bound_parameters.is_empty params) in
                      check_handler handler action1)
                    (fun t0 ->
                      match t0 with
                      | Or_unknown.Known handler ->
                        check_handler handler action1
                      | Or_unknown.Unknown -> Some action1)
                    (fun _ ->
                      Misc.fatal_errorf
                        "Inconsistency for %a between [Apply_cont.is_goto] and \
                         continuation environment in [UA]:@ %a"
                        Continuation.print cont0 Upwards_acc.print uacc)
                    (fun _ -> Some action1)
                    (fun _ -> None)
                    cont_info_from_uenv)
              (fun _ ->
                if not (Flambda.Apply_cont.is_goto action1)
                then Some action1
                else
                  let check_handler =
                   fun handler action2 ->
                    match Rebuilt_expr.to_apply_cont handler with
                    | Some action3 -> Some action3
                    | None -> Some action2
                  in
                  (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
                    match (x__0 : Continuation_in_env.t) with
                    | Continuation_in_env.Linearly_used_and_inlinable
                        { params = x__1;
                          handler = x__2;
                          free_names_of_handler = x__3;
                          cost_metrics_of_handler = x__4
                        } ->
                      f__1 x__1 x__2 x__3 x__4
                    | Continuation_in_env.Non_inlinable_zero_arity
                        { handler = x__1 } ->
                      f__2 x__1
                    | Continuation_in_env.Non_inlinable_non_zero_arity
                        { arity = x__1 } ->
                      f__3 x__1
                    | Continuation_in_env
                      .Toplevel_or_function_return_or_exn_continuation
                        { arity = x__1 } ->
                      f__4 x__1
                    | Continuation_in_env.Invalid { arity = x__1 } -> f__5 x__1)
                    (fun params handler _ _ ->
                      let () = assert (Bound_parameters.is_empty params) in
                      check_handler handler action1)
                    (fun t0 ->
                      match t0 with
                      | Or_unknown.Known handler ->
                        check_handler handler action1
                      | Or_unknown.Unknown -> Some action1)
                    (fun _ ->
                      Misc.fatal_errorf
                        "Inconsistency for %a between [Apply_cont.is_goto] and \
                         continuation environment in [UA]:@ %a"
                        Continuation.print cont0 Upwards_acc.print uacc)
                    (fun _ -> Some action1)
                    (fun _ -> None)
                    cont_info_from_uenv)
              (fun _ -> None)
              cont_info_from_uenv
          in
          match action2 with
          | Some action3 ->
            let arms1 =
              Target_ocaml_int.Map.add arm (create_arm action3) arms0
            in
            if Option.is_some (Flambda.Apply_cont.trap_action action3)
            then new_let_conts, arms1, Not_mergeable
            else
              (fun f__1 f__2 f__3 x__0 ->
                match x__0 with
                | No_arms -> f__1 ()
                | Mergeable { cont = x__1; args = x__2 } -> f__2 x__1 x__2
                | Not_mergeable -> f__3 ())
                (fun _ ->
                  let cont0 = Flambda.Apply_cont.continuation action3 in
                  let args =
                    List.map
                      (fun arg ->
                        Target_ocaml_int.Map.singleton arm
                          (find_all_aliases env_at_use arg))
                      (Flambda.Apply_cont.args action3)
                  in
                  ( new_let_conts,
                    arms1,
                    (fun (x__1, x__2) -> Mergeable { cont = x__1; args = x__2 })
                      (cont0, args) ))
                (fun cont0 args ->
                  if
                    not
                      (Continuation.equal cont0
                         (Flambda.Apply_cont.continuation action3))
                  then new_let_conts, arms1, Not_mergeable
                  else
                    let args0 =
                      List.map2
                        (fun arg_set arg ->
                          Target_ocaml_int.Map.add arm
                            (find_all_aliases env_at_use arg)
                            arg_set)
                        args
                        (Flambda.Apply_cont.args action3)
                    in
                    ( new_let_conts,
                      arms1,
                      (fun (x__1, x__2) ->
                        Mergeable { cont = x__1; args = x__2 })
                        (cont0, args0) ))
                (fun _ -> new_let_conts, arms1, Not_mergeable)
                mergeable_arms0
          | None -> new_let_conts, arms0, mergeable_arms0)
        (fun new_let_cont0 ->
          let new_let_conts0 = new_let_cont0 :: new_let_conts in
          let action1 = Flambda.Apply_cont.goto new_let_cont0.cont in
          let arms1 = Target_ocaml_int.Map.add arm (create_arm action1) arms0 in
          new_let_conts0, arms1, Not_mergeable)
        (Expr_builder.rewrite_switch_arm uacc action0 use_id arity))

(** val filter_and_choose_alias : Name.Set.t -> alias_set -> Simple.t option
    coq_M **)

let filter_and_choose_alias required_names = function
  | Aliases alias_set1 ->
    let available_alias_set =
      Flambda2_types.Typing_env.Alias_set.filter alias_set1 (fun alias ->
          Simple.pattern_match alias
            (fun name _ -> Name.Set.mem name required_names)
            (fun _ -> true))
    in
    Flambda2_types.Typing_env.Alias_set.find_best available_alias_set
  | Poison kind ->
    Some (Simple.const (Reg_width_const.const_poison kind "rebuild_switch"))

(** val find_cse_simple : bool option -> Common_subexpression_elimination.t ->
    Flambda2_types.Typing_env.t -> Name.Set.t ->
    Common_subexpression_elimination.t -> Flambda_primitive.t -> Simple.t option
    coq_M **)

let find_cse_simple required cse typing_env required_names local_cse prim =
  let required0 =
    match required with Some required0 -> required0 | None -> true
  in
  match Flambda_primitive.Eligible_for_cse.create prim with
  | Some with_fixed_value -> (
    let try_local_cse =
     fun _ -> Common_subexpression_elimination.find local_cse with_fixed_value
    in
    match Common_subexpression_elimination.find cse with_fixed_value with
    | Some simple -> (
      match
        filter_and_choose_alias required_names
          (find_all_aliases typing_env simple)
      with
      | Some simple0 -> Some simple0
      | None -> try_local_cse ())
    | None ->
      if required0
      then
        Misc.fatal_errorf
          "Expected@ primitive@ not@ found@ in@ CSE@ environment@ while@ \
           simplifying switch:@ %a"
          Flambda_primitive.print prim
      else try_local_cse ())
  | None -> None

(** val fields_to_simples : Debuginfo.t -> Simple.t list ->
    Simple.With_debuginfo.t list coq_M **)

let fields_to_simples dbg simples0 =
  List.map (fun simple -> Simple.With_debuginfo.create simple dbg) simples0

(** val fields_to_or_variables : Debuginfo.t -> Target_system.Machine_width.t ->
    (Reg_width_const.t -> 'a1 option coq_M) -> Simple.t list -> 'a1
    Or_variable.t list coq_M **)

let fields_to_or_variables dbg machine_width prover simples0 =
  ListLabels.map
    (fun simple ->
      Simple.pattern_match simple
        (fun _ _ -> assert false)
        (fun cst ->
          let cst0 =
            match Reg_width_const.is_poison cst with
            | Some p ->
              let kind, name = p in
              Reg_width_const.of_int_of_kind machine_width kind
                (String.hash name)
            | None -> cst
          in
          let cst1 =
            match prover cst0 with
            | Some v -> v
            | None ->
              Misc.fatal_errorf
                "Unexpected kind of constant (%a) in switch table at %a"
                Reg_width_const.print cst0 Debuginfo.print_compact dbg
          in
          Or_variable.Const cst1))
    simples0

(** val naked_number_array : Debuginfo.t -> Are_rebuilding_terms.t -> Simple.t
    list -> Target_system.Machine_width.t -> (Are_rebuilding_terms.t -> 'a1
    Or_variable.t list -> Rebuilt_static_const.t coq_M) -> (Reg_width_const.t ->
    'a1 option coq_M) -> Rebuilt_static_const.t coq_M **)

let naked_number_array dbg rebuilding simples0 machine_width creator prover =
  creator rebuilding (fields_to_or_variables dbg machine_width prover simples0)

(** val create_lookup_table_array_const : Debuginfo.t ->
    Flambda_primitive.Array_kind.t -> Are_rebuilding_terms.t -> Simple.t list ->
    Target_system.Machine_width.t -> Rebuilt_static_const.t coq_M **)

let create_lookup_table_array_const dbg array_kind rebuilding simples0
    machine_width =
  match array_kind with
  | Flambda_primitive.Array_kind.Immediates ->
    Rebuilt_static_const.create_immutable_value_array rebuilding
      (fields_to_simples dbg simples0)
  | Flambda_primitive.Array_kind.Gc_ignorable_values ->
    Misc.fatal_errorf
      "Unexpected array kind %a when rebuilding switch lookup table at %a"
      Flambda_primitive.Array_kind.print array_kind Debuginfo.print_compact dbg
  | Flambda_primitive.Array_kind.Values ->
    Rebuilt_static_const.create_immutable_value_array rebuilding
      (fields_to_simples dbg simples0)
  | Flambda_primitive.Array_kind.Naked_floats ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_float_array
      Reg_width_const.is_naked_float
  | Flambda_primitive.Array_kind.Naked_float32s ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_float32_array
      Reg_width_const.is_naked_float32
  | Flambda_primitive.Array_kind.Naked_ints ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_int_array
      Reg_width_const.is_naked_immediate
  | Flambda_primitive.Array_kind.Naked_int8s ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_int8_array
      Reg_width_const.is_naked_int8
  | Flambda_primitive.Array_kind.Naked_int16s ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_int16_array
      Reg_width_const.is_naked_int16
  | Flambda_primitive.Array_kind.Naked_int32s ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_int32_array
      Reg_width_const.is_naked_int32
  | Flambda_primitive.Array_kind.Naked_int64s ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_int64_array
      Reg_width_const.is_naked_int64
  | Flambda_primitive.Array_kind.Naked_nativeints ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_nativeint_array
      Reg_width_const.is_naked_nativeint
  | Flambda_primitive.Array_kind.Naked_vec128s ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_vec128_array
      Reg_width_const.is_naked_vec128
  | Flambda_primitive.Array_kind.Naked_vec256s ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_vec256_array
      Reg_width_const.is_naked_vec256
  | Flambda_primitive.Array_kind.Naked_vec512s ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_vec512_array
      Reg_width_const.is_naked_vec512
  | Flambda_primitive.Array_kind.Naked_masks ->
    naked_number_array dbg rebuilding simples0 machine_width
      Rebuilt_static_const.create_immutable_mask_array
      Reg_width_const.is_naked_mask
  | Flambda_primitive.Array_kind.Unboxed_product _ ->
    Misc.fatal_errorf
      "Unexpected array kind %a when rebuilding switch lookup table at %a"
      Flambda_primitive.Array_kind.print array_kind Debuginfo.print_compact dbg

type named =
  | Simple of Simple.t
  | Prim of string * K.t * P.t * Debuginfo.t
  | Lookup_table of
      { name : string;
        array_kind : P.Array_kind.t;
        element_kind : KS.t;
        simples : Simple.t list;
        dbg : Debuginfo.t
      }

(** val bound_simple : Simple.t -> named coq_M **)

let bound_simple simple = Simple simple

(** val bound_prim : string -> Flambda_kind.t -> Flambda_primitive.t ->
    Debuginfo.t -> named coq_M **)

let bound_prim name kind prim dbg = Prim (name, kind, prim, dbg)

(** val bound_lookup_table : string -> Flambda_kind.With_subkind.t ->
    Flambda_primitive.Array_kind.t -> Simple.t list -> Debuginfo.t -> named
    coq_M **)

let bound_lookup_table name element_kind array_kind simples0 dbg =
  (fun (x__1, x__2, x__3, x__4, x__5) ->
    Lookup_table
      { name = x__1;
        array_kind = x__2;
        element_kind = x__3;
        simples = x__4;
        dbg = x__5
      })
    (name, array_kind, element_kind, simples0, dbg)

(** val let_op_dollar : named -> (Simple.t -> (Upwards_acc.t -> Symbol.t
    Static_const.Map.t -> Flambda2_types.Typing_env.t ->
    Common_subexpression_elimination.t -> Common_subexpression_elimination.t ->
    (Rebuilt_expr.t * Upwards_acc.t) coq_M) coq_M) -> (Upwards_acc.t -> Symbol.t
    Static_const.Map.t -> Flambda2_types.Typing_env.t ->
    Common_subexpression_elimination.t -> Common_subexpression_elimination.t ->
    (Rebuilt_expr.t * Upwards_acc.t) coq_M) coq_M **)

let let_op_dollar expr k uacc shareable_constants0 typing_env_before_switch0
    cse_before_switch0 local_cse =
  let machine_width =
    Flambda2_types.Typing_env.machine_width typing_env_before_switch0
  in
  let already_bound =
   fun simple ->
    k simple uacc shareable_constants0 typing_env_before_switch0
      cse_before_switch0 local_cse
  in
  (fun f__1 f__2 f__3 x__0 ->
    match x__0 with
    | Simple x__1 -> f__1 x__1
    | Prim (x__1, x__2, x__3, x__4) -> f__2 x__1 x__2 x__3 x__4
    | Lookup_table
        { name = x__1;
          array_kind = x__2;
          element_kind = x__3;
          simples = x__4;
          dbg = x__5
        } ->
      f__3 x__1 x__2 x__3 x__4 x__5)
    (fun simple -> already_bound simple)
    (fun name kind prim dbg ->
      match
        find_cse_simple (Some false) cse_before_switch0
          typing_env_before_switch0
          (Upwards_acc.required_names uacc)
          local_cse prim
      with
      | Some simple -> already_bound simple
      | None ->
        let named0 = Flambda.Named.create_prim prim dbg in
        let var =
          (fun x__1 x__2 x__3 -> Variable.create ?user_visible:x__1 x__2 x__3)
            None name kind
        in
        let uacc0 =
          Upwards_acc.add_free_names uacc
            (Name_occurrences.singleton_variable var Name_mode.normal)
        in
        let local_cse0 =
          match Flambda_primitive.Eligible_for_cse.create prim with
          | Some with_fixed_value ->
            Common_subexpression_elimination.add local_cse with_fixed_value
              (Simple.var var)
              (Flambda2_types.Typing_env.current_scope typing_env_before_switch0)
          | None -> local_cse
        in
        let body, uacc1 =
          k (Simple.var var) uacc0 shareable_constants0
            typing_env_before_switch0 cse_before_switch0 local_cse0
        in
        let duid = Flambda_debug_uid.none in
        let machine_width0 =
          Upwards_env.machine_width (Upwards_acc.uenv uacc1)
        in
        let binding =
          let simplified_defining_expr =
            Simplified_named.create machine_width0 named0
          in
          let let_bound =
            Bound_pattern.singleton (Bound_var.create var duid Name_mode.normal)
          in
          (fun (x__1, x__2, x__3) ->
            (Simplified_named.Keep_binding
               { let_bound = x__1;
                 simplified_defining_expr = x__2;
                 original_defining_expr = x__3
               }
              : Simplified_named.binding_to_place))
            (let_bound, simplified_defining_expr, None)
        in
        Expr_builder.make_new_let_bindings uacc1 (binding :: []) body)
    (fun name array_kind element_kind simples0 dbg ->
      let array_const =
        create_lookup_table_array_const dbg array_kind
          (Upwards_acc.are_rebuilding_terms uacc)
          simples0 machine_width
      in
      let create_lookup_table =
       fun static_const ->
        let symbol = Symbol.manufacture (Current_unit.get_cu_exn ()) name in
        let shareable_constants1 =
          match static_const with
          | Some static_const0 ->
            if Static_const.can_share static_const0
            then Static_const.Map.add static_const0 symbol shareable_constants0
            else shareable_constants0
          | None -> shareable_constants0
        in
        let fields =
          List.map
            (Flambda2_types.alias_type_of
               (Flambda_kind.With_subkind.kind element_kind))
            simples0
        in
        let block_type =
          Flambda2_types.immutable_array (Or_unknown_or_bottom.Ok element_kind)
            fields Alloc_mode.For_types.heap machine_width
        in
        let uacc0 =
          Upwards_acc.add_lifted_constant uacc
            (Lifted_constant.create_block_like symbol Variable.Map.empty
               array_const typing_env_before_switch0 block_type)
        in
        k (Simple.symbol symbol) uacc0 shareable_constants1
          typing_env_before_switch0 cse_before_switch0 local_cse
      in
      match Rebuilt_static_const.to_const array_const with
      | Some t0 -> (
        match t0 with
        | Flambda.Code _ -> Misc.fatal_error "Cannot bind code"
        | Flambda.Deleted_code -> Misc.fatal_error "Cannot bind code"
        | Flambda.Static_const const -> (
          match Static_const.Map.find_opt const shareable_constants0 with
          | Some symbol -> already_bound (Simple.symbol symbol)
          | None -> create_lookup_table (Some const)))
      | None -> create_lookup_table None)
    expr

(** val return_ : Code_size.t -> Name_occurrences.t -> Rebuilt_expr.t ->
    (Upwards_acc.t -> Symbol.t Static_const.Map.t -> Flambda2_types.Typing_env.t
    -> Common_subexpression_elimination.t -> Common_subexpression_elimination.t
    -> (Rebuilt_expr.t * Upwards_acc.t) coq_M) coq_M **)

let return_ added_code_size free_names expr uacc _ _ _ _ =
  let uacc0 = Upwards_acc.notify_added added_code_size uacc in
  let uacc1 = Upwards_acc.add_free_names uacc0 free_names in
  expr, uacc1

(** val run : Upwards_acc.t -> Symbol.t Static_const.Map.t ->
    Flambda2_types.Typing_env.t -> Common_subexpression_elimination.t ->
    (Upwards_acc.t -> Symbol.t Static_const.Map.t -> Flambda2_types.Typing_env.t
    -> Common_subexpression_elimination.t -> Common_subexpression_elimination.t
    -> (Rebuilt_expr.t * Upwards_acc.t) coq_M) -> (Rebuilt_expr.t *
    Upwards_acc.t) coq_M **)

let run uacc shareable_constants0 typing_env_before_switch0 cse_before_switch0 k
    =
  k uacc shareable_constants0 typing_env_before_switch0 cse_before_switch0
    Common_subexpression_elimination.empty

type affine_immediate_kind =
  | Tagged
  | Naked

(** val equal_affine_immediate_kind : affine_immediate_kind ->
    affine_immediate_kind -> bool coq_M **)

let equal_affine_immediate_kind kind1 kind2 =
  match kind1 with
  | Tagged -> ( match kind2 with Tagged -> true | Naked -> false)
  | Naked -> ( match kind2 with Tagged -> false | Naked -> true)

(** val affine_immediate_kind_to_standard_int : affine_immediate_kind ->
    Flambda_kind.Standard_int.t coq_M **)

let affine_immediate_kind_to_standard_int = function
  | Tagged -> Flambda_kind.Standard_int.Tagged_immediate
  | Naked -> Flambda_kind.Standard_int.Naked_immediate

type affine_argument_of_mergeable_arm =
  | Not_affine
  | Maybe_affine
  | Constant of affine_immediate_kind * Target_ocaml_int.t * Target_ocaml_int.t
  | Affine of affine_immediate_kind * Target_ocaml_int.t * Target_ocaml_int.t

(** val recognize_affine_immediate_const : Reg_width_const.t ->
    (affine_immediate_kind * Target_ocaml_int.t) option coq_M **)

let recognize_affine_immediate_const const =
  match Reg_width_const.descr const with
  | Int_ids.Const.Descr.Naked_immediate naked_imm -> Some (Naked, naked_imm)
  | Int_ids.Const.Descr.Tagged_immediate tagged_imm -> Some (Tagged, tagged_imm)
  | Int_ids.Const.Descr.Naked_float32 _ -> None
  | Int_ids.Const.Descr.Naked_float _ -> None
  | Int_ids.Const.Descr.Naked_int8 _ -> None
  | Int_ids.Const.Descr.Naked_int16 _ -> None
  | Int_ids.Const.Descr.Naked_int32 _ -> None
  | Int_ids.Const.Descr.Naked_int64 _ -> None
  | Int_ids.Const.Descr.Naked_nativeint _ -> None
  | Int_ids.Const.Descr.Naked_vec128 _ -> None
  | Int_ids.Const.Descr.Naked_vec256 _ -> None
  | Int_ids.Const.Descr.Naked_vec512 _ -> None
  | Int_ids.Const.Descr.Naked_mask _ -> None
  | Int_ids.Const.Descr.Null -> None
  | Int_ids.Const.Descr.Poison (_, _) -> None

(** val recognize_affine_argument : Target_system.Machine_width.t ->
    affine_argument_of_mergeable_arm -> Target_ocaml_int.t -> Reg_width_const.t
    -> affine_argument_of_mergeable_arm coq_M **)

let recognize_affine_argument machine_width affine_argument discr const =
  let affine = fun kind offset slope -> Affine (kind, offset, slope) in
  let recognized = recognize_affine_immediate_const const in
  match affine_argument with
  | Not_affine -> Not_affine
  | Maybe_affine -> (
    match recognized with
    | Some p ->
      let kind, imm = p in
      Constant (kind, discr, imm)
    | None -> Not_affine)
  | Constant (kind, arm, arg) -> (
    match recognized with
    | Some p ->
      let imm_kind, imm = p in
      let () =
        if not (equal_affine_immediate_kind kind imm_kind)
        then Misc.fatal_error "Inconsistent kinds for mergeable switch argument"
        else ()
      in
      let arg_diff = Target_ocaml_int.sub imm arg in
      let arm_diff = Target_ocaml_int.sub discr arm in
      if
        Target_ocaml_int.equal
          (Target_ocaml_int.zero machine_width)
          (Target_ocaml_int.mod_ arg_diff arm_diff)
      then
        let slope = Target_ocaml_int.div arg_diff arm_diff in
        let offset =
          Target_ocaml_int.sub arg (Target_ocaml_int.mul slope arm)
        in
        affine kind offset slope
      else Not_affine
    | None -> Not_affine)
  | Affine (kind, offset, slope) -> (
    match recognized with
    | Some p ->
      let imm_kind, imm = p in
      let () =
        if not (equal_affine_immediate_kind imm_kind kind)
        then Misc.fatal_error "Inconsistent kinds for mergeable switch argument"
        else ()
      in
      if
        Target_ocaml_int.equal imm
          (Target_ocaml_int.add (Target_ocaml_int.mul discr slope) offset)
      then affine kind offset slope
      else Not_affine
    | None -> Not_affine)

type mergeable_argument =
  | Invariant_argument of Simple.t
  | Tagged_scrutinee
  | Not_scrutinee
  | Affine_argument of
      { kind : affine_immediate_kind;
        offset : TI.t;
        slope : TI.t
      }
  | Lookup_table_argument of
      { array_kind : P.Array_kind.t;
        array_load_kind : P.Array_load_kind.t;
        first_discriminant : TI.t;
        simples : Simple.t list
      }

(** val enough_arms : int -> mergeable_argument -> bool coq_M **)

let enough_arms num_arms x =
  (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
    match x__0 with
    | Invariant_argument x__1 -> f__1 x__1
    | Tagged_scrutinee -> f__2 ()
    | Not_scrutinee -> f__3 ()
    | Affine_argument { kind = x__1; offset = x__2; slope = x__3 } ->
      f__4 x__1 x__2 x__3
    | Lookup_table_argument
        { array_kind = x__1;
          array_load_kind = x__2;
          first_discriminant = x__3;
          simples = x__4
        } ->
      f__5 x__1 x__2 x__3 x__4)
    (fun _ -> true)
    (fun _ -> true)
    (fun _ -> true)
    (fun _ _ _ -> Stdlib.( >= ) num_arms 3)
    (fun _ _ _ _ -> Stdlib.( >= ) num_arms 3)
    x

(** val bound_tagged_scrutinee : Simple.t -> Debuginfo.t -> named coq_M **)

let bound_tagged_scrutinee scrutinee0 dbg =
  bound_prim "tagged_scrutinee" Flambda_kind.value
    (Flambda_primitive.Unary (Flambda_primitive.Tag_immediate, scrutinee0))
    dbg

(** val rebuild_mergeable_argument : Target_system.Machine_width.t -> Simple.t
    -> mergeable_argument -> (Simple.t -> (Upwards_acc.t -> Symbol.t
    Static_const.Map.t -> Flambda2_types.Typing_env.t ->
    Common_subexpression_elimination.t -> Common_subexpression_elimination.t ->
    (Rebuilt_expr.t * Upwards_acc.t) coq_M) coq_M) -> (Upwards_acc.t -> Symbol.t
    Static_const.Map.t -> Flambda2_types.Typing_env.t ->
    Common_subexpression_elimination.t -> Common_subexpression_elimination.t ->
    (Rebuilt_expr.t * Upwards_acc.t) coq_M) coq_M **)

let rebuild_mergeable_argument machine_width scrutinee0 mergeable_argument0 k =
  let dbg = Debuginfo.none in
  (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
    match x__0 with
    | Invariant_argument x__1 -> f__1 x__1
    | Tagged_scrutinee -> f__2 ()
    | Not_scrutinee -> f__3 ()
    | Affine_argument { kind = x__1; offset = x__2; slope = x__3 } ->
      f__4 x__1 x__2 x__3
    | Lookup_table_argument
        { array_kind = x__1;
          array_load_kind = x__2;
          first_discriminant = x__3;
          simples = x__4
        } ->
      f__5 x__1 x__2 x__3 x__4)
    (fun simple -> k simple)
    (fun _ -> let_op_dollar (bound_tagged_scrutinee scrutinee0 dbg) k)
    (fun _ ->
      let_op_dollar (bound_tagged_scrutinee scrutinee0 dbg)
        (fun tagged_scrutinee ->
          let_op_dollar
            (bound_prim "not_scrutinee" Flambda_kind.value
               (Flambda_primitive.Unary
                  (Flambda_primitive.Boolean_not, tagged_scrutinee))
               dbg)
            k))
    (fun kind offset slope ->
      let rebuild_affine_expr =
       fun scrutinee1 const ->
        let standard_int = affine_immediate_kind_to_standard_int kind in
        let kind0 = Flambda_kind.Standard_int.to_kind standard_int in
        let must_negate, slope0 =
          if Target_ocaml_int.is_non_negative slope
          then false, slope
          else true, Target_ocaml_int.neg slope
        in
        let_op_dollar
          (if Target_ocaml_int.equal slope0 (Target_ocaml_int.one machine_width)
           then bound_simple scrutinee1
           else
             bound_prim "scaled_arg" kind0
               (Flambda_primitive.Binary
                  ( Flambda_primitive.Int_arith
                      ( standard_int,
                        (Flambda_primitive.Mul
                          : Flambda_primitive.binary_int_arith_op) ),
                    scrutinee1,
                    Simple.const (const slope0) ))
               dbg)
          (fun scaled_arg ->
            let_op_dollar
              (if
                 Target_ocaml_int.equal offset
                   (Target_ocaml_int.zero machine_width)
                 && not must_negate
               then bound_simple scaled_arg
               else
                 bound_prim "final_arg" kind0
                   (Flambda_primitive.Binary
                      ( Flambda_primitive.Int_arith
                          ( standard_int,
                            if must_negate
                            then
                              (Flambda_primitive.Sub
                                : Flambda_primitive.binary_int_arith_op)
                            else
                              (Flambda_primitive.Add
                                : Flambda_primitive.binary_int_arith_op) ),
                        Simple.const (const offset),
                        scaled_arg ))
                   dbg)
              k)
      in
      match kind with
      | Tagged ->
        let_op_dollar (bound_tagged_scrutinee scrutinee0 dbg)
          (fun tagged_scrutinee ->
            rebuild_affine_expr tagged_scrutinee
              Reg_width_const.tagged_immediate)
      | Naked -> rebuild_affine_expr scrutinee0 Reg_width_const.naked_immediate)
    (fun array_kind array_load_kind first_discriminant simples0 ->
      let element_kind =
        Flambda_primitive.Array_load_kind.kind_of_loaded_value array_load_kind
      in
      let loaded_kind = Flambda_kind.With_subkind.kind element_kind in
      let_op_dollar
        (bound_lookup_table "switch_block" element_kind array_kind simples0 dbg)
        (fun switch_block ->
          let_op_dollar
            (bound_prim "tagged_scrutinee" Flambda_kind.value
               (Flambda_primitive.Unary
                  (Flambda_primitive.Tag_immediate, scrutinee0))
               dbg)
            (fun tagged_scrutinee ->
              let_op_dollar
                (if
                   Target_ocaml_int.equal first_discriminant
                     (Target_ocaml_int.zero machine_width)
                 then bound_simple tagged_scrutinee
                 else
                   bound_prim "offset_scrutinee" Flambda_kind.value
                     (Flambda_primitive.Binary
                        ( Flambda_primitive.Int_arith
                            ( Flambda_kind.Standard_int.Tagged_immediate,
                              (Flambda_primitive.Add
                                : Flambda_primitive.binary_int_arith_op) ),
                          tagged_scrutinee,
                          Simple.const_int
                            (Target_ocaml_int.neg first_discriminant) ))
                     dbg)
                (fun offset_scrutinee ->
                  let_op_dollar
                    (bound_prim "arg" loaded_kind
                       (Flambda_primitive.Binary
                          ( Flambda_primitive.Array_load
                              (array_kind, array_load_kind, Mutability.Immutable),
                            switch_block,
                            offset_scrutinee ))
                       dbg)
                    k))))
    mergeable_argument0

(** val recognize_invariant_argument : Name.Set.t -> alias_set TI.Map.t ->
    Simple.t option coq_M **)

let recognize_invariant_argument required_names arg =
  let shared_alias_set =
    Target_ocaml_int.Map.fold
      (fun _ alias_set0 shared_alias_set ->
        match shared_alias_set with
        | Some shared_alias_set0 ->
          Some (inter_alias_set alias_set0 shared_alias_set0)
        | None -> Some alias_set0)
      arg None
  in
  let shared_alias_set0 =
    match shared_alias_set with
    | Some shared_alias_set0 -> shared_alias_set0
    | None -> Misc.fatal_error "Trying to merge zero switch arms"
  in
  filter_and_choose_alias required_names shared_alias_set0

type const_or_symbol =
  | Const of Reg_width_const.t
  | Symbol

(** val recognize_mergeable_argument : Target_system.Machine_width.t -> Simple.t
    -> Name.Set.t -> Debuginfo.t -> alias_set TI.Map.t -> mergeable_argument
    option coq_M **)

let recognize_mergeable_argument machine_width scrutinee0 required_names dbg arg
    =
  let check_arm =
   fun discr alias_set0 pat ->
    let affine_arg, args_rev_and_expected_discr = pat in
    let maybe_table_lookup_arg =
     fun constant_arg simple ->
      match args_rev_and_expected_discr with
      | Some p ->
        let args_rev, expected_discr = p in
        if not (Target_ocaml_int.equal discr expected_discr)
        then constant_arg, None
        else
          let expected_discr0 =
            Target_ocaml_int.add
              (Target_ocaml_int.one machine_width)
              expected_discr
          in
          constant_arg, Some (simple :: args_rev, expected_discr0)
      | None -> constant_arg, None
    in
    let maybe_constant_arg =
     fun const ->
      let constant_args =
        recognize_affine_argument machine_width affine_arg discr const
      in
      maybe_table_lookup_arg constant_args (Simple.const const)
    in
    match alias_set0 with
    | Aliases aliases -> (
      match Flambda2_types.Typing_env.Alias_set.find_best aliases with
      | Some simple -> (
        match
          Simple.pattern_match' simple
            (fun _ _ ->
              Port_monad.raise_
                ( (fun () -> Argument_cannot_be_used_in_lookup_table),
                  function
                  | Argument_cannot_be_used_in_lookup_table -> Some ()
                  | _ -> None )
                ())
            (fun _ coercion ->
              let () =
                if
                  not
                    (Name_occurrences.no_variables
                       (Coercion.free_names coercion))
                then
                  Port_monad.raise_
                    ( (fun () -> Argument_cannot_be_used_in_lookup_table),
                      function
                      | Argument_cannot_be_used_in_lookup_table -> Some ()
                      | _ -> None )
                    ()
                else ()
              in
              Symbol)
            (fun const -> Const const)
        with
        | Const const -> maybe_constant_arg const
        | Symbol -> maybe_table_lookup_arg Not_affine simple)
      | None -> Misc.fatal_error "Unexpected empty argument")
    | Poison kind ->
      maybe_table_lookup_arg affine_arg
        (Simple.const (Reg_width_const.const_poison kind "rebuild_switch"))
  in
  match recognize_invariant_argument required_names arg with
  | Some simple -> Some (Invariant_argument simple)
  | None ->
    let first_discr =
      Port_monad.try_with
        (fun _ -> fst (Target_ocaml_int.Map.min_binding arg))
        Port_monad.not_found
        (fun _ -> Target_ocaml_int.zero machine_width)
    in
    let affine_is_identity =
     fun offset slope ->
      Target_ocaml_int.equal offset (Target_ocaml_int.zero machine_width)
      && Target_ocaml_int.equal slope (Target_ocaml_int.one machine_width)
    in
    let affine_is_boolean_not =
     fun offset slope ->
      Target_ocaml_int.equal offset (Target_ocaml_int.one machine_width)
      && Target_ocaml_int.equal slope (Target_ocaml_int.minus_one machine_width)
      && Target_ocaml_int.Map.subset_domain arg
           (Target_ocaml_int.Map.of_set
              (fun _ -> ())
              (Target_ocaml_int.all_bools machine_width))
    in
    Port_monad.match_exn
      (fun _ ->
        Target_ocaml_int.Map.fold check_arm arg
          (Maybe_affine, Some ([], first_discr)))
      ( (fun () -> Argument_cannot_be_used_in_lookup_table),
        function
        | Argument_cannot_be_used_in_lookup_table -> Some ()
        | _ -> None )
      (fun _ -> None)
      (fun x ->
        let a, o = x in
        match a with
        | Not_affine -> (
          match o with
          | Some p -> (
            let args_rev, _ = p in
            match args_rev with
            | [] -> None
            | _ :: _ -> (
              let args = List.rev args_rev in
              let () =
                assert (Stdlib.( >= ) (List.compare_length_with args 1) 0)
              in
              let kind_of =
               fun simple ->
                Simple.pattern_match' simple
                  (fun _ _ ->
                    Misc.fatal_errorf "Variable (%a) was not expected here: %a"
                      Simple.print simple Debuginfo.print_compact dbg)
                  (fun _ _ -> Flambda_kind.value)
                  Reg_width_const.kind
              in
              let first_kind = kind_of (List.hd args) in
              if
                not
                  (List.for_all
                     (fun arg0 -> Flambda_kind.equal (kind_of arg0) first_kind)
                     args)
              then None
              else
                let single_kind =
                 fun array_kind array_load_kind ->
                  Some
                    ((fun (x__1, x__2, x__3, x__4) ->
                       Lookup_table_argument
                         { array_kind = x__1;
                           array_load_kind = x__2;
                           first_discriminant = x__3;
                           simples = x__4
                         })
                       (array_kind, array_load_kind, first_discr, args))
                in
                match first_kind with
                | Flambda_kind.Value ->
                  if
                    List.for_all
                      (fun simple ->
                        Option.is_some
                          (Option.bind
                             (Simple.must_be_const simple)
                             Reg_width_const.is_tagged_immediate))
                      args
                  then
                    single_kind Flambda_primitive.Array_kind.Immediates
                      Flambda_primitive.Array_load_kind.Immediates
                  else
                    single_kind Flambda_primitive.Array_kind.Values
                      Flambda_primitive.Array_load_kind.Values
                | Flambda_kind.Naked_number nn -> (
                  match nn with
                  | Flambda_kind.Naked_number_kind.Naked_immediate ->
                    single_kind Flambda_primitive.Array_kind.Naked_ints
                      Flambda_primitive.Array_load_kind.Naked_ints
                  | Flambda_kind.Naked_number_kind.Naked_float32 ->
                    single_kind Flambda_primitive.Array_kind.Naked_float32s
                      Flambda_primitive.Array_load_kind.Naked_float32s
                  | Flambda_kind.Naked_number_kind.Naked_float ->
                    single_kind Flambda_primitive.Array_kind.Naked_floats
                      Flambda_primitive.Array_load_kind.Naked_floats
                  | Flambda_kind.Naked_number_kind.Naked_int8 ->
                    single_kind Flambda_primitive.Array_kind.Naked_int8s
                      Flambda_primitive.Array_load_kind.Naked_int8s
                  | Flambda_kind.Naked_number_kind.Naked_int16 ->
                    single_kind Flambda_primitive.Array_kind.Naked_int16s
                      Flambda_primitive.Array_load_kind.Naked_int16s
                  | Flambda_kind.Naked_number_kind.Naked_int32 ->
                    single_kind Flambda_primitive.Array_kind.Naked_int32s
                      Flambda_primitive.Array_load_kind.Naked_int32s
                  | Flambda_kind.Naked_number_kind.Naked_int64 ->
                    single_kind Flambda_primitive.Array_kind.Naked_int64s
                      Flambda_primitive.Array_load_kind.Naked_int64s
                  | Flambda_kind.Naked_number_kind.Naked_nativeint ->
                    single_kind Flambda_primitive.Array_kind.Naked_nativeints
                      Flambda_primitive.Array_load_kind.Naked_nativeints
                  | Flambda_kind.Naked_number_kind.Naked_vec128 ->
                    single_kind Flambda_primitive.Array_kind.Naked_vec128s
                      Flambda_primitive.Array_load_kind.Naked_vec128s
                  | Flambda_kind.Naked_number_kind.Naked_vec256 ->
                    single_kind Flambda_primitive.Array_kind.Naked_vec256s
                      Flambda_primitive.Array_load_kind.Naked_vec256s
                  | Flambda_kind.Naked_number_kind.Naked_vec512 ->
                    single_kind Flambda_primitive.Array_kind.Naked_vec512s
                      Flambda_primitive.Array_load_kind.Naked_vec512s
                  | Flambda_kind.Naked_number_kind.Naked_mask ->
                    single_kind Flambda_primitive.Array_kind.Naked_masks
                      Flambda_primitive.Array_load_kind.Naked_masks)
                | Flambda_kind.Region -> None
                | Flambda_kind.Rec_info -> None))
          | None -> None)
        | Maybe_affine -> Misc.fatal_error "Unexpected invariant argument"
        | Constant (_, _, _) -> Misc.fatal_error "Unexpected invariant argument"
        | Affine (kind, offset, slope) -> (
          if affine_is_identity offset slope
          then
            match kind with
            | Tagged -> Some Tagged_scrutinee
            | Naked -> Some (Invariant_argument scrutinee0)
          else
            match kind with
            | Tagged ->
              if affine_is_boolean_not offset slope
              then Some Not_scrutinee
              else
                Some
                  ((fun (x__1, x__2, x__3) ->
                     Affine_argument
                       { kind = x__1; offset = x__2; slope = x__3 })
                     (kind, offset, slope))
            | Naked ->
              Some
                ((fun (x__1, x__2, x__3) ->
                   Affine_argument { kind = x__1; offset = x__2; slope = x__3 })
                   (kind, offset, slope))))

(** val rebuild_switch : SE.simplified_switch_ -> Upwards_acc.t ->
    Simplify_common.after_rebuild -> (Rebuilt_expr.t * Upwards_acc.t) coq_M **)

let rebuild_switch pat uacc after_rebuild =
  let { SE.arms = arms0;
        SE.condition_dbg = condition_dbg0;
        SE.scrutinee = scrutinee0;
        SE.scrutinee_ty = scrutinee_ty0;
        SE.shareable_constants = shareable_constants0;
        SE.typing_env_before_switch = typing_env_before_switch0;
        SE.cse_before_switch = cse_before_switch0
      } =
    pat
  in
  let machine_width =
    Flambda2_types.Typing_env.machine_width typing_env_before_switch0
  in
  let new_let_conts, arms1, mergeable_arms0 =
    Target_ocaml_int.Map.fold (rebuild_arm uacc) arms0
      ([], Target_ocaml_int.Map.empty, No_arms)
  in
  let num_arms = Target_ocaml_int.Map.cardinal arms1 in
  let switch_merged =
    (fun f__1 f__2 f__3 x__0 ->
      match x__0 with
      | No_arms -> f__1 ()
      | Mergeable { cont = x__1; args = x__2 } -> f__2 x__1 x__2
      | Not_mergeable -> f__3 ())
      (fun _ -> None)
      (fun cont0 args ->
        let num_args = List.length args in
        let mergeable_args =
          List.filter_map
            (recognize_mergeable_argument machine_width scrutinee0
               (Upwards_acc.required_names uacc)
               condition_dbg0)
            args
        in
        if
          List.compare_length_with mergeable_args num_args = 0
          && List.for_all (enough_arms num_arms) mergeable_args
        then Some (cont0, mergeable_args)
        else None)
      (fun _ -> None)
      mergeable_arms0
  in
  let body, uacc0 =
    if Stdlib.( < ) num_arms 1
    then
      let uacc0 = Upwards_acc.notify_removed Removed_operations.branch uacc in
      Rebuilt_expr.create_invalid Flambda.Invalid.Zero_switch_arms, uacc0
    else
      let dbg = Debuginfo.none in
      let normal_case =
       fun uacc0 ->
        let expr, uacc1 =
          Expr_builder.create_switch uacc0 condition_dbg0 scrutinee0 arms1
        in
        let () =
          if
            Flambda_features.check_invariants ()
            && Simple.is_const scrutinee0 && num_arms > 1
          then
            Misc.fatal_errorf
              "[Switch] with constant scrutinee (type: %a) should have been \
               simplified away:@ %a"
              Flambda2_types.print scrutinee_ty0
              (Rebuilt_expr.print (Upwards_acc.are_rebuilding_terms uacc1))
              expr
          else ()
        in
        expr, uacc1
      in
      match switch_merged with
      | Some p ->
        let dest, args = p in
        let uacc0 = Upwards_acc.notify_removed Removed_operations.branch uacc in
        run uacc0 shareable_constants0 typing_env_before_switch0
          cse_before_switch0
          (let rec rebuild_merged_switch mergeable_args args_rev =
             match mergeable_args with
             | [] ->
               let args0 = List.rev args_rev in
               let is_cold =
                 Upwards_env.is_cold_continuation (Upwards_acc.uenv uacc0) dest
               in
               let apply_cont =
                 (fun x__1 x__2 x__3 x__4 ->
                   Flambda.Apply_cont.create ?trap_action:x__1 x__2 x__3 x__4)
                   None dest args0 dbg
               in
               return_
                 (Code_size.apply_cont apply_cont)
                 (Flambda.Apply_cont.free_names apply_cont)
                 (Rebuilt_expr.create_apply_cont is_cold apply_cont)
             | special_arg :: special_args ->
               rebuild_mergeable_argument machine_width scrutinee0 special_arg
                 (fun arg ->
                   rebuild_merged_switch special_args (arg :: args_rev))
           in
           rebuild_merged_switch args [])
      | None -> normal_case uacc
  in
  let uacc1, expr = Expr_builder.bind_let_conts uacc0 body new_let_conts in
  after_rebuild expr uacc1

(** val simplify_arm : Target_ocaml_int.t -> (Switch_arm.t *
    Flambda2_types.Typing_env.t) -> ((Apply_cont_expr.t, Branch_annotations.t,
    Apply_cont_rewrite_id.t, [ `Unarized ] Flambda_arity.t,
    Flambda2_types.Typing_env.t) Port_monad.tuple5 TI.Map.t * Downwards_acc.t)
    -> ((Apply_cont_expr.t, Branch_annotations.t, Apply_cont_rewrite_id.t,
    [ `Unarized ] Flambda_arity.t, Flambda2_types.Typing_env.t)
    Port_monad.tuple5 TI.Map.t * Downwards_acc.t) coq_M **)

let simplify_arm arm pat pat0 =
  let switch_arm, env_at_use = pat in
  let arms0, dacc = pat0 in
  let action = Switch_arm.action switch_arm in
  let annotations = Switch_arm.annotations switch_arm in
  let denv_at_use =
    Downwards_env.with_typing_env (Downwards_acc.denv dacc) env_at_use
  in
  let args = Flambda.Apply_cont.args action in
  let use_kind =
    Simplify_common.apply_cont_use_kind Simplify_common.Switch_branch action
  in
  let { S.simples = args0; S.simple_tys = arg_types } =
    Simplify_simple.simplify_simples
      (Downwards_acc.with_denv dacc denv_at_use)
      args
  in
  let denv_at_use0 =
    if Switch_arm.is_cold switch_arm
    then Downwards_env.mark_as_cold denv_at_use
    else denv_at_use
  in
  let dacc0, rewrite_id =
    Downwards_acc.record_continuation_use dacc
      (Flambda.Apply_cont.continuation action)
      use_kind denv_at_use0 arg_types
  in
  let arity =
    Flambda_arity.create_singletons
      (List.map
         (fun ty -> Flambda_kind.With_subkind.anything (Flambda2_types.kind ty))
         arg_types)
  in
  let action0 = Flambda.Apply_cont.update_args action args0 in
  let dbg = Flambda.Apply_cont.debuginfo action0 in
  let dbg0 =
    Downwards_env.add_inlined_debuginfo (Downwards_acc.denv dacc0) dbg
  in
  let action1 = Flambda.Apply_cont.with_debuginfo action0 dbg0 in
  let dacc1 =
    Downwards_acc.map_flow_acc dacc0
      (Flow.Acc.add_apply_cont_args rewrite_id
         (Flambda.Apply_cont.continuation action1)
         args0)
  in
  let arms1 =
    Target_ocaml_int.Map.add arm
      ((fun x__1 x__2 x__3 x__4 x__5 ->
         x__1, ~annotations:x__2, x__3, x__4, x__5)
         action1 annotations rewrite_id arity env_at_use)
      arms0
  in
  arms1, dacc1

(** val decide_continuation_specialization0 : Downwards_acc.t ->
    Flambda.Switch.t -> Simple.t ->
    [ `Disabled | `Single_use | `Exn_handler | `Toplevel | `All_unknown |
     `No_reason_to_spec | `Not_lifting | `Cannot_specialize |
     `Insufficient_lifting_budget | `Not_enough_join_info |
     `Too_many_unknown_uses | `Too_costly | `Specialized of Continuation.t * int
     ] coq_M **)

let decide_continuation_specialization0 dacc switch scrutinee0 =
  (fun f__1 f__2 f__3 x__0 ->
    match (x__0 : Are_lifting_conts.t) with
    | Are_lifting_conts.Not_lifting x__1 -> f__1 x__1
    | Are_lifting_conts.Analyzing
        { continuation = x__1; is_exn_handler = x__2; uses = x__3 } ->
      f__2 x__1 x__2 x__3
    | Are_lifting_conts.Lifting_out_of { continuation = x__1 } -> f__3 x__1)
    (fun _ -> `Not_lifting)
    (fun continuation is_exn_handler uses ->
      let n_uses = Continuation_uses.number_of_uses uses in
      if Stdlib.( <= ) n_uses 1
      then `Single_use
      else if is_exn_handler
      then `Exn_handler
      else if Downwards_env.at_unit_toplevel (Downwards_acc.denv dacc)
      then `Toplevel
      else
        let denv = Downwards_acc.denv dacc in
        (fun f__1 f__2 x__0 ->
          match (x__0 : Specialization_cost.t) with
          | Specialization_cost.Can_specialize x__1 -> f__1 x__1
          | Specialization_cost.Cannot_specialize { reason = x__1 } -> f__2 x__1)
          (fun spec_cost ->
            let () =
              if not (Flambda_features.match_in_match ())
              then
                Misc.fatal_errorf
                  "Cannot specialize continuations (due to command line \
                   arguments), this code path should not have been reached."
              else ()
            in
            let lifting_budget =
              Downwards_acc.get_continuation_lifting_budget dacc
            in
            let lifting_cost =
              Downwards_env.cost_of_lifting_continuations_out_of_current_one
                denv
            in
            if
              not
                (lifting_budget > 0 && Stdlib.( <= ) lifting_cost lifting_budget)
            then `Insufficient_lifting_budget
            else
              let join_analysis_result0 =
                match Downwards_env.join_analysis denv with
                | Some join_analysis -> (
                  match
                    Flambda2_types.Join_analysis.simple_refined_at_join
                      join_analysis
                      (Downwards_env.typing_env denv)
                      scrutinee0
                  with
                  | Flambda2_types.Join_analysis.Not_refined_at_join ->
                    `Not_enough_join_info
                  | Flambda2_types.Join_analysis.Invariant_in_all_uses _ ->
                    `No_reason_to_spec
                  | Flambda2_types.Join_analysis.Variable_refined_at_these_uses
                      var_analysis ->
                    let specialized, generic =
                      Flambda2_types.Join_analysis.Variable_refined_at_join
                      .fold_values_at_uses
                        (fun id value pat ->
                          let specialized, generic = pat in
                          match value with
                          | Or_unknown.Known _ ->
                            ( Apply_cont_rewrite_id.Set.add id specialized,
                              generic )
                          | Or_unknown.Unknown ->
                            ( specialized,
                              Apply_cont_rewrite_id.Set.add id generic ))
                        var_analysis
                        ( Apply_cont_rewrite_id.Set.empty,
                          Apply_cont_rewrite_id.Set.empty )
                    in
                    let n = Apply_cont_rewrite_id.Set.cardinal generic in
                    if n = 0 || n = 1
                    then `Spec (join_analysis, specialized, generic)
                    else if Apply_cont_rewrite_id.Set.is_empty specialized
                    then `All_unknown
                    else `Too_many_unknown_uses)
                | None -> `Not_enough_join_info
              in
              match join_analysis_result0 with
              | `Not_enough_join_info -> `Not_enough_join_info
              | `No_reason_to_spec -> `No_reason_to_spec
              | `Spec (join_analysis, specialized, generic) ->
                let cost_metrics =
                  Specialization_cost.cost_metrics
                    (Downwards_env.typing_env denv)
                    switch join_analysis specialized generic spec_cost
                in
                let final_cost =
                  Cost_metrics.evaluate
                    (Downwards_env.inlining_arguments denv)
                    cost_metrics
                in
                let threshold =
                  Flambda_features.Expert.cont_spec_threshold ()
                in
                if
                  Stdlib.( < ) (Float.compare threshold 0.) 0
                  || Float.compare final_cost threshold > 0
                then `Too_costly
                else `Specialized (continuation, lifting_cost)
              | `All_unknown -> `All_unknown
              | `Too_many_unknown_uses -> `Too_many_unknown_uses)
          (fun reason ->
            match reason with
            | Specialization_cost.Specialization_disabled -> `Disabled
            | Specialization_cost.At_toplevel -> `Toplevel
            | Specialization_cost.Contains_static_consts -> `Cannot_specialize
            | Specialization_cost.Contains_set_of_closures -> `Cannot_specialize)
          (Downwards_env.specialization_cost denv))
    (fun _ ->
      Misc.fatal_errorf
        "[Are_lifting_cont] values in the dacc cannot be [Lifting_out_of _] \
         when going downwards through a [Switch] expression. See the \
         explanation in [are_lifting_conts.mli].")
    (Downwards_acc.are_lifting_conts dacc)

(** val decide_continuation_specialization : Downwards_acc.t -> Flambda.Switch.t
    -> Simple.t ->
    [ `Disabled | `Single_use | `Exn_handler | `Toplevel | `All_unknown |
     `No_reason_to_spec | `Not_lifting | `Cannot_specialize |
     `Insufficient_lifting_budget | `Not_enough_join_info |
     `Too_many_unknown_uses | `Too_costly | `Specialized of Continuation.t * int
     ] coq_M **)

let decide_continuation_specialization dacc switch scrutinee0 =
  (fun x__1 x__2 x__3 x__4 x__5 ->
    Profile.record_with_counters ?accumulate:x__1 x__2 x__3 x__4 x__5)
    (Some true)
    (fun result ->
      let counters = Profile.Counters.create () in
      match result with
      | `Disabled -> counters
      | `Single_use -> counters
      | `Exn_handler -> counters
      | `Toplevel -> counters
      | `All_unknown -> Profile.Counters.incr "all_unknown" counters
      | `No_reason_to_spec -> Profile.Counters.incr "no_reason" counters
      | `Not_lifting -> Profile.Counters.incr "not_lifting" counters
      | `Cannot_specialize -> Profile.Counters.incr "cannot_spec" counters
      | `Insufficient_lifting_budget ->
        Profile.Counters.incr "no_lifting_budget" counters
      | `Not_enough_join_info -> Profile.Counters.incr "no_join_info" counters
      | `Too_many_unknown_uses ->
        Profile.Counters.incr "too_much_unknown" counters
      | `Too_costly -> Profile.Counters.incr "not_beneficial" counters
      | `Specialized (_, _) -> Profile.Counters.incr "specialized" counters)
    "continuation_specialization"
    (fun _ -> decide_continuation_specialization0 dacc switch scrutinee0)
    ()

(** val simplify_switch : Downwards_acc.t -> Flambda.Switch.t ->
    Simplified_expr.t down_to_up -> (Simplified_expr.t * Downwards_acc.t) coq_M
    **)

let simplify_switch dacc switch down_to_up0 =
  let scrutinee0 = Flambda.Switch.scrutinee switch in
  let scrutinee_ty0, scrutinee1 =
    Simplify_simple.simplify_simple dacc scrutinee0 Name_mode.normal
  in
  let dacc_before_switch = dacc in
  let typing_env_at_use = Downwards_acc.typing_env dacc in
  let arms0 =
    Target_ocaml_int.Map.filter_map
      (fun arm action ->
        let shape = Flambda2_types.this_naked_immediate arm in
        match Flambda2_types.meet typing_env_at_use scrutinee_ty0 shape with
        | Or_bottom.Ok p ->
          let _, env_at_use = p in
          Some (action, env_at_use)
        | Or_bottom.Bottom -> None)
      (Flambda.Switch.arms switch)
  in
  match Target_ocaml_int.Map.get_singleton arms0 with
  | Some p ->
    let _, p0 = p in
    let arm, env_at_use = p0 in
    let denv_at_use =
      Downwards_env.with_typing_env (Downwards_acc.denv dacc) env_at_use
    in
    let dacc0 = Downwards_acc.with_denv dacc denv_at_use in
    Simplify_apply_cont_expr.simplify_apply_cont dacc0 (Switch_arm.action arm)
      (fun dacc1 simplified_expr ->
        down_to_up0 dacc1
          (Simplified_expr.notify_removed Removed_operations.branch
             simplified_expr))
  | None ->
    let arms1, dacc0 =
      Target_ocaml_int.Map.fold simplify_arm arms0
        (Target_ocaml_int.Map.empty, dacc)
    in
    let dacc1 =
      if Stdlib.( <= ) (Target_ocaml_int.Map.cardinal arms1) 1
      then dacc0
      else
        Downwards_acc.map_flow_acc dacc0
          (Flow.Acc.add_used_in_current_handler (Simple.free_names scrutinee1))
    in
    let condition_dbg0 =
      Downwards_env.add_inlined_debuginfo (Downwards_acc.denv dacc1)
        (Flambda.Switch.condition_dbg switch)
    in
    let dacc2 =
      match decide_continuation_specialization dacc1 switch scrutinee1 with
      | `Disabled -> dacc1
      | `Single_use -> dacc1
      | `Exn_handler -> dacc1
      | `Toplevel -> dacc1
      | `All_unknown -> dacc1
      | `No_reason_to_spec -> dacc1
      | `Not_lifting -> dacc1
      | `Cannot_specialize -> dacc1
      | `Insufficient_lifting_budget -> dacc1
      | `Not_enough_join_info -> dacc1
      | `Too_many_unknown_uses -> dacc1
      | `Too_costly -> dacc1
      | `Specialized (continuation, lifting_cost) ->
        let dacc2 =
          Downwards_acc.decrease_continuation_lifting_budget dacc1 lifting_cost
        in
        let dacc3 =
          Downwards_acc.with_are_lifting_conts dacc2
            (Are_lifting_conts.lift_continuations_out_of continuation)
        in
        let dacc4 =
          Downwards_acc.add_continuation_to_specialize dacc3 continuation
        in
        dacc4
    in
    let shareable_constants0 =
      Downwards_acc.shareable_constants dacc_before_switch
    in
    let typing_env_before_switch0 =
      Downwards_acc.typing_env dacc_before_switch
    in
    let cse_before_switch0 =
      Downwards_env.cse (Downwards_acc.denv dacc_before_switch)
    in
    down_to_up0 dacc2
      (Simplified_expr.simplified_switch arms1 condition_dbg0 scrutinee1
         scrutinee_ty0 shareable_constants0 typing_env_before_switch0
         cse_before_switch0)
