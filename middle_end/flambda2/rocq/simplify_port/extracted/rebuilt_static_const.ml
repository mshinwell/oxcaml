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
   middle_end/flambda2/rocq/simplify_port/Rebuilt_static_const.v, which follows
   middle_end/flambda2/simplify/rebuilt_static_const.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Flambda
module ART = Are_rebuilding_terms
module SC = Static_const
open Port_monad

type t =
  | Normal of
      { const : Static_const_or_code.t;
        free_names : Name_occurrences.t;
        cost_metrics : Cost_metrics.t
      }
  | Block_not_rebuilt of
      { free_names : Name_occurrences.t;
        cost_metrics : Cost_metrics.t
      }
  | Set_of_closures_not_rebuilt of
      { free_names : Name_occurrences.t;
        cost_metrics : Cost_metrics.t
      }
  | Code_not_rebuilt of Non_constructed_code.t

type rebuilt_static_const = t

(** val is_block : t -> bool coq_M **)

let is_block t0 =
  (fun f__1 f__2 f__3 f__4 x__0 ->
    match (x__0 : rebuilt_static_const) with
    | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
      f__1 x__1 x__2 x__3
    | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__2 x__1 x__2
    | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__3 x__1 x__2
    | Code_not_rebuilt x__1 -> f__4 x__1)
    (fun const _ _ -> Static_const_or_code.is_block const)
    (fun _ _ -> true)
    (fun _ _ -> false)
    (fun _ -> false)
    t0

(** val is_set_of_closures : t -> bool coq_M **)

let is_set_of_closures t0 =
  (fun f__1 f__2 f__3 f__4 x__0 ->
    match (x__0 : rebuilt_static_const) with
    | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
      f__1 x__1 x__2 x__3
    | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__2 x__1 x__2
    | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__3 x__1 x__2
    | Code_not_rebuilt x__1 -> f__4 x__1)
    (fun const _ _ -> Static_const_or_code.is_set_of_closures const)
    (fun _ _ -> false)
    (fun _ _ -> true)
    (fun _ -> false)
    t0

(** val is_code : t -> bool coq_M **)

let is_code t0 =
  (fun f__1 f__2 f__3 f__4 x__0 ->
    match (x__0 : rebuilt_static_const) with
    | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
      f__1 x__1 x__2 x__3
    | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__2 x__1 x__2
    | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__3 x__1 x__2
    | Code_not_rebuilt x__1 -> f__4 x__1)
    (fun const _ _ -> Static_const_or_code.is_code const)
    (fun _ _ -> false)
    (fun _ _ -> false)
    (fun _ -> true)
    t0

(** val cost_metrics : t -> Cost_metrics.t coq_M **)

let cost_metrics t0 =
  (fun f__1 f__2 f__3 f__4 x__0 ->
    match (x__0 : rebuilt_static_const) with
    | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
      f__1 x__1 x__2 x__3
    | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__2 x__1 x__2
    | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__3 x__1 x__2
    | Code_not_rebuilt x__1 -> f__4 x__1)
    (fun _ _ cost_metrics0 -> cost_metrics0)
    (fun _ cost_metrics0 -> cost_metrics0)
    (fun _ cost_metrics0 -> cost_metrics0)
    (fun _ -> Cost_metrics.zero)
    t0

(** val create_normal_non_code : Cost_metrics.t -> SC.t -> t coq_M **)

let create_normal_non_code cost_metrics0 const =
  let free_names0 = Static_const.free_names const in
  let const0 = Static_const_or_code.create_static_const const in
  (fun (x__1, x__2, x__3) ->
    (Normal { const = x__1; free_names = x__2; cost_metrics = x__3 }
      : rebuilt_static_const))
    (const0, free_names0, cost_metrics0)

(** val create_code : ART.t -> Rebuilt_expr.Function_params_and_body.t ->
    Name_occurrences.t -> (t * Code.t option) Code_metadata.create_type **)

let create_code are_rebuilding params_and_body free_names_of_params_and_body
    code_id newer_version_of params_arity param_modes first_complex_local_param
    result_arity result_types result_mode stub inline zero_alloc_attribute
    poll_attribute regalloc_attribute regalloc_param_attribute cold is_a_functor
    is_opaque recursive cost_metrics0 inlining_arguments dbg is_tupled
    is_my_closure_used inlining_decision absolute_history relative_history
    loopify =
  if ART.do_not_rebuild_terms are_rebuilding
  then
    Code_metadata.createk
      (fun code_metadata ->
        ( Code_not_rebuilt
            (Non_constructed_code.create_with_metadata
               free_names_of_params_and_body code_metadata),
          None ))
      code_id newer_version_of params_arity param_modes
      first_complex_local_param result_arity result_types result_mode stub
      inline zero_alloc_attribute poll_attribute regalloc_attribute
      regalloc_param_attribute cold is_a_functor is_opaque recursive
      cost_metrics0 inlining_arguments dbg is_tupled is_my_closure_used
      inlining_decision absolute_history relative_history loopify
  else
    let params_and_body0 =
      Rebuilt_expr.Function_params_and_body.to_function_params_and_body
        params_and_body are_rebuilding
    in
    Code_metadata.createk
      (fun code_metadata ->
        let code =
          Code.create_with_metadata params_and_body0
            free_names_of_params_and_body code_metadata
        in
        let free_names0 = Code.free_names code in
        let const = Static_const_or_code.create_code code in
        ( (fun (x__1, x__2, x__3) ->
            (Normal { const = x__1; free_names = x__2; cost_metrics = x__3 }
              : rebuilt_static_const))
            (const, free_names0, Cost_metrics.zero),
          Some code ))
      code_id newer_version_of params_arity param_modes
      first_complex_local_param result_arity result_types result_mode stub
      inline zero_alloc_attribute poll_attribute regalloc_attribute
      regalloc_param_attribute cold is_a_functor is_opaque recursive
      cost_metrics0 inlining_arguments dbg is_tupled is_my_closure_used
      inlining_decision absolute_history relative_history loopify

(** val create_code' : Code.t -> t coq_M **)

let create_code' code =
  let free_names0 = Code.free_names code in
  let const = Static_const_or_code.create_code code in
  (fun (x__1, x__2, x__3) ->
    (Normal { const = x__1; free_names = x__2; cost_metrics = x__3 }
      : rebuilt_static_const))
    (const, free_names0, Cost_metrics.zero)

(** val find_code_characteristics : (Code_id.t -> Code_metadata.t coq_M) ->
    Code_id.t -> Cost_metrics.code_characteristics coq_M **)

let find_code_characteristics find_code_metadata code_id =
  let code_metadata = find_code_metadata code_id in
  let function_slot_size0 = Code_metadata.function_slot_size code_metadata in
  let cost_metrics0 = Code_metadata.cost_metrics code_metadata in
  { Cost_metrics.cost_metrics = cost_metrics0;
    Cost_metrics.function_slot_size = function_slot_size0
  }

(** val create_set_of_closures : ART.t -> (Code_id.t -> Code_metadata.t coq_M)
    -> Set_of_closures.t -> t coq_M **)

let create_set_of_closures are_rebuilding find_code_metadata set =
  let free_names0 = Set_of_closures.free_names set in
  let cost_metrics0 =
    Cost_metrics.set_of_closures
      (find_code_characteristics find_code_metadata)
      set
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (free_names0, cost_metrics0)
  else
    (fun (x__1, x__2, x__3) ->
      (Normal { const = x__1; free_names = x__2; cost_metrics = x__3 }
        : rebuilt_static_const))
      ( Static_const_or_code.create_static_const (SC.set_of_closures set),
        free_names0,
        cost_metrics0 )

(** val free_names_of_fields : Simple.With_debuginfo.t list ->
    Name_occurrences.t coq_M **)

let free_names_of_fields fields =
  ListLabels.fold_left
    (fun free_names0 field ->
      Name_occurrences.union free_names0
        (Simple.With_debuginfo.free_names field))
    Name_occurrences.empty fields

(** val create_block : ART.t -> Tag.Scannable.t -> Mutability.t ->
    Flambda_kind.Scannable_block_shape.t -> Simple.With_debuginfo.t list -> t
    coq_M **)

let create_block are_rebuilding tag is_mutable shape fields =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.block (List.length fields))
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    let free_names0 = free_names_of_fields fields in
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (free_names0, cost_metrics0)
  else
    create_normal_non_code cost_metrics0 (SC.block tag is_mutable shape fields)

(** val create_boxed_float32 : ART.t -> Target_system.Machine_width.t ->
    Numeric_types.Float32_by_bit_pattern.t Or_variable.t -> t coq_M **)

let create_boxed_float32 are_rebuilding machine_width or_var =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.box_number machine_width Naked_float32)
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Or_variable.free_names or_var, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.boxed_float32 or_var)

(** val create_boxed_float : ART.t -> Target_system.Machine_width.t ->
    Numeric_types.Float_by_bit_pattern.t Or_variable.t -> t coq_M **)

let create_boxed_float are_rebuilding machine_width or_var =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.box_number machine_width Naked_float)
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Or_variable.free_names or_var, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.boxed_float or_var)

(** val create_boxed_int32 : ART.t -> Target_system.Machine_width.t -> Int32.t
    Or_variable.t -> t coq_M **)

let create_boxed_int32 are_rebuilding machine_width or_var =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.box_number machine_width Naked_int32)
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Or_variable.free_names or_var, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.boxed_int32 or_var)

(** val create_boxed_int64 : ART.t -> Target_system.Machine_width.t -> Int64.t
    Or_variable.t -> t coq_M **)

let create_boxed_int64 are_rebuilding machine_width or_var =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.box_number machine_width Naked_int64)
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Or_variable.free_names or_var, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.boxed_int64 or_var)

(** val create_boxed_nativeint : ART.t -> Target_system.Machine_width.t ->
    Targetint_32_64.t Or_variable.t -> t coq_M **)

let create_boxed_nativeint are_rebuilding machine_width or_var =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.box_number machine_width Naked_nativeint)
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Or_variable.free_names or_var, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.boxed_nativeint or_var)

(** val create_boxed_vec128 : ART.t -> Target_system.Machine_width.t ->
    Vector_types.Vec128.Bit_pattern.t Or_variable.t -> t coq_M **)

let create_boxed_vec128 are_rebuilding machine_width or_var =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.box_number machine_width Naked_vec128)
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Or_variable.free_names or_var, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.boxed_vec128 or_var)

(** val create_boxed_vec256 : ART.t -> Target_system.Machine_width.t ->
    Vector_types.Vec256.Bit_pattern.t Or_variable.t -> t coq_M **)

let create_boxed_vec256 are_rebuilding machine_width or_var =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.box_number machine_width Naked_vec256)
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Or_variable.free_names or_var, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.boxed_vec256 or_var)

(** val create_boxed_vec512 : ART.t -> Target_system.Machine_width.t ->
    Vector_types.Vec512.Bit_pattern.t Or_variable.t -> t coq_M **)

let create_boxed_vec512 are_rebuilding machine_width or_var =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.box_number machine_width Naked_vec512)
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Or_variable.free_names or_var, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.boxed_vec512 or_var)

(** val create_boxed_mask : ART.t -> Target_system.Machine_width.t ->
    Vector_types.Mask.Bit_pattern.t Or_variable.t -> t coq_M **)

let create_boxed_mask are_rebuilding machine_width or_var =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.box_number machine_width Naked_mask)
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Or_variable.free_names or_var, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.boxed_mask or_var)

(** val create_immutable_float_block : ART.t ->
    Numeric_types.Float_by_bit_pattern.t Or_variable.t list -> t coq_M **)

let create_immutable_float_block are_rebuilding fields =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.array (List.length fields))
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    let free_names0 =
      ListLabels.fold_left
        (fun free_names0 field ->
          Name_occurrences.union free_names0 (Or_variable.free_names field))
        Name_occurrences.empty fields
    in
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (free_names0, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.immutable_float_block fields)

(** val create_immutable_naked_number_array : ('a1 Or_variable.t list -> SC.t
    coq_M) -> ART.t -> 'a1 Or_variable.t list -> t coq_M **)

let create_immutable_naked_number_array builder are_rebuilding fields =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.array (List.length fields))
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    let free_names0 =
      ListLabels.fold_left
        (fun free_names0 field ->
          Name_occurrences.union free_names0 (Or_variable.free_names field))
        Name_occurrences.empty fields
    in
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (free_names0, cost_metrics0)
  else create_normal_non_code cost_metrics0 (builder fields)

(** val create_immutable_float_array : ART.t ->
    Numeric_types.Float_by_bit_pattern.t Or_variable.t list -> t coq_M **)

let create_immutable_float_array =
  create_immutable_naked_number_array SC.immutable_float_array

(** val create_immutable_float32_array : ART.t ->
    Numeric_types.Float32_by_bit_pattern.t Or_variable.t list -> t coq_M **)

let create_immutable_float32_array =
  create_immutable_naked_number_array SC.immutable_float32_array

(** val create_immutable_int_array : ART.t -> Target_ocaml_int.t Or_variable.t
    list -> t coq_M **)

let create_immutable_int_array =
  create_immutable_naked_number_array SC.immutable_int_array

(** val create_immutable_int8_array : ART.t -> Numeric_types.Int8.t
    Or_variable.t list -> t coq_M **)

let create_immutable_int8_array =
  create_immutable_naked_number_array SC.immutable_int8_array

(** val create_immutable_int16_array : ART.t -> Numeric_types.Int16.t
    Or_variable.t list -> t coq_M **)

let create_immutable_int16_array =
  create_immutable_naked_number_array SC.immutable_int16_array

(** val create_immutable_int32_array : ART.t -> Int32.t Or_variable.t list -> t
    coq_M **)

let create_immutable_int32_array =
  create_immutable_naked_number_array SC.immutable_int32_array

(** val create_immutable_int64_array : ART.t -> Int64.t Or_variable.t list -> t
    coq_M **)

let create_immutable_int64_array =
  create_immutable_naked_number_array SC.immutable_int64_array

(** val create_immutable_nativeint_array : ART.t -> Targetint_32_64.t
    Or_variable.t list -> t coq_M **)

let create_immutable_nativeint_array =
  create_immutable_naked_number_array SC.immutable_nativeint_array

(** val create_immutable_vec128_array : ART.t ->
    Vector_types.Vec128.Bit_pattern.t Or_variable.t list -> t coq_M **)

let create_immutable_vec128_array =
  create_immutable_naked_number_array SC.immutable_vec128_array

(** val create_immutable_vec256_array : ART.t ->
    Vector_types.Vec256.Bit_pattern.t Or_variable.t list -> t coq_M **)

let create_immutable_vec256_array =
  create_immutable_naked_number_array SC.immutable_vec256_array

(** val create_immutable_vec512_array : ART.t ->
    Vector_types.Vec512.Bit_pattern.t Or_variable.t list -> t coq_M **)

let create_immutable_vec512_array =
  create_immutable_naked_number_array SC.immutable_vec512_array

(** val create_immutable_mask_array : ART.t -> Vector_types.Mask.Bit_pattern.t
    Or_variable.t list -> t coq_M **)

let create_immutable_mask_array =
  create_immutable_naked_number_array SC.immutable_mask_array

(** val create_immutable_value_array : ART.t -> Simple.With_debuginfo.t list ->
    t coq_M **)

let create_immutable_value_array are_rebuilding fields =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.array (List.length fields))
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    let free_names0 = free_names_of_fields fields in
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (free_names0, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.immutable_value_array fields)

(** val create_empty_array : ART.t -> Empty_array_kind.t -> t coq_M **)

let create_empty_array are_rebuilding array_kind =
  let cost_metrics0 = Cost_metrics.from_size (Code_size.array 0) in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Name_occurrences.empty, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.empty_array array_kind)

(** val create_immutable_string : ART.t -> string -> t coq_M **)

let create_immutable_string are_rebuilding str =
  let cost_metrics0 =
    Cost_metrics.from_size (Code_size.of_int (String.length str))
  in
  if ART.do_not_rebuild_terms are_rebuilding
  then
    (fun (x__1, x__2) ->
      (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
        : rebuilt_static_const))
      (Name_occurrences.empty, cost_metrics0)
  else create_normal_non_code cost_metrics0 (SC.immutable_string str)

(** val map_set_of_closures : t -> (Code_id.t -> Code_metadata.t coq_M) ->
    (Set_of_closures.t -> Set_of_closures.t coq_M) -> t coq_M **)

let map_set_of_closures t0 find_code_metadata f =
  (fun f__1 f__2 f__3 f__4 x__0 ->
    match (x__0 : rebuilt_static_const) with
    | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
      f__1 x__1 x__2 x__3
    | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__2 x__1 x__2
    | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__3 x__1 x__2
    | Code_not_rebuilt x__1 -> f__4 x__1)
    (fun const _ _ ->
      match const with
      | Code _ -> t0
      | Deleted_code -> t0
      | Static_const const0 -> (
        match const0 with
        | Set_of_closures set_of_closures ->
          let set_of_closures0 = f set_of_closures in
          let cost_metrics0 =
            Cost_metrics.set_of_closures
              (find_code_characteristics find_code_metadata)
              set_of_closures0
          in
          let free_names0 = Set_of_closures.free_names set_of_closures0 in
          let const1 =
            Static_const_or_code.create_static_const
              (SC.set_of_closures set_of_closures0)
          in
          (fun (x__1, x__2, x__3) ->
            (Normal { const = x__1; free_names = x__2; cost_metrics = x__3 }
              : rebuilt_static_const))
            (const1, free_names0, cost_metrics0)
        | Block (_, _, _, _) -> t0
        | Boxed_float32 _ -> t0
        | Boxed_float _ -> t0
        | Boxed_int32 _ -> t0
        | Boxed_int64 _ -> t0
        | Boxed_nativeint _ -> t0
        | Boxed_vec128 _ -> t0
        | Boxed_vec256 _ -> t0
        | Boxed_vec512 _ -> t0
        | Boxed_mask _ -> t0
        | Immutable_float_block _ -> t0
        | Immutable_float_array _ -> t0
        | Immutable_float32_array _ -> t0
        | Immutable_int_array _ -> t0
        | Immutable_int8_array _ -> t0
        | Immutable_int16_array _ -> t0
        | Immutable_int32_array _ -> t0
        | Immutable_int64_array _ -> t0
        | Immutable_nativeint_array _ -> t0
        | Immutable_vec128_array _ -> t0
        | Immutable_vec256_array _ -> t0
        | Immutable_vec512_array _ -> t0
        | Immutable_mask_array _ -> t0
        | Immutable_value_array _ -> t0
        | Empty_array _ -> t0
        | Immutable_string _ -> t0))
    (fun _ _ -> t0)
    (fun _ _ -> t0)
    (fun _ -> t0)
    t0

(** val free_names : t -> Name_occurrences.t coq_M **)

let free_names t0 =
  (fun f__1 f__2 f__3 f__4 x__0 ->
    match (x__0 : rebuilt_static_const) with
    | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
      f__1 x__1 x__2 x__3
    | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__2 x__1 x__2
    | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__3 x__1 x__2
    | Code_not_rebuilt x__1 -> f__4 x__1)
    (fun _ free_names0 _ -> free_names0)
    (fun free_names0 _ -> free_names0)
    (fun free_names0 _ -> free_names0)
    (fun code -> Non_constructed_code.free_names code)
    t0

(** val is_fully_static : t -> bool coq_M **)

let is_fully_static t0 = Name_occurrences.no_variables (free_names t0)

(** val to_const : t -> Static_const_or_code.t option coq_M **)

let to_const t0 =
  (fun f__1 f__2 f__3 f__4 x__0 ->
    match (x__0 : rebuilt_static_const) with
    | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
      f__1 x__1 x__2 x__3
    | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__2 x__1 x__2
    | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__3 x__1 x__2
    | Code_not_rebuilt x__1 -> f__4 x__1)
    (fun const _ _ -> Some const)
    (fun _ _ -> None)
    (fun _ _ -> None)
    (fun _ -> None)
    t0

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  (fun f__1 f__2 f__3 f__4 x__0 ->
    match (x__0 : rebuilt_static_const) with
    | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
      f__1 x__1 x__2 x__3
    | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__2 x__1 x__2
    | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__3 x__1 x__2
    | Code_not_rebuilt x__1 -> f__4 x__1)
    (fun const _ _ -> Static_const_or_code.print ppf const)
    (fun _ _ -> Format.fprintf ppf "Block_not_rebuilt")
    (fun _ _ -> Format.fprintf ppf "Set_of_closures_not_rebuilt")
    (fun code ->
      Format.fprintf ppf "@[<hov 1>(Code_not_rebuilt@ %a)@]"
        Non_constructed_code.print code)
    t0

(** val deleted_code : t **)

let deleted_code =
  (fun (x__1, x__2, x__3) ->
    (Normal { const = x__1; free_names = x__2; cost_metrics = x__3 }
      : rebuilt_static_const))
    ( Static_const_or_code.deleted_code,
      Name_occurrences.empty,
      Cost_metrics.zero )

(** val make_code_deleted : t -> Code_id.Set.t -> t coq_M **)

let make_code_deleted t0 if_code_id_is_member_of =
  (fun f__1 f__2 f__3 f__4 x__0 ->
    match (x__0 : rebuilt_static_const) with
    | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
      f__1 x__1 x__2 x__3
    | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__2 x__1 x__2
    | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
      f__3 x__1 x__2
    | Code_not_rebuilt x__1 -> f__4 x__1)
    (fun const _ _ ->
      match Static_const_or_code.to_code const with
      | Some code ->
        if Code_id.Set.mem (Code.code_id code) if_code_id_is_member_of
        then deleted_code
        else t0
      | None -> t0)
    (fun _ _ -> t0)
    (fun _ _ -> t0)
    (fun code ->
      if
        Code_id.Set.mem
          (Non_constructed_code.code_id code)
          if_code_id_is_member_of
      then deleted_code
      else t0)
    t0

module Group = struct
  type t =
    { consts : rebuilt_static_const list;
      mutable free_names : Name_occurrences.t Or_unknown.t
    }

  (** val mk_t : rebuilt_static_const list -> Name_occurrences.t Or_unknown.t ->
      t coq_M **)

  let mk_t = fun consts free_names -> { consts; free_names }

  (** val consts : t -> rebuilt_static_const list **)

  let consts = fun t -> t.consts

  (** val get_free_names : t -> Name_occurrences.t Or_unknown.t coq_M **)

  let get_free_names = fun t -> t.free_names

  (** val set_free_names : t -> Name_occurrences.t Or_unknown.t -> unit coq_M **)

  let set_free_names = fun t free_names -> t.free_names <- free_names

  (** val empty : t **)

  let empty = { consts = []; free_names = Known Name_occurrences.empty }

  (** val create : rebuilt_static_const list -> t coq_M **)

  let create consts0 = mk_t consts0 Or_unknown.Unknown

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    let consts0 = consts t0 in
    Format.fprintf ppf "@[<hov 1>(%a)@]"
      ((fun x__1 x__2 x__3 x__4 ->
         Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
         (Some Format.pp_print_space) print)
      consts0

  (** val free_names : t -> Name_occurrences.t coq_M **)

  let free_names t0 =
    match get_free_names t0 with
    | Or_unknown.Known free_names0 -> free_names0
    | Or_unknown.Unknown ->
      let free_names0 =
        ListLabels.fold_left
          (fun free_names_acc const ->
            Name_occurrences.union free_names_acc (free_names const))
          Name_occurrences.empty (consts t0)
      in
      let () = set_free_names t0 (Or_unknown.Known free_names0) in
      free_names0

  (** val cost_metrics : t -> Cost_metrics.t coq_M **)

  let cost_metrics t0 =
    List.fold_left
      (fun cm const -> Cost_metrics.( + ) cm (cost_metrics const))
      Cost_metrics.zero (consts t0)

  (** val to_named : t -> Named.t coq_M **)

  let to_named t0 =
    Named.create_static_consts
      (Static_const_group.create
         (ListLabels.map
            (fun const ->
              (fun f__1 f__2 f__3 f__4 x__0 ->
                match (x__0 : rebuilt_static_const) with
                | Normal
                    { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
                  f__1 x__1 x__2 x__3
                | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
                  ->
                  f__2 x__1 x__2
                | Set_of_closures_not_rebuilt
                    { free_names = x__1; cost_metrics = x__2 } ->
                  f__3 x__1 x__2
                | Code_not_rebuilt x__1 -> f__4 x__1)
                (fun const0 _ _ -> const0)
                (fun _ _ ->
                  Misc.fatal_error
                    "Cannot extract static constants when not rebuilding terms")
                (fun _ _ ->
                  Misc.fatal_error
                    "Cannot extract static constants when not rebuilding terms")
                (fun _ ->
                  Misc.fatal_error
                    "Cannot extract static constants when not rebuilding terms")
                const)
            (consts t0)))

  (** val pieces_of_code_for_cmx : t -> Code.t Code_id.Map.t coq_M **)

  let pieces_of_code_for_cmx t0 =
    Code_id.Map.of_list
      (ListLabels.filter_map
         (fun const ->
           (fun f__1 f__2 f__3 f__4 x__0 ->
             match (x__0 : rebuilt_static_const) with
             | Normal { const = x__1; free_names = x__2; cost_metrics = x__3 }
               ->
               f__1 x__1 x__2 x__3
             | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } ->
               f__2 x__1 x__2
             | Set_of_closures_not_rebuilt
                 { free_names = x__1; cost_metrics = x__2 } ->
               f__3 x__1 x__2
             | Code_not_rebuilt x__1 -> f__4 x__1)
             (fun const0 _ _ ->
               match Static_const_or_code.to_code const0 with
               | Some code -> Some (Code.code_id code, code)
               | None -> None)
             (fun _ _ -> None)
             (fun _ _ -> None)
             (fun _ -> None)
             const)
         (consts t0))

  (** val function_params_and_body_for_code_not_rebuilt :
      Function_params_and_body.t lazy_t **)

  let function_params_and_body_for_code_not_rebuilt =
    lazy
      (Function_params_and_body.create
         ~return_continuation:(Continuation.create ~sort:Return ())
         ~exn_continuation:(Continuation.create ()) Bound_parameters.empty
         ~body:(Expr.create_invalid Code_not_rebuilt)
         ~free_names_of_body:Unknown
         ~my_closure:(Variable.create "my_closure" Flambda_kind.value)
         ~my_alloc_mode:
           (Alloc_mode.For_applications.not_alloc_stack
              ~alloc_region:
                (Variable.create "my_alloc_region" Flambda_kind.region))
         ~my_depth:(Variable.create "my_depth" Flambda_kind.rec_info))

  (** val pieces_of_code_including_those_not_rebuilt : t -> Code.t Code_id.Map.t
      coq_M **)

  let pieces_of_code_including_those_not_rebuilt t0 =
    Code_id.Map.of_list
      (List.map
         (fun code -> Code.code_id code, code)
         (ListLabels.filter_map
            (fun const ->
              (fun f__1 f__2 f__3 f__4 x__0 ->
                match (x__0 : rebuilt_static_const) with
                | Normal
                    { const = x__1; free_names = x__2; cost_metrics = x__3 } ->
                  f__1 x__1 x__2 x__3
                | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 }
                  ->
                  f__2 x__1 x__2
                | Set_of_closures_not_rebuilt
                    { free_names = x__1; cost_metrics = x__2 } ->
                  f__3 x__1 x__2
                | Code_not_rebuilt x__1 -> f__4 x__1)
                (fun const0 _ _ -> Static_const_or_code.to_code const0)
                (fun _ _ -> None)
                (fun _ _ -> None)
                (fun code ->
                  let params_and_body =
                    Lazy.force function_params_and_body_for_code_not_rebuilt
                  in
                  Some
                    (Code.create_with_metadata params_and_body
                       Name_occurrences.empty
                       (Non_constructed_code.code_metadata code)))
                const)
            (consts t0)))

  (** val map : t -> (rebuilt_static_const -> rebuilt_static_const coq_M) -> t
      coq_M **)

  let map t0 f =
    let changed = ref false in
    let consts0 =
      ListLabels.map
        (fun const ->
          let const' = f const in
          let () = if const != const' then changed := true else () in
          const')
        (consts t0)
    in
    if not !changed then t0 else mk_t consts0 Or_unknown.Unknown

  (** val fold_left : t -> 'a1 -> ('a1 -> rebuilt_static_const -> 'a1 coq_M) ->
      'a1 coq_M **)

  let fold_left t0 init f = ListLabels.fold_left f init (consts t0)

  (** val add : rebuilt_static_const -> t -> t coq_M **)

  let add const t0 = mk_t (const :: consts t0) Or_unknown.Unknown

  (** val concat : t -> t -> t coq_M **)

  let concat t1 t2 =
    let free_names0 =
      let fn2 = get_free_names t2 in
      let fn1 = get_free_names t1 in
      match fn1 with
      | Or_unknown.Known free_names1 -> (
        match fn2 with
        | Or_unknown.Known free_names2 ->
          Or_unknown.Known (Name_occurrences.union free_names1 free_names2)
        | Or_unknown.Unknown -> Or_unknown.Unknown)
      | Or_unknown.Unknown -> (
        match fn2 with
        | Or_unknown.Known _ -> Or_unknown.Unknown
        | Or_unknown.Unknown -> Or_unknown.Unknown)
    in
    mk_t (consts t1 @ consts t2) free_names0

  (** val to_list : t -> rebuilt_static_const list coq_M **)

  let to_list = consts
end
