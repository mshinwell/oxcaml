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

(* This file follows middle_end/flambda2/simplify/rebuilt_static_const.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the arguments by place) is that of
   GUIDE.md; the Rocq form of the two types of the file (the fields of the
   inline records by place; the record with a mutable field abstract, with
   [mk_t], [consts], [get_free_names] and [set_free_names]) is written for
   this file. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Are_rebuilding_terms
  Bound_parameters Code Code_id Code_metadata Code_size Continuation
  Cost_metrics Empty_array_kind Flambda Flambda_kind Format Int32 Int64 List
  ListLabels Mutability Name_occurrences Non_constructed_code Numeric_types
  Or_unknown Or_variable Rebuilt_expr Simple Static_const String Tag
  Target_ocaml_int Target_system Targetint_32_64 Variable_ Vector_types.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 17 *)
(*OCAML
open! Flambda
OCAML*)
Import Flambda.
(* 18-19 *)
Module ART := Are_rebuilding_terms.
Module SC := Static_const.

(* 21-23: The cost metrics for sets of closures include the code size of
   their code_ids, like for non-lifted sets of closures. To avoid double
   counting, the cost metrics of [Code] bindings are zero. *)
(* 24-38 *)
(* PORT-GAP(type): the type has inline records. In Rocq it is the inductive
   type [t_], whose constructors take the fields by place; the OCaml
   definition is the compiler's text, which the directive of [t] puts at
   this place of the extracted file. *)
Inductive t_ : Type :=
| Normal :
    Static_const_or_code.t -> Name_occurrences.t -> Cost_metrics.t -> t_
| Block_not_rebuilt : Name_occurrences.t -> Cost_metrics.t -> t_
| Set_of_closures_not_rebuilt : Name_occurrences.t -> Cost_metrics.t -> t_
| Code_not_rebuilt : Non_constructed_code.t -> t_.
Extract Inductive t_ => "t"
  [ "(fun (x__1, x__2, x__3) -> (Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } : rebuilt_static_const))"
    "(fun (x__1, x__2) -> (Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } : rebuilt_static_const))"
    "(fun (x__1, x__2) -> (Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } : rebuilt_static_const))"
    "Code_not_rebuilt" ]
  "(fun f__1 f__2 f__3 f__4 x__0 -> match (x__0 : rebuilt_static_const) with Normal { const = x__1; free_names = x__2; cost_metrics = x__3 } -> f__1 x__1 x__2 x__3 | Block_not_rebuilt { free_names = x__1; cost_metrics = x__2 } -> f__2 x__1 x__2 | Set_of_closures_not_rebuilt { free_names = x__1; cost_metrics = x__2 } -> f__3 x__1 x__2 | Code_not_rebuilt x__1 -> f__4 x__1)".
Definition t : Type := t_.
Extract Constant t => "
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
".

(* 40 *)
Definition rebuilt_static_const : Type := t.

(* 42-46 *)
Definition is_block (t : Rebuilt_static_const.t) : M bool :=
  match t with
  | Normal const _ _ => Static_const_or_code.is_block const
  | Block_not_rebuilt _ _ => ret true
  | Set_of_closures_not_rebuilt _ _ | Code_not_rebuilt _ => ret false
  end.

(* 48-52 *)
Definition is_set_of_closures (t : Rebuilt_static_const.t) : M bool :=
  match t with
  | Normal const _ _ => Static_const_or_code.is_set_of_closures const
  | Set_of_closures_not_rebuilt _ _ => ret true
  | Code_not_rebuilt _ | Block_not_rebuilt _ _ => ret false
  end.

(* 54-58 *)
Definition is_code (t : Rebuilt_static_const.t) : M bool :=
  match t with
  | Normal const _ _ => Static_const_or_code.is_code const
  | Code_not_rebuilt _ => ret true
  | Set_of_closures_not_rebuilt _ _ | Block_not_rebuilt _ _ => ret false
  end.

(* 60-66 *)
Definition cost_metrics (t : Rebuilt_static_const.t) : M Cost_metrics.t :=
  match t with
  | Normal _ _ cost_metrics
  | Block_not_rebuilt _ cost_metrics
  | Set_of_closures_not_rebuilt _ cost_metrics =>
    ret cost_metrics
  | Code_not_rebuilt _ => ret Cost_metrics.zero
  end.

(* 68-73 *)
Definition create_normal_non_code (cost_metrics : Cost_metrics.t)
    (const : Static_const.t) : M t :=
  (* PORT-GAP(record-order): 70-71, calls in the fields [const] and
     [free_names]: the last field first. *)
  let! tmp1 := Static_const.free_names const in
  let! tmp2 := Static_const_or_code.create_static_const const in
  ret (Normal tmp2 tmp1 cost_metrics).

(* 75-98 *)
(* PORT-GAP(loose): the compiler's function has three parameters and gives
   back a function, [Code_metadata.createk (fun ...)], which waits for the
   27 arguments of [Code_metadata.create_type]; here these 27 arguments are
   parameters (under the names of the labels of that type), so that the
   test and the call of 85-86 are in the monad: they run when the last
   argument is there, not when the third is. *)
Definition create_code (are_rebuilding : ART.t)
    (params_and_body : Rebuilt_expr.Function_params_and_body.t)
    (free_names_of_params_and_body : Name_occurrences.t)
    : Code_metadata.create_type (t * option Code.t) :=
  fun code_id newer_version_of params_arity param_modes
      first_complex_local_param result_arity result_types result_mode stub
      inline zero_alloc_attribute poll_attribute regalloc_attribute
      regalloc_param_attribute cold is_a_functor is_opaque recursive
      cost_metrics inlining_arguments dbg is_tupled is_my_closure_used
      inlining_decision absolute_history relative_history loopify =>
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    Code_metadata.createk
      (fun code_metadata =>
        let! tmp2 :=
          Non_constructed_code.create_with_metadata
            free_names_of_params_and_body code_metadata
        in
        ret (Code_not_rebuilt tmp2, None))
      code_id newer_version_of params_arity param_modes
      first_complex_local_param result_arity result_types result_mode stub
      inline zero_alloc_attribute poll_attribute regalloc_attribute
      regalloc_param_attribute cold is_a_functor is_opaque recursive
      cost_metrics inlining_arguments dbg is_tupled is_my_closure_used
      inlining_decision absolute_history relative_history loopify
  else
    let* params_and_body :=
      Rebuilt_expr.Function_params_and_body.to_function_params_and_body
        params_and_body are_rebuilding
    in
    Code_metadata.createk
      (fun code_metadata =>
        let* code :=
          Code.create_with_metadata params_and_body
            free_names_of_params_and_body code_metadata
        in
        (* PORT-GAP(record-order): 94-95, calls in the fields [const] and
           [free_names]: the last field first. *)
        let! tmp2 := Code.free_names code in
        let! tmp3 := Static_const_or_code.create_code code in
        ret (Normal tmp3 tmp2 Cost_metrics.zero, Some code))
      code_id newer_version_of params_arity param_modes
      first_complex_local_param result_arity result_types result_mode stub
      inline zero_alloc_attribute poll_attribute regalloc_attribute
      regalloc_param_attribute cold is_a_functor is_opaque recursive
      cost_metrics inlining_arguments dbg is_tupled is_my_closure_used
      inlining_decision absolute_history relative_history loopify.

(* 100-105 *)
Definition create_code' (code : Code.t) : M t :=
  (* PORT-GAP(record-order): 102-103, calls in the fields [const] and
     [free_names]: the last field first. *)
  let! tmp1 := Code.free_names code in
  let! tmp2 := Static_const_or_code.create_code code in
  ret (Normal tmp2 tmp1 Cost_metrics.zero).

(* 107-112 *)
Definition find_code_characteristics
    (find_code_metadata : Code_id.t -> M Code_metadata.t)
    (code_id : Code_id.t) : M Cost_metrics.code_characteristics :=
  let* code_metadata := find_code_metadata code_id in
  (* PORT-GAP(record-order): 110-111, calls in the two fields: the last
     field first. *)
  let! tmp1 := Code_metadata.function_slot_size code_metadata in
  let! tmp2 := Code_metadata.cost_metrics code_metadata in
  ret
    {| Cost_metrics.cost_metrics := tmp2;
       Cost_metrics.function_slot_size := tmp1
    |}.

(* 114-129 *)
Definition create_set_of_closures (are_rebuilding : ART.t)
    (find_code_metadata : Code_id.t -> M Code_metadata.t)
    (set : Set_of_closures.t) : M t :=
  let* free_names := Set_of_closures.free_names set in
  let* cost_metrics :=
    Cost_metrics.set_of_closures
      (find_code_characteristics find_code_metadata)
      set
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret (Set_of_closures_not_rebuilt free_names cost_metrics)
  else
    let! tmp2 := SC.set_of_closures set in
    let! tmp3 := Static_const_or_code.create_static_const tmp2 in
    ret (Normal tmp3 free_names cost_metrics).

(* 131-134. [ListLabels.fold_left fields ~init ~f]: the arguments are in the
   order of the interface. *)
Definition free_names_of_fields (fields : list Simple.With_debuginfo.t)
    : M Name_occurrences.t :=
  ListLabels.fold_left
    (fun free_names field =>
      let! tmp1 := Simple.With_debuginfo.free_names field in
      Name_occurrences.union free_names tmp1)
    Name_occurrences.empty fields.

(* 136-145 *)
Definition create_block (are_rebuilding : ART.t) (tag : Tag.Scannable.t)
    (is_mutable : Mutability.t) (shape : Flambda_kind.Scannable_block_shape.t)
    (fields : list Simple.With_debuginfo.t) : M t :=
  let* cost_metrics :=
    let! tmp1 := List.length fields in
    let! tmp2 := Code_size.block tmp1 in
    Cost_metrics.from_size tmp2
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let* free_names := free_names_of_fields fields in
    ret (Block_not_rebuilt free_names cost_metrics)
  else
    let! tmp2 := SC.block tag is_mutable shape fields in
    create_normal_non_code cost_metrics tmp2.

(* 147-155 *)
Definition create_boxed_float32 (are_rebuilding : ART.t)
    (machine_width : Target_system.Machine_width.t)
    (or_var : Or_variable.t Numeric_types.Float32_by_bit_pattern.t) : M t :=
  let* cost_metrics :=
    let! tmp1 :=
      Code_size.box_number machine_width
        Flambda_kind.Boxable_number.Naked_float32
    in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let! tmp2 := Or_variable.free_names or_var in
    ret (Block_not_rebuilt tmp2 cost_metrics)
  else
    let! tmp2 := SC.boxed_float32 or_var in
    create_normal_non_code cost_metrics tmp2.

(* 157-165 *)
Definition create_boxed_float (are_rebuilding : ART.t)
    (machine_width : Target_system.Machine_width.t)
    (or_var : Or_variable.t Numeric_types.Float_by_bit_pattern.t) : M t :=
  let* cost_metrics :=
    let! tmp1 :=
      Code_size.box_number machine_width
        Flambda_kind.Boxable_number.Naked_float
    in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let! tmp2 := Or_variable.free_names or_var in
    ret (Block_not_rebuilt tmp2 cost_metrics)
  else
    let! tmp2 := SC.boxed_float or_var in
    create_normal_non_code cost_metrics tmp2.

(* 167-175 *)
Definition create_boxed_int32 (are_rebuilding : ART.t)
    (machine_width : Target_system.Machine_width.t)
    (or_var : Or_variable.t Int32.t) : M t :=
  let* cost_metrics :=
    let! tmp1 :=
      Code_size.box_number machine_width
        Flambda_kind.Boxable_number.Naked_int32
    in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let! tmp2 := Or_variable.free_names or_var in
    ret (Block_not_rebuilt tmp2 cost_metrics)
  else
    let! tmp2 := SC.boxed_int32 or_var in
    create_normal_non_code cost_metrics tmp2.

(* 177-185 *)
Definition create_boxed_int64 (are_rebuilding : ART.t)
    (machine_width : Target_system.Machine_width.t)
    (or_var : Or_variable.t Int64.t) : M t :=
  let* cost_metrics :=
    let! tmp1 :=
      Code_size.box_number machine_width
        Flambda_kind.Boxable_number.Naked_int64
    in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let! tmp2 := Or_variable.free_names or_var in
    ret (Block_not_rebuilt tmp2 cost_metrics)
  else
    let! tmp2 := SC.boxed_int64 or_var in
    create_normal_non_code cost_metrics tmp2.

(* 187-195 *)
Definition create_boxed_nativeint (are_rebuilding : ART.t)
    (machine_width : Target_system.Machine_width.t)
    (or_var : Or_variable.t Targetint_32_64.t) : M t :=
  let* cost_metrics :=
    let! tmp1 :=
      Code_size.box_number machine_width
        Flambda_kind.Boxable_number.Naked_nativeint
    in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let! tmp2 := Or_variable.free_names or_var in
    ret (Block_not_rebuilt tmp2 cost_metrics)
  else
    let! tmp2 := SC.boxed_nativeint or_var in
    create_normal_non_code cost_metrics tmp2.

(* 197-205 *)
Definition create_boxed_vec128 (are_rebuilding : ART.t)
    (machine_width : Target_system.Machine_width.t)
    (or_var : Or_variable.t Vector_types.Vec128.Bit_pattern.t) : M t :=
  let* cost_metrics :=
    let! tmp1 :=
      Code_size.box_number machine_width
        Flambda_kind.Boxable_number.Naked_vec128
    in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let! tmp2 := Or_variable.free_names or_var in
    ret (Block_not_rebuilt tmp2 cost_metrics)
  else
    let! tmp2 := SC.boxed_vec128 or_var in
    create_normal_non_code cost_metrics tmp2.

(* 207-215 *)
Definition create_boxed_vec256 (are_rebuilding : ART.t)
    (machine_width : Target_system.Machine_width.t)
    (or_var : Or_variable.t Vector_types.Vec256.Bit_pattern.t) : M t :=
  let* cost_metrics :=
    let! tmp1 :=
      Code_size.box_number machine_width
        Flambda_kind.Boxable_number.Naked_vec256
    in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let! tmp2 := Or_variable.free_names or_var in
    ret (Block_not_rebuilt tmp2 cost_metrics)
  else
    let! tmp2 := SC.boxed_vec256 or_var in
    create_normal_non_code cost_metrics tmp2.

(* 217-225 *)
Definition create_boxed_vec512 (are_rebuilding : ART.t)
    (machine_width : Target_system.Machine_width.t)
    (or_var : Or_variable.t Vector_types.Vec512.Bit_pattern.t) : M t :=
  let* cost_metrics :=
    let! tmp1 :=
      Code_size.box_number machine_width
        Flambda_kind.Boxable_number.Naked_vec512
    in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let! tmp2 := Or_variable.free_names or_var in
    ret (Block_not_rebuilt tmp2 cost_metrics)
  else
    let! tmp2 := SC.boxed_vec512 or_var in
    create_normal_non_code cost_metrics tmp2.

(* 227-235 *)
Definition create_boxed_mask (are_rebuilding : ART.t)
    (machine_width : Target_system.Machine_width.t)
    (or_var : Or_variable.t Vector_types.Mask.Bit_pattern.t) : M t :=
  let* cost_metrics :=
    let! tmp1 :=
      Code_size.box_number machine_width
        Flambda_kind.Boxable_number.Naked_mask
    in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let! tmp2 := Or_variable.free_names or_var in
    ret (Block_not_rebuilt tmp2 cost_metrics)
  else
    let! tmp2 := SC.boxed_mask or_var in
    create_normal_non_code cost_metrics tmp2.

(* 237-249 *)
Definition create_immutable_float_block (are_rebuilding : ART.t)
    (fields : list (Or_variable.t Numeric_types.Float_by_bit_pattern.t))
    : M t :=
  let* cost_metrics :=
    let! tmp1 := List.length fields in
    let! tmp2 := Code_size.array tmp1 in
    Cost_metrics.from_size tmp2
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let* free_names :=
      ListLabels.fold_left
        (fun free_names field =>
          let! tmp2 := Or_variable.free_names field in
          Name_occurrences.union free_names tmp2)
        Name_occurrences.empty fields
    in
    ret (Block_not_rebuilt free_names cost_metrics)
  else
    let! tmp2 := SC.immutable_float_block fields in
    create_normal_non_code cost_metrics tmp2.

(* 251-263 *)
Definition create_immutable_naked_number_array {A : Type}
    (builder : list (Or_variable.t A) -> M SC.t) (are_rebuilding : ART.t)
    (fields : list (Or_variable.t A)) : M t :=
  let* cost_metrics :=
    let! tmp1 := List.length fields in
    let! tmp2 := Code_size.array tmp1 in
    Cost_metrics.from_size tmp2
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let* free_names :=
      ListLabels.fold_left
        (fun free_names field =>
          let! tmp2 := Or_variable.free_names field in
          Name_occurrences.union free_names tmp2)
        Name_occurrences.empty fields
    in
    ret (Block_not_rebuilt free_names cost_metrics)
  else
    let! tmp2 := builder fields in
    create_normal_non_code cost_metrics tmp2.

(* 265-266. This and the eleven definitions that follow: the function of
   the file is given its first argument only, as in the compiler. *)
Definition create_immutable_float_array
    : ART.t -> list (Or_variable.t Numeric_types.Float_by_bit_pattern.t) ->
      M t :=
  create_immutable_naked_number_array SC.immutable_float_array.

(* 268-269 *)
Definition create_immutable_float32_array
    : ART.t -> list (Or_variable.t Numeric_types.Float32_by_bit_pattern.t) ->
      M t :=
  create_immutable_naked_number_array SC.immutable_float32_array.

(* 271-272 *)
Definition create_immutable_int_array
    : ART.t -> list (Or_variable.t Target_ocaml_int.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_int_array.

(* 274-275 *)
Definition create_immutable_int8_array
    : ART.t -> list (Or_variable.t Numeric_types.Int8.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_int8_array.

(* 277-278 *)
Definition create_immutable_int16_array
    : ART.t -> list (Or_variable.t Numeric_types.Int16.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_int16_array.

(* 280-281 *)
Definition create_immutable_int32_array
    : ART.t -> list (Or_variable.t Int32.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_int32_array.

(* 283-284 *)
Definition create_immutable_int64_array
    : ART.t -> list (Or_variable.t Int64.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_int64_array.

(* 286-287 *)
Definition create_immutable_nativeint_array
    : ART.t -> list (Or_variable.t Targetint_32_64.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_nativeint_array.

(* 289-290 *)
Definition create_immutable_vec128_array
    : ART.t -> list (Or_variable.t Vector_types.Vec128.Bit_pattern.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_vec128_array.

(* 292-293 *)
Definition create_immutable_vec256_array
    : ART.t -> list (Or_variable.t Vector_types.Vec256.Bit_pattern.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_vec256_array.

(* 295-296 *)
Definition create_immutable_vec512_array
    : ART.t -> list (Or_variable.t Vector_types.Vec512.Bit_pattern.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_vec512_array.

(* 298-299 *)
Definition create_immutable_mask_array
    : ART.t -> list (Or_variable.t Vector_types.Mask.Bit_pattern.t) -> M t :=
  create_immutable_naked_number_array SC.immutable_mask_array.

(* 301-309 *)
Definition create_immutable_value_array (are_rebuilding : ART.t)
    (fields : list Simple.With_debuginfo.t) : M t :=
  let* cost_metrics :=
    let! tmp1 := List.length fields in
    let! tmp2 := Code_size.array tmp1 in
    Cost_metrics.from_size tmp2
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    let* free_names := free_names_of_fields fields in
    ret (Block_not_rebuilt free_names cost_metrics)
  else
    let! tmp2 := SC.immutable_value_array fields in
    create_normal_non_code cost_metrics tmp2.

(* 311-315 *)
Definition create_empty_array (are_rebuilding : ART.t)
    (array_kind : Empty_array_kind.t) : M t :=
  let* cost_metrics :=
    let! tmp1 := Code_size.array 0 in
    Cost_metrics.from_size tmp1
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret (Block_not_rebuilt Name_occurrences.empty cost_metrics)
  else
    let! tmp2 := SC.empty_array array_kind in
    create_normal_non_code cost_metrics tmp2.

(* 317-323 *)
Definition create_immutable_string (are_rebuilding : ART.t) (str : string)
    : M t :=
  let* cost_metrics :=
    let! tmp1 := String.length str in
    let! tmp2 := Code_size.of_int tmp1 in
    Cost_metrics.from_size tmp2
  in
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret (Block_not_rebuilt Name_occurrences.empty cost_metrics)
  else
    let! tmp2 := SC.immutable_string str in
    create_normal_non_code cost_metrics tmp2.

(* 325-359 *)
Definition map_set_of_closures (t : Rebuilt_static_const.t)
    (find_code_metadata : Code_id.t -> M Code_metadata.t)
    (f : Set_of_closures.t -> M Set_of_closures.t)
    : M Rebuilt_static_const.t :=
  match t with
  | Normal const _ _ =>
    match const with
    | Code _ | Deleted_code => ret t
    | Static_const const =>
      match const with
      | SC.Set_of_closures set_of_closures =>
        let* set_of_closures := f set_of_closures in
        let* cost_metrics :=
          Cost_metrics.set_of_closures
            (find_code_characteristics find_code_metadata)
            set_of_closures
        in
        (* PORT-GAP(record-order): 341-344, calls in the fields [const] and
           [free_names]: the last field first. *)
        let! tmp1 := Set_of_closures.free_names set_of_closures in
        let! tmp2 := SC.set_of_closures set_of_closures in
        let! tmp3 := Static_const_or_code.create_static_const tmp2 in
        ret (Normal tmp3 tmp1 cost_metrics)
      | SC.Block _ _ _ _ | SC.Boxed_float _ | SC.Boxed_float32 _
      | SC.Boxed_int32 _ | SC.Boxed_int64 _ | SC.Boxed_vec128 _
      | SC.Boxed_vec256 _ | SC.Boxed_vec512 _ | SC.Boxed_mask _
      | SC.Boxed_nativeint _ | SC.Immutable_float_block _
      | SC.Immutable_float_array _ | SC.Immutable_float32_array _
      | SC.Immutable_int_array _ | SC.Immutable_int8_array _
      | SC.Immutable_int16_array _ | SC.Immutable_int32_array _
      | SC.Immutable_int64_array _ | SC.Immutable_nativeint_array _
      | SC.Immutable_vec128_array _ | SC.Immutable_vec256_array _
      | SC.Immutable_vec512_array _ | SC.Immutable_mask_array _
      | SC.Immutable_value_array _ | SC.Empty_array _
      | SC.Immutable_string _ =>
        ret t
      end
    end
  | Block_not_rebuilt _ _ | Set_of_closures_not_rebuilt _ _
  | Code_not_rebuilt _ =>
    ret t
  end.

(* 361-367 *)
Definition free_names (t : Rebuilt_static_const.t) : M Name_occurrences.t :=
  match t with
  | Normal _ free_names _ => ret free_names
  | Block_not_rebuilt free_names _ | Set_of_closures_not_rebuilt free_names _
    =>
    ret free_names
  | Code_not_rebuilt code => Non_constructed_code.free_names code
  end.

(* 369 *)
Definition is_fully_static (t : Rebuilt_static_const.t) : M bool :=
  let! tmp1 := free_names t in
  Name_occurrences.no_variables tmp1.

(* 371-375 *)
Definition to_const (t : Rebuilt_static_const.t)
    : M (option Static_const_or_code.t) :=
  match t with
  | Block_not_rebuilt _ _ | Set_of_closures_not_rebuilt _ _
  | Code_not_rebuilt _ =>
    ret None
  | Normal const _ _ => ret (Some const)
  end.

(* 377-386 *)
(* PORT-GAP(loose): 377, the attribute [@ocamlformat "disable"] is not
   kept. *)
Definition print (ppf : Format.formatter) (t : Rebuilt_static_const.t)
    : M unit :=
  match t with
  | Normal const _ _ => Static_const_or_code.print ppf const
  | Block_not_rebuilt _ _ => Format.fprintf0 ppf "Block_not_rebuilt"
  | Set_of_closures_not_rebuilt _ _ =>
    Format.fprintf0 ppf "Set_of_closures_not_rebuilt"
  | Code_not_rebuilt code =>
    Format.fprintf2 ppf "@[<hov 1>(Code_not_rebuilt@ %a)@]"
      Non_constructed_code.print code
  end.

(* 388-393 *)
Definition deleted_code : t :=
  Normal Static_const_or_code.deleted_code Name_occurrences.empty
    Cost_metrics.zero.

(* 395-411 *)
Definition make_code_deleted (t : Rebuilt_static_const.t)
    (if_code_id_is_member_of : Code_id.Set_.t) : M Rebuilt_static_const.t :=
  match t with
  | Normal const _ _ =>
    let! tmp1 := Static_const_or_code.to_code const in
    match tmp1 with
    | None => ret t
    | Some code =>
      let! tmp1 := Code.code_id code in
      let! tmp2 := Code_id.Set_.mem tmp1 if_code_id_is_member_of in
      if tmp2 then ret deleted_code else ret t
    end
  | Block_not_rebuilt _ _ | Set_of_closures_not_rebuilt _ _ => ret t
  | Code_not_rebuilt code =>
    let! tmp1 := Non_constructed_code.code_id code in
    let! tmp2 := Code_id.Set_.mem tmp1 if_code_id_is_member_of in
    if tmp2 then ret deleted_code else ret t
  end.

(* 413-522 *)
Module Group.
  (* 414-417 *)
  (* PORT-GAP(type): the record has a mutable field. In Rocq the type is
     abstract: [mk_t] makes a record (in the monad: the record has a state),
     [consts] reads the field that does not change, [get_free_names] and
     [set_free_names] read and set the mutable field (in the monad). The
     OCaml definition is the compiler's text; the four functions are
     realised by OCaml texts written for this file, and Rocq prints them
     here, in the module, as four definitions that the compiler does not
     have. *)
  Parameter t : Type.
  Extract Constant t =>
    "{ consts : rebuilt_static_const list; mutable free_names : Name_occurrences.t Or_unknown.t }".
  Parameter mk_t :
    list rebuilt_static_const -> Or_unknown.t Name_occurrences.t -> M t.
  Extract Constant mk_t => "fun consts free_names -> { consts; free_names }".
  Parameter consts : t -> list rebuilt_static_const.
  Extract Constant consts => "fun t -> t.consts".
  Parameter get_free_names : t -> M (Or_unknown.t Name_occurrences.t).
  Extract Constant get_free_names => "fun t -> t.free_names".
  Parameter set_free_names : t -> Or_unknown.t Name_occurrences.t -> M unit.
  Extract Constant set_free_names =>
    "fun t free_names -> t.free_names <- free_names".

  (* 419 *)
  (* PORT-GAP(init): a record with a mutable field that is made when the
     module starts: a parameter, realised by the compiler's text. *)
  Parameter empty : t.
  Extract Constant empty =>
    "{ consts = []; free_names = Known Name_occurrences.empty }".

  (* 421 *)
  Definition create (consts : list rebuilt_static_const) : M t :=
    mk_t consts Or_unknown.Unknown.

  (* 423-425 *)
  (* PORT-GAP(loose): 423, the attribute [@ocamlformat "disable"] is not
     kept, and the record pattern [{ consts; free_names = _; }] of the
     parameter is the reading of the field [consts]. *)
  Definition print (ppf : Format.formatter) (t : Group.t) : M unit :=
    let& consts := consts t in
    (* PORT-GAP(papp): 425, [Format.pp_print_list] is given its first two
       arguments only; [print] is the function of 377. *)
    let! tmp1 :=
      papp2 Format.pp_print_list (Some Format.pp_print_space) print
    in
    Format.fprintf2 ppf "@[<hov 1>(%a)@]" tmp1 consts.

  (* 427-437 *)
  Definition free_names (t : Group.t) : M Name_occurrences.t :=
    let! tmp1 := get_free_names t in
    match tmp1 with
    | Or_unknown.Known free_names => ret free_names
    | Or_unknown.Unknown =>
      let* free_names :=
        (* 434: [free_names const] is the function of 361. *)
        ListLabels.fold_left
          (fun free_names_acc (const : rebuilt_static_const) =>
            let! tmp1 := free_names const in
            Name_occurrences.union free_names_acc tmp1)
          Name_occurrences.empty (consts t)
      in
      set_free_names t (Or_unknown.Known free_names) ;;
      ret free_names
    end.

  (* 439-442 *)
  Definition cost_metrics (t : Group.t) : M Cost_metrics.t :=
    (* 441: [cost_metrics const] is the function of 60. *)
    List.fold_left
      (fun cm const =>
        let! tmp1 := cost_metrics const in
        Cost_metrics.op_plus cm tmp1)
      Cost_metrics.zero (consts t).

  (* 444-452: [a |> f |> g] is [g (f a)]. *)
  Definition to_named (t : Group.t) : M Named.t :=
    let! tmp1 :=
      ListLabels.map
        (fun (const : rebuilt_static_const) =>
          match const with
          | Normal const _ _ => ret const
          | Block_not_rebuilt _ _ | Set_of_closures_not_rebuilt _ _
          | Code_not_rebuilt _ =>
            fatal_error
              "Cannot extract static constants when not rebuilding terms"
          end)
        (consts t)
    in
    let! tmp2 := Static_const_group.create tmp1 in
    Named.create_static_consts tmp2.

  (* 454-464 *)
  Definition pieces_of_code_for_cmx (t : Group.t) : M (Code_id.Map.t Code.t) :=
    let! tmp3 :=
      ListLabels.filter_map
        (fun (const : rebuilt_static_const) =>
          match const with
          | Normal const _ _ =>
            let! tmp1 := Static_const_or_code.to_code const in
            match tmp1 with
            | None => ret None
            | Some code =>
              let! tmp2 := Code.code_id code in
              ret (Some (tmp2, code))
            end
          | Block_not_rebuilt _ _ | Set_of_closures_not_rebuilt _ _
          | Code_not_rebuilt _ =>
            ret None
          end)
        (consts t)
    in
    Code_id.Map.of_list tmp3.

  (* 466-478 *)
  (* PORT-GAP(init): a lazy value that is made when the module starts: a
     parameter, realised by the compiler's text. *)
  Parameter function_params_and_body_for_code_not_rebuilt :
    lazy_t Function_params_and_body.t.
  Extract Constant function_params_and_body_for_code_not_rebuilt => "
    lazy
      (Function_params_and_body.create
         ~return_continuation:(Continuation.create ~sort:Return ())
         ~exn_continuation:(Continuation.create ()) Bound_parameters.empty
         ~body:(Expr.create_invalid Code_not_rebuilt)
         ~free_names_of_body:Unknown
         ~my_closure:(Variable.create ""my_closure"" Flambda_kind.value)
         ~my_alloc_mode:
           (Alloc_mode.For_applications.not_alloc_stack
              ~alloc_region:
                (Variable.create ""my_alloc_region"" Flambda_kind.region))
         ~my_depth:(Variable.create ""my_depth"" Flambda_kind.rec_info))".

  (* 480-496 *)
  Definition pieces_of_code_including_those_not_rebuilt (t : Group.t)
      : M (Code_id.Map.t Code.t) :=
    let! tmp3 :=
      ListLabels.filter_map
        (fun (const : rebuilt_static_const) =>
          match const with
          | Normal const _ _ => Static_const_or_code.to_code const
          | Block_not_rebuilt _ _ | Set_of_closures_not_rebuilt _ _ =>
            ret None
          | Code_not_rebuilt code =>
            (* PORT-GAP(loose): 486, [let module NCC = Non_constructed_code
               in] is not kept: the module is written by its name. *)
            (* See comment in the .mli. *)
            let* params_and_body :=
              force function_params_and_body_for_code_not_rebuilt
            in
            let! tmp1 := Non_constructed_code.code_metadata code in
            let! tmp2 :=
              Code.create_with_metadata params_and_body Name_occurrences.empty
                tmp1
            in
            ret (Some tmp2)
          end)
        (consts t)
    in
    let! tmp4 :=
      List.map
        (fun code =>
          let! tmp1 := Code.code_id code in
          ret (tmp1, code))
        tmp3
    in
    Code_id.Map.of_list tmp4.

  (* 498-506 *)
  Definition map (t : Group.t)
      (f : rebuilt_static_const -> M rebuilt_static_const) : M Group.t :=
    let* changed := mk_ref false in
    let* consts :=
      ListLabels.map
        (fun const =>
          let* const' := f const in
          (let! tmp1 := phys_not_equal const const' in
           if tmp1 then set changed true else ret tt) ;;
          ret const')
        (consts t)
    in
    let! tmp1 := get changed in
    if negb tmp1 then ret t else mk_t consts Or_unknown.Unknown.

  (* 508 *)
  Definition fold_left {A : Type} (t : Group.t) (init : A)
      (f : A -> rebuilt_static_const -> M A) : M A :=
    ListLabels.fold_left f init (consts t).

  (* 510 *)
  Definition add (const : rebuilt_static_const) (t : Group.t) : M Group.t :=
    mk_t (const :: consts t) Or_unknown.Unknown.

  (* 512-519 *)
  Definition concat (t1 t2 : t) : M t :=
    let* free_names :=
      (* PORT-GAP(loose): 514, [match t1.free_names, t2.free_names with]:
         the pair is named ([fn1], [fn2], names that the compiler does not
         have) before the match, so that each field is read once and the
         second one first. *)
      let! tmp1 := get_free_names t2 in
      let! tmp2 := get_free_names t1 in
      let* '(fn1, fn2) := ret (tmp2, tmp1) in
      match fn1, fn2 with
      | Or_unknown.Known free_names1, Or_unknown.Known free_names2 =>
        let! tmp1 := Name_occurrences.union free_names1 free_names2 in
        ret (Or_unknown.Known tmp1)
      | Or_unknown.Known _, Or_unknown.Unknown
      | Or_unknown.Unknown, Or_unknown.Known _
      | Or_unknown.Unknown, Or_unknown.Unknown =>
        ret Or_unknown.Unknown
      end
    in
    mk_t (consts t1 ++ consts t2) free_names.

  (* 521 *)
  Definition to_list (t : Group.t) : M (list rebuilt_static_const) :=
    ret (consts t).
End Group.
