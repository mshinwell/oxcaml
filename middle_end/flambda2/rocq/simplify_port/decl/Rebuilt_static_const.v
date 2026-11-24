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

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Rebuilt_static_const], after its interface
   middle_end/flambda2/simplify/rebuilt_static_const.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Are_rebuilding_terms Code Code_id Code_metadata Cost_metrics Empty_array_kind Flambda Flambda_kind Format Int32 Int64 Mutability Name_occurrences Numeric_types Or_variable Rebuilt_expr Simple Tag Target_ocaml_int Target_system Targetint_32_64 Vector_types.

(* rebuilt_static_const.mli:23  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Rebuilt_static_const.t".
(* rebuilt_static_const.mli:25  type rebuilt_static_const = t *)
Definition rebuilt_static_const : Type := t.
Extract Inlined Constant rebuilt_static_const => "Rebuilt_static_const.rebuilt_static_const".
(* rebuilt_static_const.mli:27  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Rebuilt_static_const.print".
(* rebuilt_static_const.mli:29  val cost_metrics : t -> Cost_metrics.t *)
Parameter cost_metrics : t -> M Cost_metrics.t.
Extract Inlined Constant cost_metrics => "Rebuilt_static_const.cost_metrics".
(* rebuilt_static_const.mli:31  val create_code : Are_rebuilding_terms.t -> params_and_body:Rebuilt_expr.Function_params_and_body.t -> free_names_of_params_and_body:Name_occurrences.t -> (t * Code.t option) Code_metadata.create_type *)
Parameter create_code : Are_rebuilding_terms.t -> Rebuilt_expr.Function_params_and_body.t -> Name_occurrences.t -> Code_metadata.create_type (t * option Code.t).
Extract Inlined Constant create_code => "Rebuilt_static_const.create_code".
(* rebuilt_static_const.mli:41  val create_code' : Code.t -> t *)
Parameter create_code' : Code.t -> M t.
Extract Inlined Constant create_code' => "Rebuilt_static_const.create_code'".
(* rebuilt_static_const.mli:43  val create_set_of_closures : Are_rebuilding_terms.t -> find_code_metadata:(Code_id.t -> Code_metadata.t) -> Set_of_closures.t -> t *)
Parameter create_set_of_closures : Are_rebuilding_terms.t -> (Code_id.t -> M Code_metadata.t) -> Flambda.Set_of_closures.t -> M t.
Extract Inlined Constant create_set_of_closures => "Rebuilt_static_const.create_set_of_closures".
(* rebuilt_static_const.mli:49  val create_block : Are_rebuilding_terms.t -> Tag.Scannable.t -> Mutability.t -> Flambda_kind.Scannable_block_shape.t -> fields:Simple.With_debuginfo.t list -> t *)
Parameter create_block : Are_rebuilding_terms.t -> Tag.Scannable.t -> Mutability.t -> Flambda_kind.Scannable_block_shape.t -> list Simple.With_debuginfo.t -> M t.
Extract Inlined Constant create_block => "Rebuilt_static_const.create_block".
(* rebuilt_static_const.mli:57  val create_boxed_float32 : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> Numeric_types.Float32_by_bit_pattern.t Or_variable.t -> t *)
Parameter create_boxed_float32 : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> Or_variable.t Numeric_types.Float32_by_bit_pattern.t -> M t.
Extract Inlined Constant create_boxed_float32 => "Rebuilt_static_const.create_boxed_float32".
(* rebuilt_static_const.mli:63  val create_boxed_float : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> Numeric_types.Float_by_bit_pattern.t Or_variable.t -> t *)
Parameter create_boxed_float : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> Or_variable.t Numeric_types.Float_by_bit_pattern.t -> M t.
Extract Inlined Constant create_boxed_float => "Rebuilt_static_const.create_boxed_float".
(* rebuilt_static_const.mli:69  val create_boxed_int32 : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> Int32.t Or_variable.t -> t *)
Parameter create_boxed_int32 : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> Or_variable.t Int32.t -> M t.
Extract Inlined Constant create_boxed_int32 => "Rebuilt_static_const.create_boxed_int32".
(* rebuilt_static_const.mli:75  val create_boxed_int64 : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> Int64.t Or_variable.t -> t *)
Parameter create_boxed_int64 : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> Or_variable.t Int64.t -> M t.
Extract Inlined Constant create_boxed_int64 => "Rebuilt_static_const.create_boxed_int64".
(* rebuilt_static_const.mli:81  val create_boxed_nativeint : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> Targetint_32_64.t Or_variable.t -> t *)
Parameter create_boxed_nativeint : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> Or_variable.t Targetint_32_64.t -> M t.
Extract Inlined Constant create_boxed_nativeint => "Rebuilt_static_const.create_boxed_nativeint".
(* rebuilt_static_const.mli:87  val create_boxed_vec128 : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> Vector_types.Vec128.Bit_pattern.t Or_variable.t -> t *)
Parameter create_boxed_vec128 : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> Or_variable.t Vector_types.Vec128.Bit_pattern.t -> M t.
Extract Inlined Constant create_boxed_vec128 => "Rebuilt_static_const.create_boxed_vec128".
(* rebuilt_static_const.mli:93  val create_boxed_vec256 : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> Vector_types.Vec256.Bit_pattern.t Or_variable.t -> t *)
Parameter create_boxed_vec256 : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> Or_variable.t Vector_types.Vec256.Bit_pattern.t -> M t.
Extract Inlined Constant create_boxed_vec256 => "Rebuilt_static_const.create_boxed_vec256".
(* rebuilt_static_const.mli:99  val create_boxed_vec512 : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> Vector_types.Vec512.Bit_pattern.t Or_variable.t -> t *)
Parameter create_boxed_vec512 : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> Or_variable.t Vector_types.Vec512.Bit_pattern.t -> M t.
Extract Inlined Constant create_boxed_vec512 => "Rebuilt_static_const.create_boxed_vec512".
(* rebuilt_static_const.mli:105  val create_boxed_mask : Are_rebuilding_terms.t -> machine_width:Target_system.Machine_width.t -> Vector_types.Mask.Bit_pattern.t Or_variable.t -> t *)
Parameter create_boxed_mask : Are_rebuilding_terms.t -> Target_system.Machine_width.t -> Or_variable.t Vector_types.Mask.Bit_pattern.t -> M t.
Extract Inlined Constant create_boxed_mask => "Rebuilt_static_const.create_boxed_mask".
(* rebuilt_static_const.mli:111  val create_immutable_float_block : Are_rebuilding_terms.t -> Numeric_types.Float_by_bit_pattern.t Or_variable.t list -> t *)
Parameter create_immutable_float_block : Are_rebuilding_terms.t -> list (Or_variable.t Numeric_types.Float_by_bit_pattern.t) -> M t.
Extract Inlined Constant create_immutable_float_block => "Rebuilt_static_const.create_immutable_float_block".
(* rebuilt_static_const.mli:116  val create_immutable_float_array : Are_rebuilding_terms.t -> Numeric_types.Float_by_bit_pattern.t Or_variable.t list -> t *)
Parameter create_immutable_float_array : Are_rebuilding_terms.t -> list (Or_variable.t Numeric_types.Float_by_bit_pattern.t) -> M t.
Extract Inlined Constant create_immutable_float_array => "Rebuilt_static_const.create_immutable_float_array".
(* rebuilt_static_const.mli:121  val create_immutable_float32_array : Are_rebuilding_terms.t -> Numeric_types.Float32_by_bit_pattern.t Or_variable.t list -> t *)
Parameter create_immutable_float32_array : Are_rebuilding_terms.t -> list (Or_variable.t Numeric_types.Float32_by_bit_pattern.t) -> M t.
Extract Inlined Constant create_immutable_float32_array => "Rebuilt_static_const.create_immutable_float32_array".
(* rebuilt_static_const.mli:126  val create_immutable_int_array : Are_rebuilding_terms.t -> Target_ocaml_int.t Or_variable.t list -> t *)
Parameter create_immutable_int_array : Are_rebuilding_terms.t -> list (Or_variable.t Target_ocaml_int.t) -> M t.
Extract Inlined Constant create_immutable_int_array => "Rebuilt_static_const.create_immutable_int_array".
(* rebuilt_static_const.mli:129  val create_immutable_int8_array : Are_rebuilding_terms.t -> Numeric_types.Int8.t Or_variable.t list -> t *)
Parameter create_immutable_int8_array : Are_rebuilding_terms.t -> list (Or_variable.t Numeric_types.Int8.t) -> M t.
Extract Inlined Constant create_immutable_int8_array => "Rebuilt_static_const.create_immutable_int8_array".
(* rebuilt_static_const.mli:132  val create_immutable_int16_array : Are_rebuilding_terms.t -> Numeric_types.Int16.t Or_variable.t list -> t *)
Parameter create_immutable_int16_array : Are_rebuilding_terms.t -> list (Or_variable.t Numeric_types.Int16.t) -> M t.
Extract Inlined Constant create_immutable_int16_array => "Rebuilt_static_const.create_immutable_int16_array".
(* rebuilt_static_const.mli:135  val create_immutable_int32_array : Are_rebuilding_terms.t -> Int32.t Or_variable.t list -> t *)
Parameter create_immutable_int32_array : Are_rebuilding_terms.t -> list (Or_variable.t Int32.t) -> M t.
Extract Inlined Constant create_immutable_int32_array => "Rebuilt_static_const.create_immutable_int32_array".
(* rebuilt_static_const.mli:138  val create_immutable_int64_array : Are_rebuilding_terms.t -> Int64.t Or_variable.t list -> t *)
Parameter create_immutable_int64_array : Are_rebuilding_terms.t -> list (Or_variable.t Int64.t) -> M t.
Extract Inlined Constant create_immutable_int64_array => "Rebuilt_static_const.create_immutable_int64_array".
(* rebuilt_static_const.mli:141  val create_immutable_nativeint_array : Are_rebuilding_terms.t -> Targetint_32_64.t Or_variable.t list -> t *)
Parameter create_immutable_nativeint_array : Are_rebuilding_terms.t -> list (Or_variable.t Targetint_32_64.t) -> M t.
Extract Inlined Constant create_immutable_nativeint_array => "Rebuilt_static_const.create_immutable_nativeint_array".
(* rebuilt_static_const.mli:144  val create_immutable_vec128_array : Are_rebuilding_terms.t -> Vector_types.Vec128.Bit_pattern.t Or_variable.t list -> t *)
Parameter create_immutable_vec128_array : Are_rebuilding_terms.t -> list (Or_variable.t Vector_types.Vec128.Bit_pattern.t) -> M t.
Extract Inlined Constant create_immutable_vec128_array => "Rebuilt_static_const.create_immutable_vec128_array".
(* rebuilt_static_const.mli:149  val create_immutable_vec256_array : Are_rebuilding_terms.t -> Vector_types.Vec256.Bit_pattern.t Or_variable.t list -> t *)
Parameter create_immutable_vec256_array : Are_rebuilding_terms.t -> list (Or_variable.t Vector_types.Vec256.Bit_pattern.t) -> M t.
Extract Inlined Constant create_immutable_vec256_array => "Rebuilt_static_const.create_immutable_vec256_array".
(* rebuilt_static_const.mli:154  val create_immutable_vec512_array : Are_rebuilding_terms.t -> Vector_types.Vec512.Bit_pattern.t Or_variable.t list -> t *)
Parameter create_immutable_vec512_array : Are_rebuilding_terms.t -> list (Or_variable.t Vector_types.Vec512.Bit_pattern.t) -> M t.
Extract Inlined Constant create_immutable_vec512_array => "Rebuilt_static_const.create_immutable_vec512_array".
(* rebuilt_static_const.mli:159  val create_immutable_mask_array : Are_rebuilding_terms.t -> Vector_types.Mask.Bit_pattern.t Or_variable.t list -> t *)
Parameter create_immutable_mask_array : Are_rebuilding_terms.t -> list (Or_variable.t Vector_types.Mask.Bit_pattern.t) -> M t.
Extract Inlined Constant create_immutable_mask_array => "Rebuilt_static_const.create_immutable_mask_array".
(* rebuilt_static_const.mli:164  val create_immutable_value_array : Are_rebuilding_terms.t -> Simple.With_debuginfo.t list -> t *)
Parameter create_immutable_value_array : Are_rebuilding_terms.t -> list Simple.With_debuginfo.t -> M t.
Extract Inlined Constant create_immutable_value_array => "Rebuilt_static_const.create_immutable_value_array".
(* rebuilt_static_const.mli:167  val create_empty_array : Are_rebuilding_terms.t -> Empty_array_kind.t -> t *)
Parameter create_empty_array : Are_rebuilding_terms.t -> Empty_array_kind.t -> M t.
Extract Inlined Constant create_empty_array => "Rebuilt_static_const.create_empty_array".
(* rebuilt_static_const.mli:169  val create_immutable_string : Are_rebuilding_terms.t -> string -> t *)
Parameter create_immutable_string : Are_rebuilding_terms.t -> string -> M t.
Extract Inlined Constant create_immutable_string => "Rebuilt_static_const.create_immutable_string".
(* rebuilt_static_const.mli:171  val map_set_of_closures : t -> find_code_metadata:(Code_id.t -> Code_metadata.t) -> f:(Set_of_closures.t -> Set_of_closures.t) -> t *)
Parameter map_set_of_closures : t -> (Code_id.t -> M Code_metadata.t) -> (Flambda.Set_of_closures.t -> M Flambda.Set_of_closures.t) -> M t.
Extract Inlined Constant map_set_of_closures => "Rebuilt_static_const.map_set_of_closures".
(* rebuilt_static_const.mli:177  val free_names : t -> Name_occurrences.t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Rebuilt_static_const.free_names".
(* rebuilt_static_const.mli:179  val is_block : t -> bool *)
Parameter is_block : t -> M bool.
Extract Inlined Constant is_block => "Rebuilt_static_const.is_block".
(* rebuilt_static_const.mli:181  val is_set_of_closures : t -> bool *)
Parameter is_set_of_closures : t -> M bool.
Extract Inlined Constant is_set_of_closures => "Rebuilt_static_const.is_set_of_closures".
(* rebuilt_static_const.mli:183  val is_code : t -> bool *)
Parameter is_code : t -> M bool.
Extract Inlined Constant is_code => "Rebuilt_static_const.is_code".
(* rebuilt_static_const.mli:185  val is_fully_static : t -> bool *)
Parameter is_fully_static : t -> M bool.
Extract Inlined Constant is_fully_static => "Rebuilt_static_const.is_fully_static".
(* rebuilt_static_const.mli:187  val make_code_deleted : t -> if_code_id_is_member_of:Code_id.Set.t -> t *)
Parameter make_code_deleted : t -> Code_id.Set_.t -> M t.
Extract Inlined Constant make_code_deleted => "Rebuilt_static_const.make_code_deleted".
(* rebuilt_static_const.mli:190  val to_const : t -> Static_const_or_code.t option *)
Parameter to_const : t -> M (option Flambda.Static_const_or_code.t).
Extract Inlined Constant to_const => "Rebuilt_static_const.to_const".
Module Group.
  (* rebuilt_static_const.mli:193  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Rebuilt_static_const.Group.t".
  (* rebuilt_static_const.mli:195  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Rebuilt_static_const.Group.print".
  (* rebuilt_static_const.mli:197  val empty : t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Rebuilt_static_const.Group.empty".
  (* rebuilt_static_const.mli:199  val create : rebuilt_static_const list -> t *)
  Parameter create : list Rebuilt_static_const.rebuilt_static_const -> M t.
  Extract Inlined Constant create => "Rebuilt_static_const.Group.create".
  (* rebuilt_static_const.mli:201  val free_names : t -> Name_occurrences.t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Rebuilt_static_const.Group.free_names".
  (* rebuilt_static_const.mli:203  val cost_metrics : t -> Cost_metrics.t *)
  Parameter cost_metrics : t -> M Cost_metrics.t.
  Extract Inlined Constant cost_metrics => "Rebuilt_static_const.Group.cost_metrics".
  (* rebuilt_static_const.mli:207  val to_named : t -> Named.t *)
  Parameter to_named : t -> M Flambda.Named.t.
  Extract Inlined Constant to_named => "Rebuilt_static_const.Group.to_named".
  (* rebuilt_static_const.mli:213  val pieces_of_code_including_those_not_rebuilt : t -> Code.t Code_id.Map.t *)
  Parameter pieces_of_code_including_those_not_rebuilt : t -> M (Code_id.Map.t Code.t).
  Extract Inlined Constant pieces_of_code_including_those_not_rebuilt => "Rebuilt_static_const.Group.pieces_of_code_including_those_not_rebuilt".
  (* rebuilt_static_const.mli:216  val pieces_of_code_for_cmx : t -> Code.t Code_id.Map.t *)
  Parameter pieces_of_code_for_cmx : t -> M (Code_id.Map.t Code.t).
  Extract Inlined Constant pieces_of_code_for_cmx => "Rebuilt_static_const.Group.pieces_of_code_for_cmx".
  (* rebuilt_static_const.mli:218  val map : t -> f:(rebuilt_static_const -> rebuilt_static_const) -> t *)
  Parameter map : t -> (Rebuilt_static_const.rebuilt_static_const -> M Rebuilt_static_const.rebuilt_static_const) -> M t.
  Extract Inlined Constant map => "Rebuilt_static_const.Group.map".
  (* rebuilt_static_const.mli:220  val fold_left : t -> init:'a -> f:('a -> rebuilt_static_const -> 'a) -> 'a *)
  Parameter fold_left : forall {A : Type}, t -> A -> (A -> Rebuilt_static_const.rebuilt_static_const -> M A) -> M A.
  Extract Inlined Constant fold_left => "Rebuilt_static_const.Group.fold_left".
  (* rebuilt_static_const.mli:224  val to_list : t -> rebuilt_static_const list *)
  Parameter to_list : t -> M (list Rebuilt_static_const.rebuilt_static_const).
  Extract Inlined Constant to_list => "Rebuilt_static_const.Group.to_list".
  (* rebuilt_static_const.mli:226  val add : rebuilt_static_const -> t -> t *)
  Parameter add : Rebuilt_static_const.rebuilt_static_const -> t -> M t.
  Extract Inlined Constant add => "Rebuilt_static_const.Group.add".
  (* rebuilt_static_const.mli:228  val concat : t -> t -> t *)
  Parameter concat : t -> t -> M t.
  Extract Inlined Constant concat => "Rebuilt_static_const.Group.concat".
End Group.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Rebuilt_static_const. End Rebuilt_static_const.
