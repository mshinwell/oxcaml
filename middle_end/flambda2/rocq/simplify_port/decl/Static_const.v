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

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Static_const], after its interface
   middle_end/flambda2/terms/static_const.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Empty_array_kind Flambda_kind Format Int32 Int64 Mutability Name_occurrences Numeric_types Or_variable Set_of_closures Simple Tag Target_ocaml_int Targetint_32_64 Vector_types.

(* static_const.mli:25  type t = private | Set_of_closures of Set_of_closures.t | Block of Tag.Scannable.t * Mutability.t * Flambda_kind.Scannable_block_shape.t * Simple.With_debuginfo.t list | Boxed_float32 of Numeric_types.Float32_by_bit_pattern.t Or_variable.t | Boxed_float of Numeric_types.Float_by_bit_pattern.t Or_variable.t | Boxed_int32 of Int32.t Or_variable.t | Boxed_int64 of Int64.t Or_variable.t | Boxed_nat... *)
Inductive t : Type :=
| Set_of_closures : Set_of_closures.t -> t
| Block : Tag.Scannable.t -> Mutability.t -> Flambda_kind.Scannable_block_shape.t -> list Simple.With_debuginfo.t -> t
| Boxed_float32 : Or_variable.t Numeric_types.Float32_by_bit_pattern.t -> t
| Boxed_float : Or_variable.t Numeric_types.Float_by_bit_pattern.t -> t
| Boxed_int32 : Or_variable.t Int32.t -> t
| Boxed_int64 : Or_variable.t Int64.t -> t
| Boxed_nativeint : Or_variable.t Targetint_32_64.t -> t
| Boxed_vec128 : Or_variable.t Vector_types.Vec128.Bit_pattern.t -> t
| Boxed_vec256 : Or_variable.t Vector_types.Vec256.Bit_pattern.t -> t
| Boxed_vec512 : Or_variable.t Vector_types.Vec512.Bit_pattern.t -> t
| Boxed_mask : Or_variable.t Vector_types.Mask.Bit_pattern.t -> t
| Immutable_float_block : list (Or_variable.t Numeric_types.Float_by_bit_pattern.t) -> t
| Immutable_float_array : list (Or_variable.t Numeric_types.Float_by_bit_pattern.t) -> t
| Immutable_float32_array : list (Or_variable.t Numeric_types.Float32_by_bit_pattern.t) -> t
| Immutable_int_array : list (Or_variable.t Target_ocaml_int.t) -> t
| Immutable_int8_array : list (Or_variable.t Numeric_types.Int8.t) -> t
| Immutable_int16_array : list (Or_variable.t Numeric_types.Int16.t) -> t
| Immutable_int32_array : list (Or_variable.t Int32.t) -> t
| Immutable_int64_array : list (Or_variable.t Int64.t) -> t
| Immutable_nativeint_array : list (Or_variable.t Targetint_32_64.t) -> t
| Immutable_vec128_array : list (Or_variable.t Vector_types.Vec128.Bit_pattern.t) -> t
| Immutable_vec256_array : list (Or_variable.t Vector_types.Vec256.Bit_pattern.t) -> t
| Immutable_vec512_array : list (Or_variable.t Vector_types.Vec512.Bit_pattern.t) -> t
| Immutable_mask_array : list (Or_variable.t Vector_types.Mask.Bit_pattern.t) -> t
| Immutable_value_array : list Simple.With_debuginfo.t -> t
| Empty_array : Empty_array_kind.t -> t
| Immutable_string : string -> t.
Module T.
  (* static_const.mli:71  include Container_types.S with type t := t *)
  Definition t : Type := Static_const.t.
  Extract Inlined Constant t => "Static_const.T.t".
End T.
(* static_const.mli:71  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Static_const.T.t -> M unit.
Extract Inlined Constant print => "Static_const.print".
Module Map.
  (* static_const.mli:71  include Container_types.S with type t := t *)
  Definition key : Type := Static_const.t.
  Extract Inlined Constant key => "Static_const.Map.key".
  (* static_const.mli:71  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Static_const.Map.t".
  (* static_const.mli:71  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Static_const.Map.empty".
  (* static_const.mli:71  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Static_const.Map.add".
  (* static_const.mli:71  include Container_types.S with type t := t *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  Extract Inlined Constant find_opt => "Static_const.Map.find_opt".
  (* static_const.mli:71  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Static_const.Map.print".
End Map.
(* static_const.mli:73  include Contains_names.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Static_const.free_names".
(* static_const.mli:77  val set_of_closures : Set_of_closures.t -> t *)
Parameter set_of_closures : Set_of_closures.t -> M t.
Extract Inlined Constant set_of_closures => "Static_const.set_of_closures".
(* static_const.mli:79  val block : Tag.Scannable.t -> Mutability.t -> Flambda_kind.Scannable_block_shape.t -> Simple.With_debuginfo.t list -> t *)
Parameter block : Tag.Scannable.t -> Mutability.t -> Flambda_kind.Scannable_block_shape.t -> list Simple.With_debuginfo.t -> M t.
Extract Inlined Constant block => "Static_const.block".
(* static_const.mli:86  val boxed_float32 : Numeric_types.Float32_by_bit_pattern.t Or_variable.t -> t *)
Parameter boxed_float32 : Or_variable.t Numeric_types.Float32_by_bit_pattern.t -> M t.
Extract Inlined Constant boxed_float32 => "Static_const.boxed_float32".
(* static_const.mli:88  val boxed_float : Numeric_types.Float_by_bit_pattern.t Or_variable.t -> t *)
Parameter boxed_float : Or_variable.t Numeric_types.Float_by_bit_pattern.t -> M t.
Extract Inlined Constant boxed_float => "Static_const.boxed_float".
(* static_const.mli:90  val boxed_int32 : Int32.t Or_variable.t -> t *)
Parameter boxed_int32 : Or_variable.t Int32.t -> M t.
Extract Inlined Constant boxed_int32 => "Static_const.boxed_int32".
(* static_const.mli:92  val boxed_int64 : Int64.t Or_variable.t -> t *)
Parameter boxed_int64 : Or_variable.t Int64.t -> M t.
Extract Inlined Constant boxed_int64 => "Static_const.boxed_int64".
(* static_const.mli:94  val boxed_nativeint : Targetint_32_64.t Or_variable.t -> t *)
Parameter boxed_nativeint : Or_variable.t Targetint_32_64.t -> M t.
Extract Inlined Constant boxed_nativeint => "Static_const.boxed_nativeint".
(* static_const.mli:96  val boxed_vec128 : Vector_types.Vec128.Bit_pattern.t Or_variable.t -> t *)
Parameter boxed_vec128 : Or_variable.t Vector_types.Vec128.Bit_pattern.t -> M t.
Extract Inlined Constant boxed_vec128 => "Static_const.boxed_vec128".
(* static_const.mli:98  val boxed_vec256 : Vector_types.Vec256.Bit_pattern.t Or_variable.t -> t *)
Parameter boxed_vec256 : Or_variable.t Vector_types.Vec256.Bit_pattern.t -> M t.
Extract Inlined Constant boxed_vec256 => "Static_const.boxed_vec256".
(* static_const.mli:100  val boxed_vec512 : Vector_types.Vec512.Bit_pattern.t Or_variable.t -> t *)
Parameter boxed_vec512 : Or_variable.t Vector_types.Vec512.Bit_pattern.t -> M t.
Extract Inlined Constant boxed_vec512 => "Static_const.boxed_vec512".
(* static_const.mli:102  val boxed_mask : Vector_types.Mask.Bit_pattern.t Or_variable.t -> t *)
Parameter boxed_mask : Or_variable.t Vector_types.Mask.Bit_pattern.t -> M t.
Extract Inlined Constant boxed_mask => "Static_const.boxed_mask".
(* static_const.mli:104  val immutable_float_block : Numeric_types.Float_by_bit_pattern.t Or_variable.t list -> t *)
Parameter immutable_float_block : list (Or_variable.t Numeric_types.Float_by_bit_pattern.t) -> M t.
Extract Inlined Constant immutable_float_block => "Static_const.immutable_float_block".
(* static_const.mli:109  val immutable_float_array : Numeric_types.Float_by_bit_pattern.t Or_variable.t list -> t *)
Parameter immutable_float_array : list (Or_variable.t Numeric_types.Float_by_bit_pattern.t) -> M t.
Extract Inlined Constant immutable_float_array => "Static_const.immutable_float_array".
(* static_const.mli:114  val immutable_float32_array : Numeric_types.Float32_by_bit_pattern.t Or_variable.t list -> t *)
Parameter immutable_float32_array : list (Or_variable.t Numeric_types.Float32_by_bit_pattern.t) -> M t.
Extract Inlined Constant immutable_float32_array => "Static_const.immutable_float32_array".
(* static_const.mli:119  val immutable_int_array : Target_ocaml_int.t Or_variable.t list -> t *)
Parameter immutable_int_array : list (Or_variable.t Target_ocaml_int.t) -> M t.
Extract Inlined Constant immutable_int_array => "Static_const.immutable_int_array".
(* static_const.mli:123  val immutable_int8_array : Numeric_types.Int8.t Or_variable.t list -> t *)
Parameter immutable_int8_array : list (Or_variable.t Numeric_types.Int8.t) -> M t.
Extract Inlined Constant immutable_int8_array => "Static_const.immutable_int8_array".
(* static_const.mli:127  val immutable_int16_array : Numeric_types.Int16.t Or_variable.t list -> t *)
Parameter immutable_int16_array : list (Or_variable.t Numeric_types.Int16.t) -> M t.
Extract Inlined Constant immutable_int16_array => "Static_const.immutable_int16_array".
(* static_const.mli:131  val immutable_int32_array : Int32.t Or_variable.t list -> t *)
Parameter immutable_int32_array : list (Or_variable.t Int32.t) -> M t.
Extract Inlined Constant immutable_int32_array => "Static_const.immutable_int32_array".
(* static_const.mli:135  val immutable_int64_array : Int64.t Or_variable.t list -> t *)
Parameter immutable_int64_array : list (Or_variable.t Int64.t) -> M t.
Extract Inlined Constant immutable_int64_array => "Static_const.immutable_int64_array".
(* static_const.mli:139  val immutable_nativeint_array : Targetint_32_64.t Or_variable.t list -> t *)
Parameter immutable_nativeint_array : list (Or_variable.t Targetint_32_64.t) -> M t.
Extract Inlined Constant immutable_nativeint_array => "Static_const.immutable_nativeint_array".
(* static_const.mli:143  val immutable_vec128_array : Vector_types.Vec128.Bit_pattern.t Or_variable.t list -> t *)
Parameter immutable_vec128_array : list (Or_variable.t Vector_types.Vec128.Bit_pattern.t) -> M t.
Extract Inlined Constant immutable_vec128_array => "Static_const.immutable_vec128_array".
(* static_const.mli:148  val immutable_vec256_array : Vector_types.Vec256.Bit_pattern.t Or_variable.t list -> t *)
Parameter immutable_vec256_array : list (Or_variable.t Vector_types.Vec256.Bit_pattern.t) -> M t.
Extract Inlined Constant immutable_vec256_array => "Static_const.immutable_vec256_array".
(* static_const.mli:153  val immutable_vec512_array : Vector_types.Vec512.Bit_pattern.t Or_variable.t list -> t *)
Parameter immutable_vec512_array : list (Or_variable.t Vector_types.Vec512.Bit_pattern.t) -> M t.
Extract Inlined Constant immutable_vec512_array => "Static_const.immutable_vec512_array".
(* static_const.mli:158  val immutable_mask_array : Vector_types.Mask.Bit_pattern.t Or_variable.t list -> t *)
Parameter immutable_mask_array : list (Or_variable.t Vector_types.Mask.Bit_pattern.t) -> M t.
Extract Inlined Constant immutable_mask_array => "Static_const.immutable_mask_array".
(* static_const.mli:163  val immutable_value_array : Simple.With_debuginfo.t list -> t *)
Parameter immutable_value_array : list Simple.With_debuginfo.t -> M t.
Extract Inlined Constant immutable_value_array => "Static_const.immutable_value_array".
(* static_const.mli:165  val empty_array : Empty_array_kind.t -> t *)
Parameter empty_array : Empty_array_kind.t -> M t.
Extract Inlined Constant empty_array => "Static_const.empty_array".
(* static_const.mli:167  val immutable_string : string -> t *)
Parameter immutable_string : string -> M t.
Extract Inlined Constant immutable_string => "Static_const.immutable_string".
(* static_const.mli:177  val can_share : t -> bool *)
Parameter can_share : t -> M bool.
Extract Inlined Constant can_share => "Static_const.can_share".
(* static_const.mli:179  val must_be_set_of_closures : t -> Set_of_closures.t *)
Parameter must_be_set_of_closures : t -> M Set_of_closures.t.
Extract Inlined Constant must_be_set_of_closures => "Static_const.must_be_set_of_closures".
