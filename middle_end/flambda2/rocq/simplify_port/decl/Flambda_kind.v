(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017--2019 OCamlPro SAS                                    *)
(*   Copyright 2017--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flambda_kind], after its interface
   middle_end/flambda2/kinds/flambda_kind.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Tag Target_ocaml_int.

Module Naked_number_kind.
  (* flambda_kind.mli:20  type t = ( * CR mshinwell: I think we should consider renaming [Naked_immediate] to [Naked_int] or (maybe better) [Naked_int31_63], to avoid confusion with [Lambda.Const_naked_immediate]. * ) | Naked_immediate | Naked_float32 | Naked_float | Naked_int8 | Naked_int16 | Naked_int32 | Naked_int64 | Naked_nativeint | Naked_vec128 | Naked_vec256 | Naked_vec512 | Naked_mask *)
  Inductive t : Type :=
  | Naked_immediate : t
  | Naked_float32 : t
  | Naked_float : t
  | Naked_int8 : t
  | Naked_int16 : t
  | Naked_int32 : t
  | Naked_int64 : t
  | Naked_nativeint : t
  | Naked_vec128 : t
  | Naked_vec256 : t
  | Naked_vec512 : t
  | Naked_mask : t.
  Extract Inductive t => "Flambda_kind.Naked_number_kind.t" [ "Flambda_kind.Naked_number_kind.Naked_immediate" "Flambda_kind.Naked_number_kind.Naked_float32" "Flambda_kind.Naked_number_kind.Naked_float" "Flambda_kind.Naked_number_kind.Naked_int8" "Flambda_kind.Naked_number_kind.Naked_int16" "Flambda_kind.Naked_number_kind.Naked_int32" "Flambda_kind.Naked_number_kind.Naked_int64" "Flambda_kind.Naked_number_kind.Naked_nativeint" "Flambda_kind.Naked_number_kind.Naked_vec128" "Flambda_kind.Naked_number_kind.Naked_vec256" "Flambda_kind.Naked_number_kind.Naked_vec512" "Flambda_kind.Naked_number_kind.Naked_mask" ].
  (* flambda_kind.mli:37  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda_kind.Naked_number_kind.print".
End Naked_number_kind.
(* flambda_kind.mli:43  type t = private | Value ( ** OCaml values, either immediates or pointers. * ) | Naked_number of Naked_number_kind.t ( ** The kind of unboxed numbers and untagged immediates. * ) | Region ( ** Values which have been introduced by Flambda and are never accessible at the source language level (for example sets of closures). * ) | Rec_info *)
Inductive t : Type :=
| Value : t
| Naked_number : Flambda_kind.Naked_number_kind.t -> t
| Region : t
| Rec_info : t.
Extract Inductive t => "Flambda_kind.t" [ "Flambda_kind.Value" "Flambda_kind.Naked_number" "Flambda_kind.Region" "Flambda_kind.Rec_info" ].
(* flambda_kind.mli:54  type kind = t *)
Definition kind : Type := t.
Extract Inlined Constant kind => "Flambda_kind.kind".
(* flambda_kind.mli:57  val value : t *)
Parameter value : t.
Extract Inlined Constant value => "Flambda_kind.value".
(* flambda_kind.mli:59  val naked_number : Naked_number_kind.t -> t *)
Parameter naked_number : Flambda_kind.Naked_number_kind.t -> M t.
Extract Inlined Constant naked_number => "Flambda_kind.naked_number".
(* flambda_kind.mli:61  val naked_immediate : t *)
Parameter naked_immediate : t.
Extract Inlined Constant naked_immediate => "Flambda_kind.naked_immediate".
(* flambda_kind.mli:63  val naked_float32 : t *)
Parameter naked_float32 : t.
Extract Inlined Constant naked_float32 => "Flambda_kind.naked_float32".
(* flambda_kind.mli:65  val naked_float : t *)
Parameter naked_float : t.
Extract Inlined Constant naked_float => "Flambda_kind.naked_float".
(* flambda_kind.mli:67  val naked_int8 : t *)
Parameter naked_int8 : t.
Extract Inlined Constant naked_int8 => "Flambda_kind.naked_int8".
(* flambda_kind.mli:69  val naked_int16 : t *)
Parameter naked_int16 : t.
Extract Inlined Constant naked_int16 => "Flambda_kind.naked_int16".
(* flambda_kind.mli:71  val naked_int32 : t *)
Parameter naked_int32 : t.
Extract Inlined Constant naked_int32 => "Flambda_kind.naked_int32".
(* flambda_kind.mli:73  val naked_int64 : t *)
Parameter naked_int64 : t.
Extract Inlined Constant naked_int64 => "Flambda_kind.naked_int64".
(* flambda_kind.mli:75  val naked_nativeint : t *)
Parameter naked_nativeint : t.
Extract Inlined Constant naked_nativeint => "Flambda_kind.naked_nativeint".
(* flambda_kind.mli:77  val naked_vec128 : t *)
Parameter naked_vec128 : t.
Extract Inlined Constant naked_vec128 => "Flambda_kind.naked_vec128".
(* flambda_kind.mli:79  val naked_vec256 : t *)
Parameter naked_vec256 : t.
Extract Inlined Constant naked_vec256 => "Flambda_kind.naked_vec256".
(* flambda_kind.mli:81  val naked_vec512 : t *)
Parameter naked_vec512 : t.
Extract Inlined Constant naked_vec512 => "Flambda_kind.naked_vec512".
(* flambda_kind.mli:83  val naked_mask : t *)
Parameter naked_mask : t.
Extract Inlined Constant naked_mask => "Flambda_kind.naked_mask".
(* flambda_kind.mli:85  val region : t *)
Parameter region : t.
Extract Inlined Constant region => "Flambda_kind.region".
(* flambda_kind.mli:87  val rec_info : t *)
Parameter rec_info : t.
Extract Inlined Constant rec_info => "Flambda_kind.rec_info".
(* flambda_kind.mli:89  val is_value : t -> bool *)
Parameter is_value : t -> M bool.
Extract Inlined Constant is_value => "Flambda_kind.is_value".
Module T.
  (* flambda_kind.mli:93  include Container_types.S with type t := t *)
  Definition t : Type := Flambda_kind.t.
  Extract Inlined Constant t => "Flambda_kind.T.t".
End T.
(* flambda_kind.mli:93  include Container_types.S with type t := t *)
Parameter equal : Flambda_kind.T.t -> Flambda_kind.T.t -> M bool.
Extract Inlined Constant equal => "Flambda_kind.equal".
(* flambda_kind.mli:93  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Flambda_kind.T.t -> M unit.
Extract Inlined Constant print => "Flambda_kind.print".
(* flambda_kind.mli:95  type flat_suffix_element = | Naked_float | Naked_float32 | Naked_int8 | Naked_int16 | Naked_int32 | Naked_int64 | Naked_nativeint | Naked_immediate | Naked_vec128 | Naked_vec256 | Naked_vec512 | Naked_mask *)
Parameter flat_suffix_element : Type.
Extract Inlined Constant flat_suffix_element => "Flambda_kind.flat_suffix_element".
Module Mixed_block_shape.
  (* flambda_kind.mli:112  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_kind.Mixed_block_shape.t".
  (* flambda_kind.mli:114  val field_kinds : t -> kind array *)
  Parameter field_kinds : t -> M (array Flambda_kind.kind).
  Extract Inlined Constant field_kinds => "Flambda_kind.Mixed_block_shape.field_kinds".
  (* flambda_kind.mli:116  val value_prefix_size : t -> int *)
  Parameter value_prefix_size : t -> M int.
  Extract Inlined Constant value_prefix_size => "Flambda_kind.Mixed_block_shape.value_prefix_size".
  (* flambda_kind.mli:118  val flat_suffix : t -> flat_suffix_element array *)
  Parameter flat_suffix : t -> M (array Flambda_kind.flat_suffix_element).
  Extract Inlined Constant flat_suffix => "Flambda_kind.Mixed_block_shape.flat_suffix".
  (* flambda_kind.mli:124  val equal : t -> t -> bool *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Flambda_kind.Mixed_block_shape.equal".
End Mixed_block_shape.
Module Scannable_block_shape.
  (* flambda_kind.mli:135  type t = | Value_only | Mixed_record of Mixed_block_shape.t *)
  Inductive t : Type :=
  | Value_only : t
  | Mixed_record : Flambda_kind.Mixed_block_shape.t -> t.
  Extract Inductive t => "Flambda_kind.Scannable_block_shape.t" [ "Flambda_kind.Scannable_block_shape.Value_only" "Flambda_kind.Scannable_block_shape.Mixed_record" ].
End Scannable_block_shape.
Module Block_shape.
  (* flambda_kind.mli:154  type t = | Scannable of Scannable_block_shape.t | Float_record *)
  Inductive t : Type :=
  | Scannable : Flambda_kind.Scannable_block_shape.t -> t
  | Float_record : t.
  Extract Inductive t => "Flambda_kind.Block_shape.t" [ "Flambda_kind.Block_shape.Scannable" "Flambda_kind.Block_shape.Float_record" ].
  (* flambda_kind.mli:162  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda_kind.Block_shape.print".
  (* flambda_kind.mli:164  val element_kind : t -> int -> kind *)
  Parameter element_kind : t -> int -> M Flambda_kind.kind.
  Extract Inlined Constant element_kind => "Flambda_kind.Block_shape.element_kind".
End Block_shape.
Module Standard_int.
  (* flambda_kind.mli:171  type t = | Tagged_immediate | Naked_immediate | Naked_int8 | Naked_int16 | Naked_int32 | Naked_int64 | Naked_nativeint *)
  Inductive t : Type :=
  | Tagged_immediate : t
  | Naked_immediate : t
  | Naked_int8 : t
  | Naked_int16 : t
  | Naked_int32 : t
  | Naked_int64 : t
  | Naked_nativeint : t.
  Extract Inductive t => "Flambda_kind.Standard_int.t" [ "Flambda_kind.Standard_int.Tagged_immediate" "Flambda_kind.Standard_int.Naked_immediate" "Flambda_kind.Standard_int.Naked_int8" "Flambda_kind.Standard_int.Naked_int16" "Flambda_kind.Standard_int.Naked_int32" "Flambda_kind.Standard_int.Naked_int64" "Flambda_kind.Standard_int.Naked_nativeint" ].
  (* flambda_kind.mli:180  val to_kind : t -> kind *)
  Parameter to_kind : t -> M Flambda_kind.kind.
  Extract Inlined Constant to_kind => "Flambda_kind.Standard_int.to_kind".
  (* flambda_kind.mli:182  val print_lowercase : Format.formatter -> t -> unit *)
  Parameter print_lowercase : Format.formatter -> t -> M unit.
  Extract Inlined Constant print_lowercase => "Flambda_kind.Standard_int.print_lowercase".
End Standard_int.
Module Boxable_number.
  (* flambda_kind.mli:191  type t = | Naked_float32 | Naked_float | Naked_int32 | Naked_int64 | Naked_nativeint | Naked_vec128 | Naked_vec256 | Naked_vec512 | Naked_mask *)
  Inductive t : Type :=
  | Naked_float32 : t
  | Naked_float : t
  | Naked_int32 : t
  | Naked_int64 : t
  | Naked_nativeint : t
  | Naked_vec128 : t
  | Naked_vec256 : t
  | Naked_vec512 : t
  | Naked_mask : t.
  Extract Inductive t => "Flambda_kind.Boxable_number.t" [ "Flambda_kind.Boxable_number.Naked_float32" "Flambda_kind.Boxable_number.Naked_float" "Flambda_kind.Boxable_number.Naked_int32" "Flambda_kind.Boxable_number.Naked_int64" "Flambda_kind.Boxable_number.Naked_nativeint" "Flambda_kind.Boxable_number.Naked_vec128" "Flambda_kind.Boxable_number.Naked_vec256" "Flambda_kind.Boxable_number.Naked_vec512" "Flambda_kind.Boxable_number.Naked_mask" ].
  (* flambda_kind.mli:202  val unboxed_kind : t -> kind *)
  Parameter unboxed_kind : t -> M Flambda_kind.kind.
  Extract Inlined Constant unboxed_kind => "Flambda_kind.Boxable_number.unboxed_kind".
End Boxable_number.
Module With_subkind.
  (* flambda_kind.mli:212  type full_kind *)
  Parameter full_kind : Type.
  Extract Inlined Constant full_kind => "Flambda_kind.With_subkind.full_kind".
  Module Nullable.
    (* flambda_kind.mli:215  type t = | Nullable | Non_nullable *)
    Inductive t : Type :=
    | Nullable : t
    | Non_nullable : t.
    Extract Inductive t => "Flambda_kind.With_subkind.Nullable.t" [ "Flambda_kind.With_subkind.Nullable.Nullable" "Flambda_kind.With_subkind.Nullable.Non_nullable" ].
  End Nullable.
  Module Non_null_value_subkind.
    (* flambda_kind.mli:258  and constructor_shape = | Undetermined | Determined of Block_shape.t * full_kind list *)
    Parameter constructor_shape : Type.
    Extract Inlined Constant constructor_shape => "Flambda_kind.With_subkind.Non_null_value_subkind.constructor_shape".
    (* flambda_kind.mli:224  type t = | Anything | Boxed_float32 | Boxed_float | Boxed_int32 | Boxed_int64 | Boxed_nativeint | Boxed_vec128 | Boxed_vec256 | Boxed_vec512 | Boxed_mask | Tagged_immediate | Variant of { consts : Target_ocaml_int.Set.t; non_consts : constructor_shape Tag.Scannable.Map.t } | Float_block of { num_fields : int } | Float_array | Immediate_array | Value_array | Generic_array | Unboxed_float32_array... *)
    Inductive t : Type :=
    | Anything : t
    | Boxed_float32 : t
    | Boxed_float : t
    | Boxed_int32 : t
    | Boxed_int64 : t
    | Boxed_nativeint : t
    | Boxed_vec128 : t
    | Boxed_vec256 : t
    | Boxed_vec512 : t
    | Boxed_mask : t
    | Tagged_immediate : t
    | Variant : Target_ocaml_int.Set_.t -> Tag.Scannable.Map.t constructor_shape -> t
    | Float_block : int -> t
    | Float_array : t
    | Immediate_array : t
    | Value_array : t
    | Generic_array : t
    | Unboxed_float32_array : t
    | Untagged_int_array : t
    | Untagged_int8_array : t
    | Untagged_int16_array : t
    | Unboxed_int32_array : t
    | Unboxed_int64_array : t
    | Unboxed_nativeint_array : t
    | Unboxed_vec128_array : t
    | Unboxed_vec256_array : t
    | Unboxed_vec512_array : t
    | Unboxed_mask_array : t
    | Unboxed_product_array : t.
    Extract Inductive t => "Flambda_kind.With_subkind.Non_null_value_subkind.t" [ "Flambda_kind.With_subkind.Non_null_value_subkind.Anything" "Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_float32" "Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_float" "Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_int32" "Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_int64" "Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_nativeint" "Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_vec128" "Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_vec256" "Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_vec512" "Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_mask" "Flambda_kind.With_subkind.Non_null_value_subkind.Tagged_immediate" "(fun (x__1, x__2) -> (Flambda_kind.With_subkind.Non_null_value_subkind.Variant { consts = x__1; non_consts = x__2 } : Flambda_kind.With_subkind.Non_null_value_subkind.t))" "(fun x__1 -> (Flambda_kind.With_subkind.Non_null_value_subkind.Float_block { num_fields = x__1 } : Flambda_kind.With_subkind.Non_null_value_subkind.t))" "Flambda_kind.With_subkind.Non_null_value_subkind.Float_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Immediate_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Value_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Generic_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_float32_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Untagged_int_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Untagged_int8_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Untagged_int16_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_int32_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_int64_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_nativeint_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_vec128_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_vec256_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_vec512_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_mask_array" "Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_product_array" ] "(fun f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 f__9 f__10 f__11 f__12 f__13 f__14 f__15 f__16 f__17 f__18 f__19 f__20 f__21 f__22 f__23 f__24 f__25 f__26 f__27 f__28 f__29 x__0 -> match (x__0 : Flambda_kind.With_subkind.Non_null_value_subkind.t) with Flambda_kind.With_subkind.Non_null_value_subkind.Anything -> f__1 () | Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_float32 -> f__2 () | Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_float -> f__3 () | Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_int32 -> f__4 () | Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_int64 -> f__5 () | Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_nativeint -> f__6 () | Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_vec128 -> f__7 () | Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_vec256 -> f__8 () | Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_vec512 -> f__9 () | Flambda_kind.With_subkind.Non_null_value_subkind.Boxed_mask -> f__10 () | Flambda_kind.With_subkind.Non_null_value_subkind.Tagged_immediate -> f__11 () | Flambda_kind.With_subkind.Non_null_value_subkind.Variant { consts = x__1; non_consts = x__2 } -> f__12 x__1 x__2 | Flambda_kind.With_subkind.Non_null_value_subkind.Float_block { num_fields = x__1 } -> f__13 x__1 | Flambda_kind.With_subkind.Non_null_value_subkind.Float_array -> f__14 () | Flambda_kind.With_subkind.Non_null_value_subkind.Immediate_array -> f__15 () | Flambda_kind.With_subkind.Non_null_value_subkind.Value_array -> f__16 () | Flambda_kind.With_subkind.Non_null_value_subkind.Generic_array -> f__17 () | Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_float32_array -> f__18 () | Flambda_kind.With_subkind.Non_null_value_subkind.Untagged_int_array -> f__19 () | Flambda_kind.With_subkind.Non_null_value_subkind.Untagged_int8_array -> f__20 () | Flambda_kind.With_subkind.Non_null_value_subkind.Untagged_int16_array -> f__21 () | Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_int32_array -> f__22 () | Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_int64_array -> f__23 () | Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_nativeint_array -> f__24 () | Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_vec128_array -> f__25 () | Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_vec256_array -> f__26 () | Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_vec512_array -> f__27 () | Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_mask_array -> f__28 () | Flambda_kind.With_subkind.Non_null_value_subkind.Unboxed_product_array -> f__29 ())".
  End Non_null_value_subkind.
  (* flambda_kind.mli:265  type t = full_kind *)
  Definition t : Type := full_kind.
  Extract Inlined Constant t => "Flambda_kind.With_subkind.t".
  (* flambda_kind.mli:267  val create : kind -> Non_null_value_subkind.t -> Nullable.t -> t *)
  Parameter create : Flambda_kind.kind -> Flambda_kind.With_subkind.Non_null_value_subkind.t -> Flambda_kind.With_subkind.Nullable.t -> M t.
  Extract Inlined Constant create => "Flambda_kind.With_subkind.create".
  (* flambda_kind.mli:269  val anything : kind -> t *)
  Parameter anything : Flambda_kind.kind -> M t.
  Extract Inlined Constant anything => "Flambda_kind.With_subkind.anything".
  (* flambda_kind.mli:271  val kind : t -> kind *)
  Parameter kind : t -> M Flambda_kind.kind.
  Extract Inlined Constant kind => "Flambda_kind.With_subkind.kind".
  (* flambda_kind.mli:273  val non_null_value_subkind : t -> Non_null_value_subkind.t *)
  Parameter non_null_value_subkind : t -> M Flambda_kind.With_subkind.Non_null_value_subkind.t.
  Extract Inlined Constant non_null_value_subkind => "Flambda_kind.With_subkind.non_null_value_subkind".
  (* flambda_kind.mli:277  val has_useful_subkind_info : t -> bool *)
  Parameter has_useful_subkind_info : t -> M bool.
  Extract Inlined Constant has_useful_subkind_info => "Flambda_kind.With_subkind.has_useful_subkind_info".
  (* flambda_kind.mli:282  val any_value : t *)
  Parameter any_value : t.
  Extract Inlined Constant any_value => "Flambda_kind.With_subkind.any_value".
  (* flambda_kind.mli:284  val naked_immediate : t *)
  Parameter naked_immediate : t.
  Extract Inlined Constant naked_immediate => "Flambda_kind.With_subkind.naked_immediate".
  (* flambda_kind.mli:286  val naked_float32 : t *)
  Parameter naked_float32 : t.
  Extract Inlined Constant naked_float32 => "Flambda_kind.With_subkind.naked_float32".
  (* flambda_kind.mli:288  val naked_float : t *)
  Parameter naked_float : t.
  Extract Inlined Constant naked_float => "Flambda_kind.With_subkind.naked_float".
  (* flambda_kind.mli:290  val naked_int8 : t *)
  Parameter naked_int8 : t.
  Extract Inlined Constant naked_int8 => "Flambda_kind.With_subkind.naked_int8".
  (* flambda_kind.mli:292  val naked_int16 : t *)
  Parameter naked_int16 : t.
  Extract Inlined Constant naked_int16 => "Flambda_kind.With_subkind.naked_int16".
  (* flambda_kind.mli:294  val naked_int32 : t *)
  Parameter naked_int32 : t.
  Extract Inlined Constant naked_int32 => "Flambda_kind.With_subkind.naked_int32".
  (* flambda_kind.mli:296  val naked_int64 : t *)
  Parameter naked_int64 : t.
  Extract Inlined Constant naked_int64 => "Flambda_kind.With_subkind.naked_int64".
  (* flambda_kind.mli:298  val naked_nativeint : t *)
  Parameter naked_nativeint : t.
  Extract Inlined Constant naked_nativeint => "Flambda_kind.With_subkind.naked_nativeint".
  (* flambda_kind.mli:300  val naked_vec128 : t *)
  Parameter naked_vec128 : t.
  Extract Inlined Constant naked_vec128 => "Flambda_kind.With_subkind.naked_vec128".
  (* flambda_kind.mli:302  val naked_vec256 : t *)
  Parameter naked_vec256 : t.
  Extract Inlined Constant naked_vec256 => "Flambda_kind.With_subkind.naked_vec256".
  (* flambda_kind.mli:304  val naked_vec512 : t *)
  Parameter naked_vec512 : t.
  Extract Inlined Constant naked_vec512 => "Flambda_kind.With_subkind.naked_vec512".
  (* flambda_kind.mli:306  val naked_mask : t *)
  Parameter naked_mask : t.
  Extract Inlined Constant naked_mask => "Flambda_kind.With_subkind.naked_mask".
  (* flambda_kind.mli:308  val region : t *)
  Parameter region : t.
  Extract Inlined Constant region => "Flambda_kind.With_subkind.region".
  (* flambda_kind.mli:324  val rec_info : t *)
  Parameter rec_info : t.
  Extract Inlined Constant rec_info => "Flambda_kind.With_subkind.rec_info".
  (* flambda_kind.mli:348  val of_naked_number_kind : Naked_number_kind.t -> t *)
  Parameter of_naked_number_kind : Flambda_kind.Naked_number_kind.t -> M t.
  Extract Inlined Constant of_naked_number_kind => "Flambda_kind.With_subkind.of_naked_number_kind".
  Module T.
    (* flambda_kind.mli:366  include Container_types.S with type t := t *)
    Definition t : Type := Flambda_kind.With_subkind.t.
    Extract Inlined Constant t => "Flambda_kind.With_subkind.T.t".
  End T.
  (* flambda_kind.mli:366  include Container_types.S with type t := t *)
  Parameter equal : Flambda_kind.With_subkind.T.t -> Flambda_kind.With_subkind.T.t -> M bool.
  Extract Inlined Constant equal => "Flambda_kind.With_subkind.equal".
  (* flambda_kind.mli:366  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> Flambda_kind.With_subkind.T.t -> M unit.
  Extract Inlined Constant print => "Flambda_kind.With_subkind.print".
End With_subkind.
Module Flat_suffix_element.
  (* flambda_kind.mli:374  type t = flat_suffix_element *)
  Definition t : Type := Flambda_kind.flat_suffix_element.
  Extract Inlined Constant t => "Flambda_kind.Flat_suffix_element.t".
  (* flambda_kind.mli:378  val kind : t -> kind *)
  Parameter kind : t -> M Flambda_kind.kind.
  Extract Inlined Constant kind => "Flambda_kind.Flat_suffix_element.kind".
End Flat_suffix_element.
Module Standard_int_or_float.
  (* flambda_kind.mli:392  type t = | Tagged_immediate | Naked_immediate | Naked_float32 | Naked_float | Naked_int8 | Naked_int16 | Naked_int32 | Naked_int64 | Naked_nativeint *)
  Inductive t : Type :=
  | Tagged_immediate : t
  | Naked_immediate : t
  | Naked_float32 : t
  | Naked_float : t
  | Naked_int8 : t
  | Naked_int16 : t
  | Naked_int32 : t
  | Naked_int64 : t
  | Naked_nativeint : t.
  Extract Inductive t => "Flambda_kind.Standard_int_or_float.t" [ "Flambda_kind.Standard_int_or_float.Tagged_immediate" "Flambda_kind.Standard_int_or_float.Naked_immediate" "Flambda_kind.Standard_int_or_float.Naked_float32" "Flambda_kind.Standard_int_or_float.Naked_float" "Flambda_kind.Standard_int_or_float.Naked_int8" "Flambda_kind.Standard_int_or_float.Naked_int16" "Flambda_kind.Standard_int_or_float.Naked_int32" "Flambda_kind.Standard_int_or_float.Naked_int64" "Flambda_kind.Standard_int_or_float.Naked_nativeint" ].
  (* flambda_kind.mli:405  val to_kind : t -> kind *)
  Parameter to_kind : t -> M Flambda_kind.kind.
  Extract Inlined Constant to_kind => "Flambda_kind.Standard_int_or_float.to_kind".
  Module T.
    (* flambda_kind.mli:411  include Container_types.S with type t := t *)
    Definition t : Type := Flambda_kind.Standard_int_or_float.t.
    Extract Inlined Constant t => "Flambda_kind.Standard_int_or_float.T.t".
  End T.
  (* flambda_kind.mli:411  include Container_types.S with type t := t *)
  Parameter equal : Flambda_kind.Standard_int_or_float.T.t -> Flambda_kind.Standard_int_or_float.T.t -> M bool.
  Extract Inlined Constant equal => "Flambda_kind.Standard_int_or_float.equal".
End Standard_int_or_float.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Flambda_kind. End Flambda_kind.
