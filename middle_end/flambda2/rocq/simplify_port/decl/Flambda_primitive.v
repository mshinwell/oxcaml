(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*            Mark Shinwell and Xavier Clerc, Jane Street Europe          *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   Copyright 2017--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flambda_primitive], after its interface
   middle_end/flambda2/terms/flambda_primitive.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Asttypes Flambda_kind Format Function_slot Inlined_attribute Inlined_debuginfo Lambda Mutability Name Name_occurrences Or_unknown Scalar Simple Tag Target_ocaml_int Value_slot Variable_.

Module Lazy_block_tag.
  (* flambda_primitive.mli:29  type t = Lambda.lazy_block_tag = | Lazy_tag | Forward_tag *)
  Definition t : Type := Lambda.lazy_block_tag.
  Extract Inlined Constant t => "Flambda_primitive.Lazy_block_tag.t".
End Lazy_block_tag.
Module Block_kind.
  (* flambda_primitive.mli:41  type t = | Values of Tag.Scannable.t * Flambda_kind.With_subkind.t list | Naked_floats | Mixed of Tag.Scannable.t * Flambda_kind.Mixed_block_shape.t *)
  Inductive t : Type :=
  | Values : Tag.Scannable.t -> list Flambda_kind.With_subkind.t -> t
  | Naked_floats : t
  | Mixed : Tag.Scannable.t -> Flambda_kind.Mixed_block_shape.t -> t.
  (* flambda_primitive.mli:46  val to_shape : t -> Tag.t * Flambda_kind.Block_shape.t *)
  Parameter to_shape : t -> M (Tag.t * Flambda_kind.Block_shape.t).
  Extract Inlined Constant to_shape => "Flambda_primitive.Block_kind.to_shape".
End Block_kind.
Module Array_kind.
  (* flambda_primitive.mli:54  type t = | Immediates ( ** An array consisting only of immediate values. * ) | Gc_ignorable_values ( ** An array consisting of [value]-kind elements that the GC may ignore. * ) | Values ( ** An array consisting of elements of kind [value]. With the float array optimisation enabled, such elements must never be [float]s. * ) | Naked_floats ( ** An array consisting of naked floats, represented usi... *)
  Inductive t : Type :=
  | Immediates : t
  | Gc_ignorable_values : t
  | Values : t
  | Naked_floats : t
  | Naked_float32s : t
  | Naked_ints : t
  | Naked_int8s : t
  | Naked_int16s : t
  | Naked_int32s : t
  | Naked_int64s : t
  | Naked_nativeints : t
  | Naked_vec128s : t
  | Naked_vec256s : t
  | Naked_vec512s : t
  | Naked_masks : t
  | Unboxed_product : list t -> t.
  (* flambda_primitive.mli:81  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda_primitive.Array_kind.print".
  (* flambda_primitive.mli:85  val element_kinds : t -> Flambda_kind.With_subkind.t list *)
  Parameter element_kinds : t -> M (list Flambda_kind.With_subkind.t).
  Extract Inlined Constant element_kinds => "Flambda_primitive.Array_kind.element_kinds".
End Array_kind.
Module Array_kind_for_length.
  (* flambda_primitive.mli:93  type t = | Array_kind of Array_kind.t | Float_array_opt_dynamic *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Array_kind_for_length.t".
End Array_kind_for_length.
Module Init_or_assign.
  (* flambda_primitive.mli:101  type t = | Initialization | Assignment of Alloc_mode.For_assignments.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Init_or_assign.t".
End Init_or_assign.
Module Array_load_kind.
  (* flambda_primitive.mli:109  type t = | Immediates ( ** An array consisting only of immediate values. * ) | Gc_ignorable_values ( ** An array consisting of [value]-kind elements that the GC may ignore. * ) | Values ( ** An array consisting of elements of kind [value]. With the float array optimisation enabled, such elements must never be [float]s. * ) | Naked_floats ( ** An array consisting of naked floats, represented usi... *)
  Inductive t : Type :=
  | Immediates : t
  | Gc_ignorable_values : t
  | Values : t
  | Naked_floats : t
  | Naked_float32s : t
  | Naked_ints : t
  | Naked_int8s : t
  | Naked_int16s : t
  | Naked_int32s : t
  | Naked_int64s : t
  | Naked_nativeints : t
  | Naked_vec128s : t
  | Naked_vec256s : t
  | Naked_vec512s : t
  | Naked_masks : t.
  (* flambda_primitive.mli:136  val kind_of_loaded_value : t -> Flambda_kind.With_subkind.t *)
  Parameter kind_of_loaded_value : t -> M Flambda_kind.With_subkind.t.
  Extract Inlined Constant kind_of_loaded_value => "Flambda_primitive.Array_load_kind.kind_of_loaded_value".
End Array_load_kind.
Module Array_set_kind.
  (* flambda_primitive.mli:140  type t = | Immediates ( ** An array consisting only of immediate values. * ) | Gc_ignorable_values ( ** An array of [value]-kind elements that the GC may ignore. * ) | Values of Init_or_assign.t ( ** An array consisting of elements of kind [value]. With the float array optimisation enabled, such elements must never be [float]s. * ) | Naked_floats ( ** An array consisting of naked floats, repres... *)
  Inductive t : Type :=
  | Immediates : t
  | Gc_ignorable_values : t
  | Values : Flambda_primitive.Init_or_assign.t -> t
  | Naked_floats : t
  | Naked_float32s : t
  | Naked_ints : t
  | Naked_int8s : t
  | Naked_int16s : t
  | Naked_int32s : t
  | Naked_int64s : t
  | Naked_nativeints : t
  | Naked_vec128s : t
  | Naked_vec256s : t
  | Naked_vec512s : t
  | Naked_masks : t.
  (* flambda_primitive.mli:162  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Flambda_primitive.Array_set_kind.print".
End Array_set_kind.
Module Duplicate_block_kind.
  (* flambda_primitive.mli:168  type t = | Values of { tag : Tag.Scannable.t; length : Target_ocaml_int.t } | Naked_floats of { length : Target_ocaml_int.t } | Mixed *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Duplicate_block_kind.t".
End Duplicate_block_kind.
Module Duplicate_array_kind.
  (* flambda_primitive.mli:185  type t = | Immediates | Values | Naked_floats of { length : Target_ocaml_int.t option } | Naked_float32s of { length : Target_ocaml_int.t option } | Naked_ints of { length : Target_ocaml_int.t option } | Naked_int8s of { length : Target_ocaml_int.t option } | Naked_int16s of { length : Target_ocaml_int.t option } | Naked_int32s of { length : Target_ocaml_int.t option } | Naked_int64s of { lengt... *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Duplicate_array_kind.t".
End Duplicate_array_kind.
Module Block_access_field_kind.
  (* flambda_primitive.mli:208  type t = | Any_value | Immediate *)
  Inductive t : Type :=
  | Any_value : t
  | Immediate : t.
End Block_access_field_kind.
Module Mixed_block_access_field_kind.
  (* flambda_primitive.mli:220  type t = | Value_prefix of Block_access_field_kind.t | Flat_suffix of Flambda_kind.Flat_suffix_element.t *)
  Inductive t : Type :=
  | Value_prefix : Flambda_primitive.Block_access_field_kind.t -> t
  | Flat_suffix : Flambda_kind.Flat_suffix_element.t -> t.
End Mixed_block_access_field_kind.
Module Block_access_kind.
  (* flambda_primitive.mli:230  type t = | Values of { tag : Tag.Scannable.t Or_unknown.t; size : Target_ocaml_int.t Or_unknown.t; field_kind : Block_access_field_kind.t } | Naked_floats of { size : Target_ocaml_int.t Or_unknown.t } | Mixed of { tag : Tag.Scannable.t Or_unknown.t; size : Target_ocaml_int.t Or_unknown.t; field_kind : Mixed_block_access_field_kind.t; shape : Flambda_kind.Mixed_block_shape.t } *)
  Record values_payload_ : Type := { tag : Or_unknown.t Tag.Scannable.t; size : Or_unknown.t Target_ocaml_int.t; field_kind : Flambda_primitive.Block_access_field_kind.t }.
  (* The inline record of [Naked_floats]: abstract (a name of its fields is taken, or it holds the type); [mk_Naked_floats] makes one, [match_t] reads it. *)
  Parameter naked_floats_payload_ : Type.
  (* The inline record of [Mixed]: abstract (a name of its fields is taken, or it holds the type); [mk_Mixed] makes one, [match_t] reads it. *)
  Parameter mixed_payload_ : Type.
  Inductive t : Type :=
  | Values : values_payload_ -> t
  | Naked_floats : naked_floats_payload_ -> t
  | Mixed : mixed_payload_ -> t.
  Parameter mk_Values : Or_unknown.t Tag.Scannable.t -> Or_unknown.t Target_ocaml_int.t -> Flambda_primitive.Block_access_field_kind.t -> t.
  Extract Inlined Constant mk_Values => "(fun x__1 x__2 x__3 -> Flambda_primitive.Block_access_kind.Values { tag = x__1; size = x__2; field_kind = x__3 })".
  Parameter mk_Naked_floats : Or_unknown.t Target_ocaml_int.t -> t.
  Extract Inlined Constant mk_Naked_floats => "(fun x__1 -> Flambda_primitive.Block_access_kind.Naked_floats { size = x__1 })".
  Parameter mk_Mixed : Or_unknown.t Tag.Scannable.t -> Or_unknown.t Target_ocaml_int.t -> Flambda_primitive.Mixed_block_access_field_kind.t -> Flambda_kind.Mixed_block_shape.t -> t.
  Extract Inlined Constant mk_Mixed => "(fun x__1 x__2 x__3 x__4 -> Flambda_primitive.Block_access_kind.Mixed { tag = x__1; size = x__2; field_kind = x__3; shape = x__4 })".
  Parameter match_t : forall {Res : Type}, t -> (Or_unknown.t Tag.Scannable.t -> Or_unknown.t Target_ocaml_int.t -> Flambda_primitive.Block_access_field_kind.t -> M Res) -> (Or_unknown.t Target_ocaml_int.t -> M Res) -> (Or_unknown.t Tag.Scannable.t -> Or_unknown.t Target_ocaml_int.t -> Flambda_primitive.Mixed_block_access_field_kind.t -> Flambda_kind.Mixed_block_shape.t -> M Res) -> M Res.
  Extract Inlined Constant match_t => "(fun x__0 f__1 f__2 f__3 -> match x__0 with Flambda_primitive.Block_access_kind.Values { tag = x__1; size = x__2; field_kind = x__3 } -> f__1 x__1 x__2 x__3 | Flambda_primitive.Block_access_kind.Naked_floats { size = x__1 } -> f__2 x__1 | Flambda_primitive.Block_access_kind.Mixed { tag = x__1; size = x__2; field_kind = x__3; shape = x__4 } -> f__3 x__1 x__2 x__3 x__4)".
  (* flambda_primitive.mli:248  val element_kind_for_load : t -> Flambda_kind.t *)
  Parameter element_kind_for_load : t -> M Flambda_kind.t.
  Extract Inlined Constant element_kind_for_load => "Flambda_primitive.Block_access_kind.element_kind_for_load".
  (* flambda_primitive.mli:250  val element_subkind_for_load : t -> Flambda_kind.With_subkind.t *)
  Parameter element_subkind_for_load : t -> M Flambda_kind.With_subkind.t.
  Extract Inlined Constant element_subkind_for_load => "Flambda_primitive.Block_access_kind.element_subkind_for_load".
  (* flambda_primitive.mli:254  val from_block_shape : Flambda_kind.Block_shape.t -> index:Target_ocaml_int.t -> result_kind:Flambda_kind.With_subkind.t -> t *)
  Parameter from_block_shape : Flambda_kind.Block_shape.t -> Target_ocaml_int.t -> Flambda_kind.With_subkind.t -> M t.
  Extract Inlined Constant from_block_shape => "Flambda_primitive.Block_access_kind.from_block_shape".
End Block_access_kind.
(* flambda_primitive.mli:269  type string_or_bytes = | String | Bytes *)
Parameter string_or_bytes : Type.
Extract Inlined Constant string_or_bytes => "Flambda_primitive.string_or_bytes".
(* flambda_primitive.mli:273  type 'signed_or_unsigned comparison = | Eq | Neq | Lt of 'signed_or_unsigned | Gt of 'signed_or_unsigned | Le of 'signed_or_unsigned | Ge of 'signed_or_unsigned *)
Inductive comparison (Signed_or_unsigned : Type) : Type :=
| Eq : comparison Signed_or_unsigned
| Neq : comparison Signed_or_unsigned
| Lt : Signed_or_unsigned -> comparison Signed_or_unsigned
| Gt : Signed_or_unsigned -> comparison Signed_or_unsigned
| Le : Signed_or_unsigned -> comparison Signed_or_unsigned
| Ge : Signed_or_unsigned -> comparison Signed_or_unsigned.
Arguments Eq {Signed_or_unsigned}.
Arguments Neq {Signed_or_unsigned}.
Arguments Lt {Signed_or_unsigned}.
Arguments Gt {Signed_or_unsigned}.
Arguments Le {Signed_or_unsigned}.
Arguments Ge {Signed_or_unsigned}.
(* flambda_primitive.mli:281  type equality_comparison = | Eq | Neq *)
Inductive equality_comparison : Type :=
| Eq_ : equality_comparison
| Neq_ : equality_comparison.
Extract Inductive equality_comparison => "Flambda_primitive.equality_comparison" [ "Flambda_primitive.Eq" "Flambda_primitive.Neq" ].
Module Bigarray_kind.
  (* flambda_primitive.mli:286  type t = | Float16 ( ** This is analogous to [Float32] in that whilst storage is 16-bit, reading and writing goes via 64-bit floats. * ) | Float32 | Float32_t ( ** [Float32_t] is used for bigarrays that contain (unboxed) float32 values and are read and written to using the [float32] type. This is in contrast to [Float32] bigarrays, where the accesses are done at type [float]. * ) | Float64 | Si... *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Bigarray_kind.t".
End Bigarray_kind.
Module Bigarray_layout.
  (* flambda_primitive.mli:316  type t = | C | Fortran *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Bigarray_layout.t".
End Bigarray_layout.
(* flambda_primitive.mli:323  type string_accessor_width = | Eight | Eight_signed | Sixteen | Sixteen_signed | Thirty_two | Single | Sixty_four | One_twenty_eight of { aligned : bool } | Two_fifty_six of { aligned : bool } | Five_twelve of { aligned : bool } | Mask *)
Parameter string_accessor_width : Type.
Extract Inlined Constant string_accessor_width => "Flambda_primitive.string_accessor_width".
(* flambda_primitive.mli:338  type float_bitwidth = | Float32 | Float64 *)
Inductive float_bitwidth : Type :=
| Float32 : float_bitwidth
| Float64 : float_bitwidth.
(* flambda_primitive.mli:342  type string_like_value = | String | Bytes | Bigstring *)
Parameter string_like_value : Type.
Extract Inlined Constant string_like_value => "Flambda_primitive.string_like_value".
(* flambda_primitive.mli:347  type bytes_like_value = | Bytes | Bigstring *)
Parameter bytes_like_value : Type.
Extract Inlined Constant bytes_like_value => "Flambda_primitive.bytes_like_value".
(* flambda_primitive.mli:351  type num_dimensions = int *)
Definition num_dimensions : Type := int.
Extract Inlined Constant num_dimensions => "Flambda_primitive.num_dimensions".
(* flambda_primitive.mli:353  type signed_or_unsigned = | Signed | Unsigned *)
Inductive signed_or_unsigned : Type :=
| Signed : signed_or_unsigned
| Unsigned : signed_or_unsigned.
(* flambda_primitive.mli:358  type nullary_primitive = ( * CR mshinwell: try to remove [Invalid]; we probably shouldn't have two mechanisms for propagating this. * ) | Invalid of Flambda_kind.t ( ** Used when rebuilding a primitive that turns out to be invalid. This is easier to use than turning a whole let-binding into Invalid (which might end up deleting code on the way up, resulting in a typing env out-of-sync with the g... *)
Record probe_is_enabled_payload_ : Type := { name : string; enabled_at_init : option bool }.
Record enter_inlined_apply_payload_ : Type := { dbg : Inlined_debuginfo.t; inlined_attribute : Inlined_attribute.t }.
Inductive nullary_primitive : Type :=
| Invalid : Flambda_kind.t -> nullary_primitive
| Optimised_out : Flambda_kind.t -> nullary_primitive
| Probe_is_enabled : probe_is_enabled_payload_ -> nullary_primitive
| Enter_inlined_apply : enter_inlined_apply_payload_ -> nullary_primitive
| Dls_get : nullary_primitive
| Tls_get : nullary_primitive
| Domain_index : nullary_primitive
| Poll : nullary_primitive
| Cpu_relax : nullary_primitive.
(* flambda_primitive.mli:401  type unary_int_arith_op = | Swap_byte_endianness | Not *)
Inductive unary_int_arith_op : Type :=
| Swap_byte_endianness : unary_int_arith_op
| Not : unary_int_arith_op.
(* flambda_primitive.mli:408  type unary_float_arith_op = | Abs | Neg *)
Inductive unary_float_arith_op : Type :=
| Abs : unary_float_arith_op
| Neg : unary_float_arith_op.
Module Reinterpret_64_bit_word.
  (* flambda_primitive.mli:414  type t = | Tagged_int63_as_unboxed_int64 | Unboxed_int64_as_tagged_int63 | Unboxed_int64_as_unboxed_float64 | Unboxed_float64_as_unboxed_int64 *)
  Inductive t : Type :=
  | Tagged_int63_as_unboxed_int64 : t
  | Unboxed_int64_as_tagged_int63 : t
  | Unboxed_int64_as_unboxed_float64 : t
  | Unboxed_float64_as_unboxed_int64 : t.
End Reinterpret_64_bit_word.
(* flambda_primitive.mli:422  type unary_primitive = | Block_load of { kind : Block_access_kind.t; mut : Mutability.t; field : Target_ocaml_int.t } | Duplicate_block of { kind : Duplicate_block_kind.t; alloc_region : Variable.t } ( ** [Duplicate_block] may not be used to change the tag or the mutability of a block. * ) | Duplicate_array of { kind : Duplicate_array_kind.t; source_mutability : Mutability.t; destination_mutabi... *)
Record block_load_payload_ : Type := { kind : Flambda_primitive.Block_access_kind.t; mut : Mutability.t; field : Target_ocaml_int.t }.
(* The inline record of [Duplicate_block]: abstract (a name of its fields is taken, or it holds the type); [mk_Duplicate_block] makes one, [match_unary_primitive] reads it. *)
Parameter duplicate_block_payload_ : Type.
(* The inline record of [Duplicate_array]: abstract (a name of its fields is taken, or it holds the type); [mk_Duplicate_array] makes one, [match_unary_primitive] reads it. *)
Parameter duplicate_array_payload_ : Type.
Record is_int_payload_ : Type := { variant_only : bool }.
Record bigarray_length_payload_ : Type := { dimension : int }.
(* The inline record of [Opaque_identity]: abstract (a name of its fields is taken, or it holds the type); [mk_Opaque_identity] makes one, [match_unary_primitive] reads it. *)
Parameter opaque_identity_payload_ : Type.
Record num_conv_payload_ : Type := { src : Flambda_kind.Standard_int_or_float.t; dst : Flambda_kind.Standard_int_or_float.t }.
Record project_function_slot_payload_ : Type := { move_from : Function_slot.t; move_to : Function_slot.t }.
Record project_value_slot_payload_ : Type := { project_from : Function_slot.t; value_slot : Value_slot.t }.
Record end_region_payload_ : Type := { ghost : bool }.
Record obj_dup_payload_ : Type := { alloc_region : Variable_.t }.
(* The inline record of [Make_lazy]: abstract (a name of its fields is taken, or it holds the type); [mk_Make_lazy] makes one, [match_unary_primitive] reads it. *)
Parameter make_lazy_payload_ : Type.
Inductive unary_primitive : Type :=
| Block_load : block_load_payload_ -> unary_primitive
| Duplicate_block : duplicate_block_payload_ -> unary_primitive
| Duplicate_array : duplicate_array_payload_ -> unary_primitive
| Is_int : is_int_payload_ -> unary_primitive
| Is_null : unary_primitive
| Get_tag : unary_primitive
| Array_length : Flambda_primitive.Array_kind_for_length.t -> unary_primitive
| Bigarray_length : bigarray_length_payload_ -> unary_primitive
| String_length : string_or_bytes -> unary_primitive
| Int_as_pointer : Alloc_mode.For_allocations.t -> unary_primitive
| Opaque_identity : opaque_identity_payload_ -> unary_primitive
| Int_arith : Flambda_kind.Standard_int.t -> unary_int_arith_op -> unary_primitive
| Float_arith : float_bitwidth -> unary_float_arith_op -> unary_primitive
| Num_conv : num_conv_payload_ -> unary_primitive
| Boolean_not : unary_primitive
| Reinterpret_64_bit_word : Flambda_primitive.Reinterpret_64_bit_word.t -> unary_primitive
| Reinterpret_boxed_vector : unary_primitive
| Unbox_number : Flambda_kind.Boxable_number.t -> unary_primitive
| Box_number : Flambda_kind.Boxable_number.t -> Alloc_mode.For_allocations.t -> unary_primitive
| Untag_immediate : unary_primitive
| Tag_immediate : unary_primitive
| Project_function_slot : project_function_slot_payload_ -> unary_primitive
| Project_value_slot : project_value_slot_payload_ -> unary_primitive
| Is_boxed_float : unary_primitive
| Is_flat_float_array : unary_primitive
| End_region : end_region_payload_ -> unary_primitive
| End_try_region : end_region_payload_ -> unary_primitive
| Obj_dup : obj_dup_payload_ -> unary_primitive
| Get_header : unary_primitive
| Peek : Flambda_kind.Standard_int_or_float.t -> unary_primitive
| Make_lazy : make_lazy_payload_ -> unary_primitive.
Parameter mk_Block_load : Flambda_primitive.Block_access_kind.t -> Mutability.t -> Target_ocaml_int.t -> unary_primitive.
Extract Inlined Constant mk_Block_load => "(fun x__1 x__2 x__3 -> Flambda_primitive.Block_load { kind = x__1; mut = x__2; field = x__3 })".
Parameter mk_Duplicate_block : Flambda_primitive.Duplicate_block_kind.t -> Variable_.t -> unary_primitive.
Extract Inlined Constant mk_Duplicate_block => "(fun x__1 x__2 -> Flambda_primitive.Duplicate_block { kind = x__1; alloc_region = x__2 })".
Parameter mk_Duplicate_array : Flambda_primitive.Duplicate_array_kind.t -> Mutability.t -> Mutability.t -> Variable_.t -> unary_primitive.
Extract Inlined Constant mk_Duplicate_array => "(fun x__1 x__2 x__3 x__4 -> Flambda_primitive.Duplicate_array { kind = x__1; source_mutability = x__2; destination_mutability = x__3; alloc_region = x__4 })".
Parameter mk_Is_int : bool -> unary_primitive.
Extract Inlined Constant mk_Is_int => "(fun x__1 -> Flambda_primitive.Is_int { variant_only = x__1 })".
Parameter mk_Is_null : unary_primitive.
Extract Inlined Constant mk_Is_null => "Flambda_primitive.Is_null".
Parameter mk_Get_tag : unary_primitive.
Extract Inlined Constant mk_Get_tag => "Flambda_primitive.Get_tag".
Parameter mk_Array_length : Flambda_primitive.Array_kind_for_length.t -> unary_primitive.
Extract Inlined Constant mk_Array_length => "(fun x__1 -> Flambda_primitive.Array_length x__1)".
Parameter mk_Bigarray_length : int -> unary_primitive.
Extract Inlined Constant mk_Bigarray_length => "(fun x__1 -> Flambda_primitive.Bigarray_length { dimension = x__1 })".
Parameter mk_String_length : string_or_bytes -> unary_primitive.
Extract Inlined Constant mk_String_length => "(fun x__1 -> Flambda_primitive.String_length x__1)".
Parameter mk_Int_as_pointer : Alloc_mode.For_allocations.t -> unary_primitive.
Extract Inlined Constant mk_Int_as_pointer => "(fun x__1 -> Flambda_primitive.Int_as_pointer x__1)".
Parameter mk_Opaque_identity : bool -> Flambda_kind.t -> unary_primitive.
Extract Inlined Constant mk_Opaque_identity => "(fun x__1 x__2 -> Flambda_primitive.Opaque_identity { middle_end_only = x__1; kind = x__2 })".
Parameter mk_Int_arith : Flambda_kind.Standard_int.t -> unary_int_arith_op -> unary_primitive.
Extract Inlined Constant mk_Int_arith => "(fun x__1 x__2 -> Flambda_primitive.Int_arith (x__1, x__2))".
Parameter mk_Float_arith : float_bitwidth -> unary_float_arith_op -> unary_primitive.
Extract Inlined Constant mk_Float_arith => "(fun x__1 x__2 -> Flambda_primitive.Float_arith (x__1, x__2))".
Parameter mk_Num_conv : Flambda_kind.Standard_int_or_float.t -> Flambda_kind.Standard_int_or_float.t -> unary_primitive.
Extract Inlined Constant mk_Num_conv => "(fun x__1 x__2 -> Flambda_primitive.Num_conv { src = x__1; dst = x__2 })".
Parameter mk_Boolean_not : unary_primitive.
Extract Inlined Constant mk_Boolean_not => "Flambda_primitive.Boolean_not".
Parameter mk_Reinterpret_64_bit_word : Flambda_primitive.Reinterpret_64_bit_word.t -> unary_primitive.
Extract Inlined Constant mk_Reinterpret_64_bit_word => "(fun x__1 -> Flambda_primitive.Reinterpret_64_bit_word x__1)".
Parameter mk_Reinterpret_boxed_vector : unary_primitive.
Extract Inlined Constant mk_Reinterpret_boxed_vector => "Flambda_primitive.Reinterpret_boxed_vector".
Parameter mk_Unbox_number : Flambda_kind.Boxable_number.t -> unary_primitive.
Extract Inlined Constant mk_Unbox_number => "(fun x__1 -> Flambda_primitive.Unbox_number x__1)".
Parameter mk_Box_number : Flambda_kind.Boxable_number.t -> Alloc_mode.For_allocations.t -> unary_primitive.
Extract Inlined Constant mk_Box_number => "(fun x__1 x__2 -> Flambda_primitive.Box_number (x__1, x__2))".
Parameter mk_Untag_immediate : unary_primitive.
Extract Inlined Constant mk_Untag_immediate => "Flambda_primitive.Untag_immediate".
Parameter mk_Tag_immediate : unary_primitive.
Extract Inlined Constant mk_Tag_immediate => "Flambda_primitive.Tag_immediate".
Parameter mk_Project_function_slot : Function_slot.t -> Function_slot.t -> unary_primitive.
Extract Inlined Constant mk_Project_function_slot => "(fun x__1 x__2 -> Flambda_primitive.Project_function_slot { move_from = x__1; move_to = x__2 })".
Parameter mk_Project_value_slot : Function_slot.t -> Value_slot.t -> unary_primitive.
Extract Inlined Constant mk_Project_value_slot => "(fun x__1 x__2 -> Flambda_primitive.Project_value_slot { project_from = x__1; value_slot = x__2 })".
Parameter mk_Is_boxed_float : unary_primitive.
Extract Inlined Constant mk_Is_boxed_float => "Flambda_primitive.Is_boxed_float".
Parameter mk_Is_flat_float_array : unary_primitive.
Extract Inlined Constant mk_Is_flat_float_array => "Flambda_primitive.Is_flat_float_array".
Parameter mk_End_region : bool -> unary_primitive.
Extract Inlined Constant mk_End_region => "(fun x__1 -> Flambda_primitive.End_region { ghost = x__1 })".
Parameter mk_End_try_region : bool -> unary_primitive.
Extract Inlined Constant mk_End_try_region => "(fun x__1 -> Flambda_primitive.End_try_region { ghost = x__1 })".
Parameter mk_Obj_dup : Variable_.t -> unary_primitive.
Extract Inlined Constant mk_Obj_dup => "(fun x__1 -> Flambda_primitive.Obj_dup { alloc_region = x__1 })".
Parameter mk_Get_header : unary_primitive.
Extract Inlined Constant mk_Get_header => "Flambda_primitive.Get_header".
Parameter mk_Peek : Flambda_kind.Standard_int_or_float.t -> unary_primitive.
Extract Inlined Constant mk_Peek => "(fun x__1 -> Flambda_primitive.Peek x__1)".
Parameter mk_Make_lazy : Flambda_primitive.Lazy_block_tag.t -> Variable_.t -> unary_primitive.
Extract Inlined Constant mk_Make_lazy => "(fun x__1 x__2 -> Flambda_primitive.Make_lazy { lazy_tag = x__1; alloc_region = x__2 })".
Parameter match_unary_primitive : forall {Res : Type}, unary_primitive -> (Flambda_primitive.Block_access_kind.t -> Mutability.t -> Target_ocaml_int.t -> M Res) -> (Flambda_primitive.Duplicate_block_kind.t -> Variable_.t -> M Res) -> (Flambda_primitive.Duplicate_array_kind.t -> Mutability.t -> Mutability.t -> Variable_.t -> M Res) -> (bool -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (Flambda_primitive.Array_kind_for_length.t -> M Res) -> (int -> M Res) -> (string_or_bytes -> M Res) -> (Alloc_mode.For_allocations.t -> M Res) -> (bool -> Flambda_kind.t -> M Res) -> (Flambda_kind.Standard_int.t -> unary_int_arith_op -> M Res) -> (float_bitwidth -> unary_float_arith_op -> M Res) -> (Flambda_kind.Standard_int_or_float.t -> Flambda_kind.Standard_int_or_float.t -> M Res) -> (unit -> M Res) -> (Flambda_primitive.Reinterpret_64_bit_word.t -> M Res) -> (unit -> M Res) -> (Flambda_kind.Boxable_number.t -> M Res) -> (Flambda_kind.Boxable_number.t -> Alloc_mode.For_allocations.t -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (Function_slot.t -> Function_slot.t -> M Res) -> (Function_slot.t -> Value_slot.t -> M Res) -> (unit -> M Res) -> (unit -> M Res) -> (bool -> M Res) -> (bool -> M Res) -> (Variable_.t -> M Res) -> (unit -> M Res) -> (Flambda_kind.Standard_int_or_float.t -> M Res) -> (Flambda_primitive.Lazy_block_tag.t -> Variable_.t -> M Res) -> M Res.
Extract Inlined Constant match_unary_primitive => "(fun x__0 f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 f__9 f__10 f__11 f__12 f__13 f__14 f__15 f__16 f__17 f__18 f__19 f__20 f__21 f__22 f__23 f__24 f__25 f__26 f__27 f__28 f__29 f__30 f__31 -> match x__0 with Flambda_primitive.Block_load { kind = x__1; mut = x__2; field = x__3 } -> f__1 x__1 x__2 x__3 | Flambda_primitive.Duplicate_block { kind = x__1; alloc_region = x__2 } -> f__2 x__1 x__2 | Flambda_primitive.Duplicate_array { kind = x__1; source_mutability = x__2; destination_mutability = x__3; alloc_region = x__4 } -> f__3 x__1 x__2 x__3 x__4 | Flambda_primitive.Is_int { variant_only = x__1 } -> f__4 x__1 | Flambda_primitive.Is_null -> f__5 () | Flambda_primitive.Get_tag -> f__6 () | Flambda_primitive.Array_length x__1 -> f__7 x__1 | Flambda_primitive.Bigarray_length { dimension = x__1 } -> f__8 x__1 | Flambda_primitive.String_length x__1 -> f__9 x__1 | Flambda_primitive.Int_as_pointer x__1 -> f__10 x__1 | Flambda_primitive.Opaque_identity { middle_end_only = x__1; kind = x__2 } -> f__11 x__1 x__2 | Flambda_primitive.Int_arith (x__1, x__2) -> f__12 x__1 x__2 | Flambda_primitive.Float_arith (x__1, x__2) -> f__13 x__1 x__2 | Flambda_primitive.Num_conv { src = x__1; dst = x__2 } -> f__14 x__1 x__2 | Flambda_primitive.Boolean_not -> f__15 () | Flambda_primitive.Reinterpret_64_bit_word x__1 -> f__16 x__1 | Flambda_primitive.Reinterpret_boxed_vector -> f__17 () | Flambda_primitive.Unbox_number x__1 -> f__18 x__1 | Flambda_primitive.Box_number (x__1, x__2) -> f__19 x__1 x__2 | Flambda_primitive.Untag_immediate -> f__20 () | Flambda_primitive.Tag_immediate -> f__21 () | Flambda_primitive.Project_function_slot { move_from = x__1; move_to = x__2 } -> f__22 x__1 x__2 | Flambda_primitive.Project_value_slot { project_from = x__1; value_slot = x__2 } -> f__23 x__1 x__2 | Flambda_primitive.Is_boxed_float -> f__24 () | Flambda_primitive.Is_flat_float_array -> f__25 () | Flambda_primitive.End_region { ghost = x__1 } -> f__26 x__1 | Flambda_primitive.End_try_region { ghost = x__1 } -> f__27 x__1 | Flambda_primitive.Obj_dup { alloc_region = x__1 } -> f__28 x__1 | Flambda_primitive.Get_header -> f__29 () | Flambda_primitive.Peek x__1 -> f__30 x__1 | Flambda_primitive.Make_lazy { lazy_tag = x__1; alloc_region = x__2 } -> f__31 x__1 x__2)".
(* flambda_primitive.mli:525  type 'signed_or_unsigned comparison_behaviour = | Yielding_bool of 'signed_or_unsigned comparison | Yielding_int_like_compare_functions of 'signed_or_unsigned *)
Inductive comparison_behaviour (Signed_or_unsigned : Type) : Type :=
| Yielding_bool : comparison Signed_or_unsigned -> comparison_behaviour Signed_or_unsigned
| Yielding_int_like_compare_functions : Signed_or_unsigned -> comparison_behaviour Signed_or_unsigned.
Arguments Yielding_bool {Signed_or_unsigned}.
Arguments Yielding_int_like_compare_functions {Signed_or_unsigned}.
(* flambda_primitive.mli:530  type binary_int_arith_op = | Add | Sub | Mul | Div of Scalar.Signedness.t | Mod of Scalar.Signedness.t | And | Or | Xor *)
Inductive binary_int_arith_op : Type :=
| Add : binary_int_arith_op
| Sub : binary_int_arith_op
| Mul : binary_int_arith_op
| Div : Scalar.Signedness.t -> binary_int_arith_op
| Mod : Scalar.Signedness.t -> binary_int_arith_op
| And : binary_int_arith_op
| Or : binary_int_arith_op
| Xor : binary_int_arith_op.
(* flambda_primitive.mli:541  type int_shift_op = | Lsl | Lsr | Asr *)
Inductive int_shift_op : Type :=
| Lsl : int_shift_op
| Lsr : int_shift_op
| Asr : int_shift_op.
(* flambda_primitive.mli:547  type binary_float_arith_op = | Add | Sub | Mul | Div *)
Inductive binary_float_arith_op : Type :=
| Add_ : binary_float_arith_op
| Sub_ : binary_float_arith_op
| Mul_ : binary_float_arith_op
| Div_ : binary_float_arith_op.
Extract Inductive binary_float_arith_op => "Flambda_primitive.binary_float_arith_op" [ "Flambda_primitive.Add" "Flambda_primitive.Sub" "Flambda_primitive.Mul" "Flambda_primitive.Div" ].
(* flambda_primitive.mli:553  type atomic_offset_units = | Field_index | Byte_offset *)
Parameter atomic_offset_units : Type.
Extract Inlined Constant atomic_offset_units => "Flambda_primitive.atomic_offset_units".
(* flambda_primitive.mli:558  type binary_primitive = | Block_set of { kind : Block_access_kind.t; init : Init_or_assign.t; field : Target_ocaml_int.t } | Array_load of Array_kind.t * Array_load_kind.t * Mutability.t ( ** Unarized or SIMD array load. The array kind preserves unboxed product information but the load kind and index all correspond to the unarized representation. See also [Array_length], above. * ) | String_or_... *)
(* The inline record of [Block_set]: abstract (a name of its fields is taken, or it holds the type); [mk_Block_set] makes one, [match_binary_primitive] reads it. *)
Parameter block_set_payload_ : Type.
Inductive binary_primitive : Type :=
| Block_set : block_set_payload_ -> binary_primitive
| Array_load : Flambda_primitive.Array_kind.t -> Flambda_primitive.Array_load_kind.t -> Mutability.t -> binary_primitive
| String_or_bigstring_load : string_like_value -> string_accessor_width -> binary_primitive
| Bigarray_load : num_dimensions -> Flambda_primitive.Bigarray_kind.t -> Flambda_primitive.Bigarray_layout.t -> binary_primitive
| Phys_equal : equality_comparison -> binary_primitive
| Int_arith_ : Flambda_kind.Standard_int.t -> binary_int_arith_op -> binary_primitive
| Int_shift : Flambda_kind.Standard_int.t -> int_shift_op -> binary_primitive
| Int_comp : Flambda_kind.Standard_int.t -> comparison_behaviour signed_or_unsigned -> binary_primitive
| Float_arith_ : float_bitwidth -> binary_float_arith_op -> binary_primitive
| Float_comp : float_bitwidth -> comparison_behaviour unit -> binary_primitive
| Bigarray_get_alignment : int -> binary_primitive
| Atomic_load : atomic_offset_units -> Flambda_primitive.Block_access_field_kind.t -> binary_primitive
| Poke : Flambda_kind.Standard_int_or_float.t -> binary_primitive
| Read_offset : Flambda_kind.With_subkind.t -> Asttypes.mutable_flag -> binary_primitive.
Extract Inductive binary_primitive => "Flambda_primitive.binary_primitive" [ "Flambda_primitive.Block_set" "Flambda_primitive.Array_load" "Flambda_primitive.String_or_bigstring_load" "Flambda_primitive.Bigarray_load" "Flambda_primitive.Phys_equal" "Flambda_primitive.Int_arith" "Flambda_primitive.Int_shift" "Flambda_primitive.Int_comp" "Flambda_primitive.Float_arith" "Flambda_primitive.Float_comp" "Flambda_primitive.Bigarray_get_alignment" "Flambda_primitive.Atomic_load" "Flambda_primitive.Poke" "Flambda_primitive.Read_offset" ].
Parameter mk_Block_set : Flambda_primitive.Block_access_kind.t -> Flambda_primitive.Init_or_assign.t -> Target_ocaml_int.t -> binary_primitive.
Extract Inlined Constant mk_Block_set => "(fun x__1 x__2 x__3 -> Flambda_primitive.Block_set { kind = x__1; init = x__2; field = x__3 })".
Parameter mk_Array_load : Flambda_primitive.Array_kind.t -> Flambda_primitive.Array_load_kind.t -> Mutability.t -> binary_primitive.
Extract Inlined Constant mk_Array_load => "(fun x__1 x__2 x__3 -> Flambda_primitive.Array_load (x__1, x__2, x__3))".
Parameter mk_String_or_bigstring_load : string_like_value -> string_accessor_width -> binary_primitive.
Extract Inlined Constant mk_String_or_bigstring_load => "(fun x__1 x__2 -> Flambda_primitive.String_or_bigstring_load (x__1, x__2))".
Parameter mk_Bigarray_load : num_dimensions -> Flambda_primitive.Bigarray_kind.t -> Flambda_primitive.Bigarray_layout.t -> binary_primitive.
Extract Inlined Constant mk_Bigarray_load => "(fun x__1 x__2 x__3 -> Flambda_primitive.Bigarray_load (x__1, x__2, x__3))".
Parameter mk_Phys_equal : equality_comparison -> binary_primitive.
Extract Inlined Constant mk_Phys_equal => "(fun x__1 -> Flambda_primitive.Phys_equal x__1)".
Parameter mk_Int_arith_ : Flambda_kind.Standard_int.t -> binary_int_arith_op -> binary_primitive.
Extract Inlined Constant mk_Int_arith_ => "(fun x__1 x__2 -> Flambda_primitive.Int_arith (x__1, x__2))".
Parameter mk_Int_shift : Flambda_kind.Standard_int.t -> int_shift_op -> binary_primitive.
Extract Inlined Constant mk_Int_shift => "(fun x__1 x__2 -> Flambda_primitive.Int_shift (x__1, x__2))".
Parameter mk_Int_comp : Flambda_kind.Standard_int.t -> comparison_behaviour signed_or_unsigned -> binary_primitive.
Extract Inlined Constant mk_Int_comp => "(fun x__1 x__2 -> Flambda_primitive.Int_comp (x__1, x__2))".
Parameter mk_Float_arith_ : float_bitwidth -> binary_float_arith_op -> binary_primitive.
Extract Inlined Constant mk_Float_arith_ => "(fun x__1 x__2 -> Flambda_primitive.Float_arith (x__1, x__2))".
Parameter mk_Float_comp : float_bitwidth -> comparison_behaviour unit -> binary_primitive.
Extract Inlined Constant mk_Float_comp => "(fun x__1 x__2 -> Flambda_primitive.Float_comp (x__1, x__2))".
Parameter mk_Bigarray_get_alignment : int -> binary_primitive.
Extract Inlined Constant mk_Bigarray_get_alignment => "(fun x__1 -> Flambda_primitive.Bigarray_get_alignment x__1)".
Parameter mk_Atomic_load : atomic_offset_units -> Flambda_primitive.Block_access_field_kind.t -> binary_primitive.
Extract Inlined Constant mk_Atomic_load => "(fun x__1 x__2 -> Flambda_primitive.Atomic_load (x__1, x__2))".
Parameter mk_Poke : Flambda_kind.Standard_int_or_float.t -> binary_primitive.
Extract Inlined Constant mk_Poke => "(fun x__1 -> Flambda_primitive.Poke x__1)".
Parameter mk_Read_offset : Flambda_kind.With_subkind.t -> Asttypes.mutable_flag -> binary_primitive.
Extract Inlined Constant mk_Read_offset => "(fun x__1 x__2 -> Flambda_primitive.Read_offset (x__1, x__2))".
Parameter match_binary_primitive : forall {Res : Type}, binary_primitive -> (Flambda_primitive.Block_access_kind.t -> Flambda_primitive.Init_or_assign.t -> Target_ocaml_int.t -> M Res) -> (Flambda_primitive.Array_kind.t -> Flambda_primitive.Array_load_kind.t -> Mutability.t -> M Res) -> (string_like_value -> string_accessor_width -> M Res) -> (num_dimensions -> Flambda_primitive.Bigarray_kind.t -> Flambda_primitive.Bigarray_layout.t -> M Res) -> (equality_comparison -> M Res) -> (Flambda_kind.Standard_int.t -> binary_int_arith_op -> M Res) -> (Flambda_kind.Standard_int.t -> int_shift_op -> M Res) -> (Flambda_kind.Standard_int.t -> comparison_behaviour signed_or_unsigned -> M Res) -> (float_bitwidth -> binary_float_arith_op -> M Res) -> (float_bitwidth -> comparison_behaviour unit -> M Res) -> (int -> M Res) -> (atomic_offset_units -> Flambda_primitive.Block_access_field_kind.t -> M Res) -> (Flambda_kind.Standard_int_or_float.t -> M Res) -> (Flambda_kind.With_subkind.t -> Asttypes.mutable_flag -> M Res) -> M Res.
Extract Inlined Constant match_binary_primitive => "(fun x__0 f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 f__9 f__10 f__11 f__12 f__13 f__14 -> match x__0 with Flambda_primitive.Block_set { kind = x__1; init = x__2; field = x__3 } -> f__1 x__1 x__2 x__3 | Flambda_primitive.Array_load (x__1, x__2, x__3) -> f__2 x__1 x__2 x__3 | Flambda_primitive.String_or_bigstring_load (x__1, x__2) -> f__3 x__1 x__2 | Flambda_primitive.Bigarray_load (x__1, x__2, x__3) -> f__4 x__1 x__2 x__3 | Flambda_primitive.Phys_equal x__1 -> f__5 x__1 | Flambda_primitive.Int_arith (x__1, x__2) -> f__6 x__1 x__2 | Flambda_primitive.Int_shift (x__1, x__2) -> f__7 x__1 x__2 | Flambda_primitive.Int_comp (x__1, x__2) -> f__8 x__1 x__2 | Flambda_primitive.Float_arith (x__1, x__2) -> f__9 x__1 x__2 | Flambda_primitive.Float_comp (x__1, x__2) -> f__10 x__1 x__2 | Flambda_primitive.Bigarray_get_alignment x__1 -> f__11 x__1 | Flambda_primitive.Atomic_load (x__1, x__2) -> f__12 x__1 x__2 | Flambda_primitive.Poke x__1 -> f__13 x__1 | Flambda_primitive.Read_offset (x__1, x__2) -> f__14 x__1 x__2)".
(* flambda_primitive.mli:588  type int_atomic_op = | Fetch_add | Add | Sub | And | Or | Xor *)
Parameter int_atomic_op : Type.
Extract Inlined Constant int_atomic_op => "Flambda_primitive.int_atomic_op".
Module Write_offset_kind.
  (* flambda_primitive.mli:597  type t = | Into_block | Into_block_or_off_heap *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Write_offset_kind.t".
End Write_offset_kind.
(* flambda_primitive.mli:605  type ternary_primitive = | Array_set of Array_kind.t * Array_set_kind.t ( ** Unarized array update, for mutable arrays. See [Array_load] above for more details on the unarization. * ) | Bytes_or_bigstring_set of bytes_like_value * string_accessor_width | Bigarray_set of num_dimensions * Bigarray_kind.t * Bigarray_layout.t | Atomic_int_arith of atomic_offset_units * int_atomic_op | Atomic_set of... *)
Inductive ternary_primitive : Type :=
| Array_set : Flambda_primitive.Array_kind.t -> Flambda_primitive.Array_set_kind.t -> ternary_primitive
| Bytes_or_bigstring_set : bytes_like_value -> string_accessor_width -> ternary_primitive
| Bigarray_set : num_dimensions -> Flambda_primitive.Bigarray_kind.t -> Flambda_primitive.Bigarray_layout.t -> ternary_primitive
| Atomic_int_arith : atomic_offset_units -> int_atomic_op -> ternary_primitive
| Atomic_set : atomic_offset_units -> Flambda_primitive.Block_access_field_kind.t -> Alloc_mode.For_assignments.t -> ternary_primitive
| Atomic_exchange : atomic_offset_units -> Flambda_primitive.Block_access_field_kind.t -> Alloc_mode.For_assignments.t -> ternary_primitive
| Write_offset : Flambda_primitive.Write_offset_kind.t -> Flambda_kind.With_subkind.t -> Alloc_mode.For_assignments.t -> ternary_primitive.
(* flambda_primitive.mli:635  type quaternary_primitive = | Atomic_compare_and_set of atomic_offset_units * Block_access_field_kind.t * Alloc_mode.For_assignments.t | Atomic_compare_exchange of { offset_units : atomic_offset_units; atomic_kind : Block_access_field_kind.t; ( ** The kind of values which the atomic can hold. * ) args_kind : Block_access_field_kind.t; ( ** The kind of values which the compare-exchange operation... *)
Record atomic_compare_exchange_payload_ : Type := { offset_units : atomic_offset_units; atomic_kind : Flambda_primitive.Block_access_field_kind.t; args_kind : Flambda_primitive.Block_access_field_kind.t; mode : Alloc_mode.For_assignments.t }.
Inductive quaternary_primitive : Type :=
| Atomic_compare_and_set : atomic_offset_units -> Flambda_primitive.Block_access_field_kind.t -> Alloc_mode.For_assignments.t -> quaternary_primitive
| Atomic_compare_exchange : atomic_compare_exchange_payload_ -> quaternary_primitive.
(* flambda_primitive.mli:653  type variadic_primitive = | Begin_region of { ghost : bool } ( ** Starting delimiter of local allocation region, returning a region name. For regions for the 'try' part of a 'try...with', use [Begin_try_region] (below) instead. * ) | Begin_try_region of { ghost : bool } ( ** Starting delimiter of local allocation region, when used for a 'try' body. * ) | Make_block of Block_kind.t * Mutability.... *)
Inductive variadic_primitive : Type :=
| Begin_region : end_region_payload_ -> variadic_primitive
| Begin_try_region : end_region_payload_ -> variadic_primitive
| Make_block : Flambda_primitive.Block_kind.t -> Mutability.t -> Alloc_mode.For_allocations.t -> variadic_primitive
| Make_array : Flambda_primitive.Array_kind.t -> Mutability.t -> Alloc_mode.For_allocations.t -> variadic_primitive.
(* flambda_primitive.mli:667  type t = | Nullary of nullary_primitive | Unary of unary_primitive * Simple.t | Binary of binary_primitive * Simple.t * Simple.t | Ternary of ternary_primitive * Simple.t * Simple.t * Simple.t | Quaternary of quaternary_primitive * Simple.t * Simple.t * Simple.t * Simple.t | Variadic of variadic_primitive * Simple.t list *)
Inductive t : Type :=
| Nullary : nullary_primitive -> t
| Unary : unary_primitive -> Simple.t -> t
| Binary : binary_primitive -> Simple.t -> Simple.t -> t
| Ternary : ternary_primitive -> Simple.t -> Simple.t -> Simple.t -> t
| Quaternary : quaternary_primitive -> Simple.t -> Simple.t -> Simple.t -> Simple.t -> t
| Variadic : variadic_primitive -> list Simple.t -> t.
(* flambda_primitive.mli:676  type primitive_application = t *)
Definition primitive_application : Type := t.
Extract Inlined Constant primitive_application => "Flambda_primitive.primitive_application".
(* flambda_primitive.mli:678  include Contains_names.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Flambda_primitive.free_names".
(* flambda_primitive.mli:682  val args : t -> Simple.t list *)
Parameter args : t -> M (list Simple.t).
Extract Inlined Constant args => "Flambda_primitive.args".
(* flambda_primitive.mli:684  val map_args : (Simple.t -> Simple.t) -> t -> t *)
Parameter map_args : (Simple.t -> M Simple.t) -> t -> M t.
Extract Inlined Constant map_args => "Flambda_primitive.map_args".
Module Without_args.
  (* flambda_primitive.mli:689  type t = | Nullary of nullary_primitive | Unary of unary_primitive | Binary of binary_primitive | Ternary of ternary_primitive | Quaternary of quaternary_primitive | Variadic of variadic_primitive *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Without_args.t".
End Without_args.
(* flambda_primitive.mli:708  val without_args : t -> Without_args.t *)
Parameter without_args : t -> M Flambda_primitive.Without_args.t.
Extract Inlined Constant without_args => "Flambda_primitive.without_args".
(* flambda_primitive.mli:712  val arg_kind_of_unary_primitive : unary_primitive -> Flambda_kind.t *)
Parameter arg_kind_of_unary_primitive : unary_primitive -> M Flambda_kind.t.
Extract Inlined Constant arg_kind_of_unary_primitive => "Flambda_primitive.arg_kind_of_unary_primitive".
(* flambda_primitive.mli:714  val args_kind_of_binary_primitive : binary_primitive -> Flambda_kind.t * Flambda_kind.t *)
Parameter args_kind_of_binary_primitive : binary_primitive -> M (Flambda_kind.t * Flambda_kind.t).
Extract Inlined Constant args_kind_of_binary_primitive => "Flambda_primitive.args_kind_of_binary_primitive".
(* flambda_primitive.mli:717  val args_kind_of_ternary_primitive : ternary_primitive -> Flambda_kind.t * Flambda_kind.t * Flambda_kind.t *)
Parameter args_kind_of_ternary_primitive : ternary_primitive -> M (tuple3 Flambda_kind.t Flambda_kind.t Flambda_kind.t).
Extract Inlined Constant args_kind_of_ternary_primitive => "Flambda_primitive.args_kind_of_ternary_primitive".
(* flambda_primitive.mli:720  val args_kind_of_quaternary_primitive : quaternary_primitive -> Flambda_kind.t * Flambda_kind.t * Flambda_kind.t * Flambda_kind.t *)
Parameter args_kind_of_quaternary_primitive : quaternary_primitive -> M (tuple4 Flambda_kind.t Flambda_kind.t Flambda_kind.t Flambda_kind.t).
Extract Inlined Constant args_kind_of_quaternary_primitive => "Flambda_primitive.args_kind_of_quaternary_primitive".
(* flambda_primitive.mli:724  type arg_kinds = | Variadic_mixed of Flambda_kind.Mixed_block_shape.t | Variadic_all_of_kind of Flambda_kind.t | Variadic_zero_or_one of Flambda_kind.t | Variadic_unboxed_product of Flambda_kind.t list *)
Inductive arg_kinds : Type :=
| Variadic_mixed : Flambda_kind.Mixed_block_shape.t -> arg_kinds
| Variadic_all_of_kind : Flambda_kind.t -> arg_kinds
| Variadic_zero_or_one : Flambda_kind.t -> arg_kinds
| Variadic_unboxed_product : list Flambda_kind.t -> arg_kinds.
(* flambda_primitive.mli:730  val args_kind_of_variadic_primitive : variadic_primitive -> arg_kinds *)
Parameter args_kind_of_variadic_primitive : variadic_primitive -> M arg_kinds.
Extract Inlined Constant args_kind_of_variadic_primitive => "Flambda_primitive.args_kind_of_variadic_primitive".
(* flambda_primitive.mli:768  val result_kind' : t -> Flambda_kind.t *)
Parameter result_kind' : t -> M Flambda_kind.t.
Extract Inlined Constant result_kind' => "Flambda_primitive.result_kind'".
(* flambda_primitive.mli:777  val at_most_generative_effects : t -> bool *)
Parameter at_most_generative_effects : t -> M bool.
Extract Inlined Constant at_most_generative_effects => "Flambda_primitive.at_most_generative_effects".
(* flambda_primitive.mli:781  val only_generative_effects : t -> bool *)
Parameter only_generative_effects : t -> M bool.
Extract Inlined Constant only_generative_effects => "Flambda_primitive.only_generative_effects".
Module Eligible_for_cse.
  (* flambda_primitive.mli:788  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_primitive.Eligible_for_cse.t".
  (* flambda_primitive.mli:792  val create : primitive_application -> t option *)
  Parameter create : Flambda_primitive.primitive_application -> M (option t).
  Extract Inlined Constant create => "Flambda_primitive.Eligible_for_cse.create".
  (* flambda_primitive.mli:794  val create_exn : primitive_application -> t *)
  Parameter create_exn : Flambda_primitive.primitive_application -> M t.
  Extract Inlined Constant create_exn => "Flambda_primitive.Eligible_for_cse.create_exn".
  (* flambda_primitive.mli:796  val create_is_int : variant_only:bool -> immediate_or_block:Name.t -> t *)
  Parameter create_is_int : bool -> Name.t -> M t.
  Extract Inlined Constant create_is_int => "Flambda_primitive.Eligible_for_cse.create_is_int".
  (* flambda_primitive.mli:798  val create_get_tag : block:Name.t -> t *)
  Parameter create_get_tag : Name.t -> M t.
  Extract Inlined Constant create_get_tag => "Flambda_primitive.Eligible_for_cse.create_get_tag".
  (* flambda_primitive.mli:802  val to_primitive : t -> primitive_application *)
  Parameter to_primitive : t -> M Flambda_primitive.primitive_application.
  Extract Inlined Constant to_primitive => "Flambda_primitive.Eligible_for_cse.to_primitive".
  (* flambda_primitive.mli:806  val filter_map_args : t -> f:(Simple.t -> Simple.t option) -> t option *)
  Parameter filter_map_args : t -> (Simple.t -> M (option Simple.t)) -> M (option t).
  Extract Inlined Constant filter_map_args => "Flambda_primitive.Eligible_for_cse.filter_map_args".
  Module Map.
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Definition key : Type := Flambda_primitive.Eligible_for_cse.t.
    Extract Inlined Constant key => "Flambda_primitive.Eligible_for_cse.Map.key".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Flambda_primitive.Eligible_for_cse.Map.t".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter empty : forall {A : Type}, t A.
    Extract Inlined Constant empty => "Flambda_primitive.Eligible_for_cse.Map.empty".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    Extract Inlined Constant is_empty => "Flambda_primitive.Eligible_for_cse.Map.is_empty".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter mem : forall {A : Type}, key -> t A -> M bool.
    Extract Inlined Constant mem => "Flambda_primitive.Eligible_for_cse.Map.mem".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    Extract Inlined Constant add => "Flambda_primitive.Eligible_for_cse.Map.add".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter singleton : forall {A : Type}, key -> A -> M (t A).
    Extract Inlined Constant singleton => "Flambda_primitive.Eligible_for_cse.Map.singleton".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold => "Flambda_primitive.Eligible_for_cse.Map.fold".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    Extract Inlined Constant find => "Flambda_primitive.Eligible_for_cse.Map.find".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    Extract Inlined Constant find_opt => "Flambda_primitive.Eligible_for_cse.Map.find_opt".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Flambda_primitive.Eligible_for_cse.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
    (* flambda_primitive.mli:808  include Container_types.S with type t := t *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print => "Flambda_primitive.Eligible_for_cse.Map.print".
  End Map.
End Eligible_for_cse.
Module T.
  (* flambda_primitive.mli:811  include Container_types.S with type t := t *)
  Definition t : Type := Flambda_primitive.t.
  Extract Inlined Constant t => "Flambda_primitive.T.t".
End T.
(* flambda_primitive.mli:811  include Container_types.S with type t := t *)
Parameter compare : Flambda_primitive.T.t -> Flambda_primitive.T.t -> M int.
Extract Inlined Constant compare => "Flambda_primitive.compare".
(* flambda_primitive.mli:811  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Flambda_primitive.T.t -> M unit.
Extract Inlined Constant print => "Flambda_primitive.print".
(* flambda_primitive.mli:828  val compare_primitive_application : compare_simple:(Simple.t -> Simple.t -> int) -> t -> t -> int *)
Parameter compare_primitive_application : (Simple.t -> Simple.t -> M int) -> t -> t -> M int.
Extract Inlined Constant compare_primitive_application => "Flambda_primitive.compare_primitive_application".
(* flambda_primitive.mli:835  val is_end_region : t -> Variable.t option *)
Parameter is_end_region : t -> M (option Variable_.t).
Extract Inlined Constant is_end_region => "Flambda_primitive.is_end_region".
