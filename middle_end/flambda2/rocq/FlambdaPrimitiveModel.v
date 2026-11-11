(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(* The primitives of Flambda 2 as the semantics sees them: a fragment.

   This file is to be reviewed, against
   middle_end/flambda2/terms/flambda_primitive.mli. It holds definitions
   only: the types of the primitives without their arguments. What each
   computes is FlambdaPrimitiveSpec.v.

   The fragment has, with the compiler's names:
   - of [unary_primitive]: [Block_load] from an immutable block of
     values, [Is_int], [Is_null], [Get_tag], [String_length] of a
     string, [Opaque_identity], [Num_conv] between the integer kinds,
     [Boolean_not], [Unbox_number], [Box_number], [Untag_immediate] and
     [Tag_immediate];
   - of [binary_primitive]: [Int_arith], [Int_shift] and [Int_comp], at
     every [Standard_int.t], and [Phys_equal];
   - of [variadic_primitive]: [Make_block] of an immutable block of
     values.
   Every other primitive is left out. The conversion from the compiler's
   terms must refuse a primitive that is not here, and a primitive whose
   fields have a value that is not here; it must never approximate one.

   Differences from the compiler:
   - [Opaque_identity] has no [middle_end_only], which has no effect on
     execution.
   - [Box_number] and [Make_block] have no allocation mode: they are the
     allocations on the heap, and the conversion must refuse a local one.
   - [Block_load] and [Make_block] have no mutability: they are those of
     immutable blocks ([Immutable], not [Immutable_unique]), and the
     conversion must refuse the others. The only [Block_access_kind.t]
     and [Block_kind.t] are those of blocks of values, [Values]; an
     [Or_unknown.t] is an [option], [Unknown] being [None].
   - [Block_kind.Values] has no list of the kinds of the fields. In the
     compiler each has a subkind, which Simplify takes an argument that
     is a variable to be of ([Simplify_variadic_primitive]). The model
     has no subkinds, so the conversion must refuse a list that says
     more of a field than [any_value].
   - A tag is any integer, where the compiler's [Tag.Scannable.t] is at
     least 0 and below 251. The field and the size of a [Block_load]
     are any integers too, where the compiler's are signed integers of
     63 bits ([Target_ocaml_int.t]). A primitive with a number out of
     its range is one the compiler cannot build. No type here refuses
     it: FlambdaPrimitiveSpec.prim_in_range is the test, and a unit
     that passes the check FlambdaWellFormedSpec.numbers_in_range has
     no such primitive.
   - The comparisons are those of integers only: the compiler's
     [comparison] and [comparison_behaviour] are polymorphic in the
     signedness so as to serve the floats too, which are not here. Their
     constructors are prefixed with [Int_], as [Eq], [Lt] and [Gt] are
     Rocq's.
   - [signedness] is both [Flambda_primitive.signed_or_unsigned] and
     [Scalar.Signedness.t], which have the same constructors.
   - The constructors of [equality_comparison] are prefixed with
     [Phys_], for the same reason: the compiler's are [Eq] and [Neq].
   - [String_length] has no [string_or_bytes]: it is the length of a
     string ([String]). The model has no bytes, which are mutable, and
     the conversion must refuse [Bytes].
   - [Num_conv] is between two [Standard_int.t], where the compiler's is
     between two [Standard_int_or_float.t], a record of [src] and
     [dst]: the conversions to and from the two kinds of float are not
     here, and the conversion must refuse them.
   - The unary [Int_arith] of the compiler is not here; when it is, it
     will need another name, as this [Int_arith] is the binary one.

   To add a primitive: add its constructor here, its case to the
   evaluation, to the kinds and to [prim_in_range] of
   FlambdaPrimitiveSpec.v, and its case to the proofs of the laws of
   that file, in FlambdaPrimitiveProofs.v. Nothing else in the model
   looks inside a primitive. *)

From Stdlib Require Import ZArith.
From OxCamlFlambda2 Require Import FlambdaKindModel.

(* [Flambda_primitive.signed_or_unsigned]. *)
Inductive signedness : Type :=
  | Signed
  | Unsigned.

(* [Flambda_primitive.Block_access_field_kind.t]. *)
Inductive block_access_field_kind : Type :=
  | Any_value
  | Immediate.

(* [Flambda_primitive.Block_access_kind.t]. *)
Inductive block_access_kind : Type :=
  | Block_access_values (tag : option Z) (size : option Z)
      (field_kind : block_access_field_kind).

(* [Flambda_primitive.unary_primitive]. *)
Inductive unary_primitive : Type :=
  | Block_load (kind : block_access_kind) (field : Z)
  | Is_int (variant_only : bool)
  | Is_null
  | Get_tag
  | String_length
  | Opaque_identity (kind : flambda_kind)
  | Num_conv (src dst : standard_int)
  | Boolean_not
  | Unbox_number (kind : boxable_number)
  | Box_number (kind : boxable_number)
  | Untag_immediate
  | Tag_immediate.

(* [Flambda_primitive.binary_int_arith_op]. *)
Inductive binary_int_arith_op : Type :=
  | Add
  | Sub
  | Mul
  | Div (s : signedness)
  | Mod (s : signedness)
  | And
  | Or
  | Xor.

(* [Flambda_primitive.int_shift_op]. *)
Inductive int_shift_op : Type :=
  | Lsl
  | Lsr
  | Asr.

(* [Flambda_primitive.comparison], of integers. *)
Inductive int_comparison : Type :=
  | Int_eq
  | Int_neq
  | Int_lt (s : signedness)
  | Int_gt (s : signedness)
  | Int_le (s : signedness)
  | Int_ge (s : signedness).

(* [Flambda_primitive.comparison_behaviour], of integers. *)
Inductive int_comparison_behaviour : Type :=
  | Yielding_bool (c : int_comparison)
  | Yielding_int_like_compare_functions (s : signedness).

(* [Flambda_primitive.equality_comparison]. *)
Inductive equality_comparison : Type :=
  | Phys_eq
  | Phys_neq.

(* [Flambda_primitive.binary_primitive]. *)
Inductive binary_primitive : Type :=
  | Phys_equal (op : equality_comparison)
  | Int_arith (kind : standard_int) (op : binary_int_arith_op)
  | Int_shift (kind : standard_int) (op : int_shift_op)
  | Int_comp (kind : standard_int) (behaviour : int_comparison_behaviour).

(* [Flambda_primitive.Block_kind.t]. *)
Inductive block_kind : Type :=
  | Block_kind_values (tag : Z).

(* [Flambda_primitive.variadic_primitive]. *)
Inductive variadic_primitive : Type :=
  | Make_block (kind : block_kind).

(* [Flambda_primitive.Without_args.t]: a primitive without its
   arguments. *)
Inductive prim : Type :=
  | Unary (p : unary_primitive)
  | Binary (p : binary_primitive)
  | Variadic (p : variadic_primitive).
