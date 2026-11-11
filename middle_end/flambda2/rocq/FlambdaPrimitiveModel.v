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
   - of [unary_primitive]: [Is_int], [Is_null], [Get_tag],
     [Opaque_identity], [Untag_immediate] and [Tag_immediate];
   - of [binary_primitive]: [Int_arith] and [Int_comp], at every
     [Standard_int.t].
   Every other primitive is left out. The conversion from the compiler's
   terms must refuse a primitive that is not here, and a primitive whose
   fields have a value that is not here; it must never approximate one.

   Differences from the compiler:
   - [Opaque_identity] has no [middle_end_only], which has no effect on
     execution.
   - The comparisons are those of integers only: the compiler's
     [comparison] and [comparison_behaviour] are polymorphic in the
     signedness so as to serve the floats too, which are not here. Their
     constructors are prefixed with [Int_], as [Eq], [Lt] and [Gt] are
     Rocq's.
   - [signedness] is both [Flambda_primitive.signed_or_unsigned] and
     [Scalar.Signedness.t], which have the same constructors.
   - The unary [Int_arith] of the compiler is not here; when it is, it
     will need another name, as this [Int_arith] is the binary one.

   To add a primitive: add its constructor here, its case to the
   evaluation and to the kinds of FlambdaPrimitiveSpec.v, and its case to
   the proofs of the laws of that file, in FlambdaPrimitiveProofs.v.
   Nothing else in the model looks inside a primitive. *)

From Stdlib Require Import ZArith.
From OxCamlFlambda2 Require Import FlambdaKindModel.

(* [Flambda_primitive.signed_or_unsigned]. *)
Inductive signedness : Type :=
  | Signed
  | Unsigned.

(* [Flambda_primitive.unary_primitive]. *)
Inductive unary_primitive : Type :=
  | Is_int (variant_only : bool)
  | Is_null
  | Get_tag
  | Opaque_identity (kind : flambda_kind)
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

(* [Flambda_primitive.binary_primitive]. *)
Inductive binary_primitive : Type :=
  | Int_arith (kind : standard_int) (op : binary_int_arith_op)
  | Int_comp (kind : standard_int) (behaviour : int_comparison_behaviour).

(* [Flambda_primitive.Without_args.t]: a primitive without its
   arguments. *)
Inductive prim : Type :=
  | Unary (p : unary_primitive)
  | Binary (p : binary_primitive).
