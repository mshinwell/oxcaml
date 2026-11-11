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

(* What the primitives of FlambdaPrimitiveModel.v compute, their kinds,
   and the laws that every primitive obeys.

   This file is to be reviewed: [eval_prim] and what it is made of, against
   middle_end/flambda2/terms/flambda_primitive.mli for what each primitive
   is, and against middle_end/flambda2/simplify/simplify_unary_primitive.ml,
   simplify_binary_primitive.ml and number_adjuncts.ml for what Simplify
   takes each to compute; the kinds, against [arg_kind_of_unary_primitive],
   [args_kind_of_binary_primitive] and the [result_kind_of_] functions of
   flambda_primitive.ml; and the statements at the end.

   [eval_prim statics p vs] is the value of the primitive [p] applied to
   the values [vs], if it has one. Where it has none the term is
   undefined (FlambdaSemanticsSpec.v), and a transformation may do
   anything to it. A primitive has no value
   - when it is not given as many arguments as it takes;
   - when an argument is not of the kind it takes: this is what Simplify
     assumes, which replaces a primitive applied to an argument of the
     wrong kind by [Invalid] ([Simplify_primitive.arg_kind_mismatch]);
   - when an argument is not what the primitive is for, even if of the
     right kind: the cases are listed at each primitive below. Most are
     there because Simplify assumes that the case does not arise, where
     the machine would compute something;
   - when it computes with an integer that is out of the range of its
     kind.

   The integers. The model is of a 64-bit target: the tagged and the
   naked immediates are OCaml's [int], of 63 bits, and the other kinds
   have 8, 16, 32 and 64 bits ([int_width]). A constant holds any integer
   (FlambdaModel.v); the arithmetic, the comparisons, tagging and
   untagging take only integers in the range of their kind
   ([int_of_value]), and their results are in range. Arithmetic is on
   mathematical integers and wraps ([wrap]), which is two's complement.
   FlambdaPrimitiveProofs.v shows that the results of arithmetic are in
   range, that at 64 bits [wrap], [unsigned] and [in_range] are the
   [wrap64], [unsigned64] and [fits_int64] of rocq/OxCamlInt64.v, and
   that at 63 bits addition, subtraction and multiplication are those of
   OCaml's [int] as rocq/OxCamlInt.v models it.

   Allocated values are read through the observations of
   FlambdaValueSpec.v ([block_of], ...), which look through a symbol to
   what it is bound to. So the value of a primitive may depend on the
   static environment, but only on what the symbols among its arguments
   are bound to ([eval_prim_static_values_statement]).

   The laws. The rest of the model does not look inside a primitive: it
   uses the statements at the end, which hold of every primitive.
   [eval_prim] is opaque after FlambdaPrimitiveProofs.v, as [step] is, so
   that no proof elsewhere comes to depend on which primitives there are.
   A proof about one primitive rewrites with the equation of its arity
   there ([eval_prim_unary], [eval_prim_binary]).

   The proofs are in FlambdaPrimitiveProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaValueSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* Integers of a width                                                      *)
(* ======================================================================== *)

(* The integers of [width] bits: the signed reading of a machine register
   of that width. *)
Definition in_range (width z : Z) : bool :=
  (- 2 ^ (width - 1) <=? z) && (z <? 2 ^ (width - 1)).

(* Two's-complement wrap-around: the integer of [width] bits that differs
   from [z] by a multiple of [2 ^ width]. *)
Definition wrap (width z : Z) : Z :=
  (z + 2 ^ (width - 1)) mod 2 ^ width - 2 ^ (width - 1).

(* The unsigned reading of an integer of [width] bits. *)
Definition unsigned (width z : Z) : Z :=
  if z <? 0 then z + 2 ^ width else z.

Definition reading (width : Z) (s : signedness) (z : Z) : Z :=
  match s with
  | Signed => z
  | Unsigned => unsigned width z
  end.

(* The number of bits of the integers of a kind, on a 64-bit target. *)
Definition int_width (kind : standard_int) : Z :=
  match kind with
  | Standard_tagged_immediate | Standard_naked_immediate => 63
  | Standard_naked_int8 => 8
  | Standard_naked_int16 => 16
  | Standard_naked_int32 => 32
  | Standard_naked_int64 | Standard_naked_nativeint => 64
  end.

(* The constant that is an integer of a kind. *)
Definition const_of_int (kind : standard_int) (i : Z) : const :=
  match kind with
  | Standard_tagged_immediate => Tagged_immediate i
  | Standard_naked_immediate => Naked_immediate i
  | Standard_naked_int8 => Naked_int8 i
  | Standard_naked_int16 => Naked_int16 i
  | Standard_naked_int32 => Naked_int32 i
  | Standard_naked_int64 => Naked_int64 i
  | Standard_naked_nativeint => Naked_nativeint i
  end.

(* The integer that a value is, if it is a constant of the kind and in
   its range. *)
Definition int_of_value (kind : standard_int) (v : value) : option Z :=
  match kind, v with
  | Standard_tagged_immediate, Value_const (Tagged_immediate i)
  | Standard_naked_immediate, Value_const (Naked_immediate i)
  | Standard_naked_int8, Value_const (Naked_int8 i)
  | Standard_naked_int16, Value_const (Naked_int16 i)
  | Standard_naked_int32, Value_const (Naked_int32 i)
  | Standard_naked_int64, Value_const (Naked_int64 i)
  | Standard_naked_nativeint, Value_const (Naked_nativeint i) =>
    if in_range (int_width kind) i then Some i else None
  | _, _ => None
  end.

(* ======================================================================== *)
(* Integer arithmetic and comparison                                        *)
(* ======================================================================== *)

(* [Int_arith]. Addition, subtraction and multiplication wrap. Division
   truncates towards zero and [Mod] is its remainder, with the sign of
   the dividend; the unsigned ones are those of the unsigned readings.
   Neither has a value on a zero divisor: the compiler tests for zero
   before a division, and Simplify takes one by zero to be unreachable
   ([Simplify_binary_primitive], [op_lhs_unknown]). The least integer
   divided by minus one wraps to itself. The bitwise operations are those
   of two's complement. *)
Definition eval_int_arith (width : Z) (op : binary_int_arith_op) (a b : Z)
    : option Z :=
  match op with
  | Add => Some (wrap width (a + b))
  | Sub => Some (wrap width (a - b))
  | Mul => Some (wrap width (a * b))
  | Div s =>
    if b =? 0 then None
    else Some (wrap width (Z.quot (reading width s a) (reading width s b)))
  | Mod s =>
    if b =? 0 then None
    else Some (wrap width (Z.rem (reading width s a) (reading width s b)))
  | And => Some (wrap width (Z.land a b))
  | Or => Some (wrap width (Z.lor a b))
  | Xor => Some (wrap width (Z.lxor a b))
  end.

Definition eval_int_comparison (width : Z) (c : int_comparison) (a b : Z)
    : bool :=
  match c with
  | Int_eq => a =? b
  | Int_neq => negb (a =? b)
  | Int_lt s => reading width s a <? reading width s b
  | Int_gt s => reading width s b <? reading width s a
  | Int_le s => reading width s a <=? reading width s b
  | Int_ge s => reading width s b <=? reading width s a
  end.

(* [Int_comp]: 1 or 0 for a comparison yielding a boolean; -1, 0 or 1 for
   one that behaves as the [compare] functions do. *)
Definition eval_int_comp (width : Z) (behaviour : int_comparison_behaviour)
    (a b : Z) : Z :=
  match behaviour with
  | Yielding_bool c => if eval_int_comparison width c a b then 1 else 0
  | Yielding_int_like_compare_functions s =>
    match reading width s a ?= reading width s b with
    | Lt => -1
    | Eq => 0
    | Gt => 1
    end
  end.

(* ======================================================================== *)
(* The primitives                                                           *)
(* ======================================================================== *)

(* A boolean result is a naked immediate, 1 or 0. *)
Definition naked_bool (b : bool) : value :=
  Value_const (Naked_immediate (if b then 1 else 0)).

Definition is_tagged_immediate (v : value) : bool :=
  is_some (int_of_value Standard_tagged_immediate v).

(* [Is_int]. With [variant_only], the argument is taken to be a variant:
   a tagged immediate or a block, and the primitive has no value on
   anything else. That is what Simplify assumes: it takes the argument
   to be a variant that is not null
   ([Flambda2_types.add_is_int_relation]), and
   [Provers.prove_is_int_generic_value] answers [Invalid] on closures,
   boxed numbers and strings. The machine computes the low bit of
   anything. Without [variant_only], the primitive also answers no on
   every other allocated value. It has no value on null, on poison, or
   on a symbol bound to nothing; on a poison constant Simplify folds it
   to 1. *)
Definition eval_is_int (statics : static_env) (variant_only : bool)
    (v : value) : option bool :=
  if is_tagged_immediate v then Some true
  else if
    if variant_only then is_some (block_of statics v)
    else is_allocated statics v
  then Some false
  else None.

(* [Is_null]. It has no value on poison or on a symbol bound to
   nothing; on a poison constant Simplify folds it to 0. *)
Definition eval_is_null (statics : static_env) (v : value) : option bool :=
  match v with
  | Value_const Null => Some true
  | _ =>
    if is_tagged_immediate v || is_allocated statics v then Some false
    else None
  end.

(* A unary primitive applied to a value.
   - [Get_tag] is the tag of a block, and has no value on anything else,
     a closure, a boxed number and a string included: Simplify takes its
     argument to be a variant that is not null
     ([Flambda2_types.add_get_tag_relation]).
   - [Opaque_identity] is the identity, on a value of the kind it
     carries.
   - [Untag_immediate] and [Tag_immediate] change a tagged immediate into
     the naked immediate that is the same integer, and back. *)
Definition eval_unary_primitive (statics : static_env) (p : unary_primitive)
    (v : value) : option value :=
  match p with
  | Is_int variant_only =>
    option_map naked_bool (eval_is_int statics variant_only v)
  | Is_null => option_map naked_bool (eval_is_null statics v)
  | Get_tag =>
    let* '(tag, _) := block_of statics v in
    Some (Value_const (Naked_immediate tag))
  | Opaque_identity kind =>
    if kind_eqb (kind_of_value v) kind then Some v else None
  | Untag_immediate =>
    let* i := int_of_value Standard_tagged_immediate v in
    Some (Value_const (Naked_immediate i))
  | Tag_immediate =>
    let* i := int_of_value Standard_naked_immediate v in
    Some (Value_const (Tagged_immediate i))
  end.

(* A binary primitive applied to two values: both integers of the kind
   the primitive carries. The result of a comparison is a naked
   immediate. *)
Definition eval_binary_primitive (p : binary_primitive) (v1 v2 : value)
    : option value :=
  match p with
  | Int_arith kind op =>
    let* a := int_of_value kind v1 in
    let* b := int_of_value kind v2 in
    let* result := eval_int_arith (int_width kind) op a b in
    Some (Value_const (const_of_int kind result))
  | Int_comp kind behaviour =>
    let* a := int_of_value kind v1 in
    let* b := int_of_value kind v2 in
    Some
      (Value_const
         (Naked_immediate (eval_int_comp (int_width kind) behaviour a b)))
  end.

(* The value of a primitive applied to the values of its arguments, if it
   has one. *)
Definition eval_prim (statics : static_env) (p : prim) (vs : list value)
    : option value :=
  match p, vs with
  | Unary p, [v] => eval_unary_primitive statics p v
  | Binary p, [v1; v2] => eval_binary_primitive p v1 v2
  | _, _ => None
  end.

(* ======================================================================== *)
(* Kinds                                                                    *)
(* ======================================================================== *)

Definition naked_immediate_kind : flambda_kind :=
  Naked_number Kind_naked_immediate.

(* [Flambda_primitive.arg_kind_of_unary_primitive]. *)
Definition arg_kind_of_unary_primitive (p : unary_primitive) : flambda_kind :=
  match p with
  | Is_int _ | Is_null | Get_tag | Untag_immediate => Value
  | Opaque_identity kind => kind
  | Tag_immediate => naked_immediate_kind
  end.

(* [Flambda_primitive.result_kind_of_unary_primitive']. *)
Definition result_kind_of_unary_primitive (p : unary_primitive)
    : flambda_kind :=
  match p with
  | Is_int _ | Is_null | Get_tag | Untag_immediate => naked_immediate_kind
  | Opaque_identity kind => kind
  | Tag_immediate => Value
  end.

(* [Flambda_primitive.args_kind_of_binary_primitive]. *)
Definition args_kind_of_binary_primitive (p : binary_primitive)
    : flambda_kind * flambda_kind :=
  match p with
  | Int_arith kind _ | Int_comp kind _ =>
    (kind_of_standard_int kind, kind_of_standard_int kind)
  end.

(* [Flambda_primitive.result_kind_of_binary_primitive']. *)
Definition result_kind_of_binary_primitive (p : binary_primitive)
    : flambda_kind :=
  match p with
  | Int_arith kind _ => kind_of_standard_int kind
  | Int_comp _ _ => naked_immediate_kind
  end.

(* [Flambda_primitive.result_kind']: the kind of the variable that a
   [Let] binds to the primitive. *)
Definition prim_result_kind (p : prim) : flambda_kind :=
  match p with
  | Unary p => result_kind_of_unary_primitive p
  | Binary p => result_kind_of_binary_primitive p
  end.

(* Whether arguments of these kinds are as many as the primitive takes,
   and of the kinds it takes. *)
Definition prim_args_well_kinded (p : prim) (kinds : list flambda_kind)
    : bool :=
  match p, kinds with
  | Unary p, [kind] => kind_eqb kind (arg_kind_of_unary_primitive p)
  | Binary p, [kind1; kind2] =>
    kind_eqb kind1 (fst (args_kind_of_binary_primitive p))
    && kind_eqb kind2 (snd (args_kind_of_binary_primitive p))
  | _, _ => false
  end.

(* ======================================================================== *)
(* Equality, and which primitives to fold                                   *)
(* ======================================================================== *)

Definition prim_eq_dec : ∀ p p' : prim, {p = p'} + {p <> p'}.
Proof. repeat decide equality. Defined.

(* [Flambda_primitive.Without_args.equal]. *)
Definition prim_eqb (p p' : prim) : bool :=
  if prim_eq_dec p p' then true else false.

(* ======================================================================== *)
(* The laws of every primitive                                              *)
(* ======================================================================== *)

(* The value of a primitive depends on the static environment only
   through what the symbols among its arguments are bound to. In
   particular it does not depend on the code, and on constants it does
   not depend on the static environment at all. *)
Definition eval_prim_static_values_statement : Prop :=
  ∀ (statics statics' : static_env) (p : prim) (vs : list value),
    (∀ s : symbol,
      Value_symbol s ∈ vs ->
      lookup s (static_values statics) = lookup s (static_values statics')) ->
    eval_prim statics p vs = eval_prim statics' p vs.

(* A primitive that has a value keeps it when the static environment
   grows: when each symbol among its arguments that is bound stays bound
   to the same thing, whatever else comes to be bound. The statement
   above does not give this, as it asks of a symbol that is not bound
   that it stay so. It holds because no primitive has a value by a
   symbol's being bound to nothing. The premise is that of
   [FlambdaWellFormedSpec.statics_extend], which a run of the machine
   keeps, asked of the symbols among the arguments only. *)
Definition eval_prim_statics_extend_statement : Prop :=
  ∀ (statics statics' : static_env) (p : prim) (vs : list value)
    (v : value),
    (∀ (s : symbol) (allocated : statically_allocated_value),
      Value_symbol s ∈ vs ->
      lookup s (static_values statics) = Some allocated ->
      lookup s (static_values statics') = Some allocated) ->
    eval_prim statics p vs = Some v ->
    eval_prim statics' p vs = Some v.

(* A primitive that has a value was given arguments of its kinds, as many
   as it takes, and its value is of its result kind. *)
Definition eval_prim_kinds_statement : Prop :=
  ∀ (statics : static_env) (p : prim) (vs : list value) (v : value),
    eval_prim statics p vs = Some v ->
    prim_args_well_kinded p (map kind_of_value vs) = true
    ∧ kind_of_value v = prim_result_kind p.

(* A primitive makes its value out of its arguments: it returns a number,
   one of its arguments, a block of them, or a field of a block that is
   one of them. So a property of values that holds of numbers, that holds
   of a block exactly when it holds of its fields, and that holds of the
   fields of the static block that a symbol with the property is bound
   to, holds of the value of a primitive whose arguments have it. That no
   primitive brings in a symbol or a code id is a case
   (FlambdaUnusedStaticsProofs.eval_prim_avoids). *)
Definition holds_of_numbers (P : value -> Prop) : Prop :=
  ∀ c : const, P (Value_const c) ∧ P (Value_boxed_number c).

Definition holds_of_blocks (P : value -> Prop) : Prop :=
  ∀ (tag : Z) (fields : list value),
    P (Value_block tag fields) <-> (∀ v : value, v ∈ fields -> P v).

Definition holds_in_static_blocks (statics : static_env)
    (P : value -> Prop) : Prop :=
  ∀ (s : symbol) (tag : Z) (fields : list value),
    P (Value_symbol s) ->
    lookup s (static_values statics) = Some (Static_block tag fields) ->
    ∀ v : value, v ∈ fields -> P v.

Definition eval_prim_preserves_statement : Prop :=
  ∀ (P : value -> Prop) (statics : static_env) (p : prim) (vs : list value)
    (v : value),
    holds_of_numbers P ->
    holds_of_blocks P ->
    holds_in_static_blocks statics P ->
    (∀ arg : value, arg ∈ vs -> P arg) ->
    eval_prim statics p vs = Some v ->
    P v.
