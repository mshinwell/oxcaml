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

(* Soundness of the covered answers of Simplify's table for the
   arithmetic of integers with one argument unknown, FOR EACH OF THE SEVEN
   KINDS OF INTEGER: the seven tables that the port has, against the
   model's semantics of the operation.

   This file is to be reviewed: the two general statements, the fourteen
   statements, and the one that joins this file to
   FlambdaPortIntArithTableSpec.v. The proofs are in
   FlambdaPortIntArithTableKindsProofs.v. Read README.md of this folder
   and FlambdaPortIntArithTableSpec.v first: this file uses the map of
   the operation, the form of the contracts and [answer_is_sound] of that
   file as they are, and exports that file. This file follows no file of
   the compiler.

   THE PORT'S SIDE. The table is in a functor of
   Simplify_binary_primitive.v, [Int_ops_for_binary_arith], over a module
   [I : Number_adjuncts.Int_number_kind] of numbers. The port applies it
   seven times, as the compiler does (simplify_binary_primitive.ml, after
   that functor). Each application is a module of the port with its own
   [op_lhs_unknown] and [op_rhs_unknown]. The seven modules of numbers
   are of [Number_adjuncts], and decl/ declares each: its type of numbers
   and its functions are parameters.

   THE MODEL'S SIDE. [int_arith_identities_statement] of
   simplify/FlambdaSimplifyArithSpec.v is for EVERY kind of integer of the
   model ([standard_int]): at the width of each kind, what the model's
   [eval_int_arith] is at each place of the table that answers
   [Exactly], [The_other_side] or [Invalid]. The model proves it. The
   model's statements about TERMS (the same file) are for the tagged
   immediates only; FlambdaPortIntArithTableSpec.v is the statement that
   fits them. For the other six kinds this file has no statement of the
   model about terms above it.

   WHAT IS STATED. For each of the seven modules and each of its two
   functions: SOUNDNESS OF THE COVERED ANSWERS, as
   FlambdaPortIntArithTableSpec.v states it for the tagged immediates,
   for the model's operation AT THE WIDTH OF ANY KIND of the model. The
   same three things are the reader's to choose (the machine width, a
   reading of a number as an integer, the numbers that fit), and the same
   four contracts are premises, on the four functions of the module's own
   numbers ([Num.zero], [Num.one], [Num.minus_one], [Num.equal] of the
   module of [Number_adjuncts] that the table is applied at). EACH IS A
   CLAIM ABOUT THE COMPILER THAT IS NOT PROVED: twenty-eight claims of one
   shape, four for each of the seven declared modules.

   WHICH KIND GOES WITH WHICH MODULE IS A READING. The model's identities
   hold for every kind of the model. So each ported table is sound for
   the model's operation at the width of EVERY kind, and each statement
   here is for every kind. Which kind the compiler means for a module,
   the port cannot say: decl/ declares the module's [standard_int_kind]
   as a parameter. So a statement here does not say that a table is used
   at its own kind; it says that its covered answers are sound at
   whichever kind it is used.

   THE PAIRING THAT THE COMPILER MAKES, module by module. In the compiler
   each module of numbers gives its kind ([standard_int_kind], in
   number_adjuncts.ml). Below: the port's module, the module of numbers
   that the functor is applied at, the model's kind that has the name of
   the compiler's, and the width that the model gives it ([int_width]).

     Int_ops_for_binary_arith_tagged_immediate  at  For_tagged_immediates
       [Standard_tagged_immediate], 63 bits ON THE 64-BIT TARGET
     Int_ops_for_binary_arith_naked_immediate   at  For_naked_immediates
       [Standard_naked_immediate], 63 bits ON THE 64-BIT TARGET
     Int_ops_for_binary_arith_int8              at  For_int8s
       [Standard_naked_int8], 8 bits
     Int_ops_for_binary_arith_int16             at  For_int16s
       [Standard_naked_int16], 16 bits
     Int_ops_for_binary_arith_int32             at  For_int32s
       [Standard_naked_int32], 32 bits
     Int_ops_for_binary_arith_int64             at  For_int64s
       [Standard_naked_int64], 64 bits
     Int_ops_for_binary_arith_nativeint         at  For_nativeints
       [Standard_naked_nativeint], 64 bits ON THE 64-BIT TARGET

   ON THE 64-BIT TARGET: THE MODEL IS OF THAT TARGET ONLY. In the
   compiler the width of the two kinds of immediates and of the native
   integers is that of the target: it is less on a 32-bit target. The
   model has 63 and 64 bits for them, and no other width. At those three
   kinds a statement here is about the model's operation at the model's
   width. It is not the model's word on a 32-bit target. The widths of
   the other four kinds are the same on every target.

   THIS FILE AND FlambdaPortIntArithTableSpec.v. The two statements of
   that file follow from the first two of the fourteen, at the kind
   [Standard_tagged_immediate]: [tagged_statements_agree_statement], the
   last statement of this file. That file stays as it is: it writes the
   width as the model's [tagged_width], as the model's statements about
   terms do.

   WHAT IS NOT SAID: what the head of FlambdaPortIntArithTableSpec.v
   lists, for each of the seven. Not completeness; nothing of a run that
   is out of fuel; nothing of the width of the compiler's numbers (the
   model is of the 64-bit target only); nothing new about division by
   zero; nothing of the extracted OCaml. And nothing of the tables of the
   shifts, of the comparisons and of the floats, which are other functors
   of the same file. *)

From Stdlib Require Import ZArith Bool.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaPrimitiveModel
  FlambdaPrimitiveSpec.
From OxCamlFlambda2Types Require Import FlambdaSimplifyArithSpec.
From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort Require Simplify_binary_primitive.
From SimplifyPort.decl Require Flambda_primitive Number_adjuncts
  Target_system.
From SimplifyPortAgainstModel Require Export FlambdaPortIntArithTableSpec.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The statement, of any numbers and any table                              *)
(* ======================================================================== *)

(* Of any type of numbers with its three constants and its test of
   equality, any function of the type of [op_lhs_unknown] or
   [op_rhs_unknown] over those numbers, and a width of the model. The
   three things that the reader chooses, the four contracts and the
   conclusion are those of [op_lhs_unknown_statement] and
   [op_rhs_unknown_statement] of FlambdaPortIntArithTableSpec.v. *)
Section Any_table.

  Variable num : Type.
  Variable width : Z.
  Variable zero one minus_one : Target_system.Machine_width.t -> M num.
  Variable equal : num -> num -> M bool.
  Variable table :
    Target_system.Machine_width.t -> P.binary_int_arith_op -> num ->
    M (answer num).

  (* The known number is the right argument. *)
  Definition lhs_unknown_table_sound : Prop :=
    forall (machine_width : Target_system.Machine_width.t)
      (value : num -> Z) (compatible : num -> Prop),
      constant_reads_as value compatible (zero machine_width) 0 ->
      constant_reads_as value compatible (one machine_width) 1 ->
      constant_reads_as value compatible (minus_one machine_width) (-1) ->
      tests_equality value compatible equal ->
      forall (op : P.binary_int_arith_op) (rhs : num),
        compatible rhs ->
        pure_if_returns (table machine_width op rhs)
          (fun a =>
             answer_is_sound width value a
               (fun j =>
                  eval_int_arith width (int_arith_op_of_port op) j
                    (value rhs))).

  (* The known number is the left argument. *)
  Definition rhs_unknown_table_sound : Prop :=
    forall (machine_width : Target_system.Machine_width.t)
      (value : num -> Z) (compatible : num -> Prop),
      constant_reads_as value compatible (zero machine_width) 0 ->
      constant_reads_as value compatible (one machine_width) 1 ->
      constant_reads_as value compatible (minus_one machine_width) (-1) ->
      tests_equality value compatible equal ->
      forall (op : P.binary_int_arith_op) (lhs : num),
        compatible lhs ->
        pure_if_returns (table machine_width op lhs)
          (fun a =>
             answer_is_sound width value a
               (fun j =>
                  eval_int_arith width (int_arith_op_of_port op)
                    (value lhs) j)).

End Any_table.

(* ======================================================================== *)
(* The seven modules of the port                                            *)
(* ======================================================================== *)

(* The port's seven tables, each under a short name. [Tagged] of
   FlambdaPortIntArithTableSpec.v is the first. *)
Module Ops_tagged := Tagged.
Module Ops_naked :=
  SimplifyPort.Simplify_binary_primitive
    .Int_ops_for_binary_arith_naked_immediate.
Module Ops_int8 :=
  SimplifyPort.Simplify_binary_primitive
    .Int_ops_for_binary_arith_int8.
Module Ops_int16 :=
  SimplifyPort.Simplify_binary_primitive
    .Int_ops_for_binary_arith_int16.
Module Ops_int32 :=
  SimplifyPort.Simplify_binary_primitive
    .Int_ops_for_binary_arith_int32.
Module Ops_int64 :=
  SimplifyPort.Simplify_binary_primitive
    .Int_ops_for_binary_arith_int64.
Module Ops_nativeint :=
  SimplifyPort.Simplify_binary_primitive
    .Int_ops_for_binary_arith_nativeint.

(* THE FOURTEEN STATEMENTS. Each is one of the two general statements for
   one module of the port: its numbers are those of the module of
   [Number_adjuncts] that the comment names, and the four contracts are
   on the [Num.zero], [Num.one], [Num.minus_one] and [Num.equal] of that
   module. The comment names the kind that the compiler pairs with the
   module (the head of this file); the statement is for every kind. *)

(* [Int_ops_for_binary_arith_tagged_immediate]: the numbers of
   [Number_adjuncts.For_tagged_immediates].
   The compiler's kind for it: [Standard_tagged_immediate], 63 bits in the model
   (the 64-bit target only). *)
Definition tagged_op_lhs_unknown_statement : Prop :=
  forall kind : standard_int,
    lhs_unknown_table_sound Ops_tagged.Num.t (int_width kind)
      Ops_tagged.Num.zero Ops_tagged.Num.one Ops_tagged.Num.minus_one
      Ops_tagged.Num.equal Ops_tagged.op_lhs_unknown.

Definition tagged_op_rhs_unknown_statement : Prop :=
  forall kind : standard_int,
    rhs_unknown_table_sound Ops_tagged.Num.t (int_width kind)
      Ops_tagged.Num.zero Ops_tagged.Num.one Ops_tagged.Num.minus_one
      Ops_tagged.Num.equal Ops_tagged.op_rhs_unknown.

(* [Int_ops_for_binary_arith_naked_immediate]: the numbers of
   [Number_adjuncts.For_naked_immediates].
   The compiler's kind for it: [Standard_naked_immediate], 63 bits in the model
   (the 64-bit target only). *)
Definition naked_op_lhs_unknown_statement : Prop :=
  forall kind : standard_int,
    lhs_unknown_table_sound Ops_naked.Num.t (int_width kind)
      Ops_naked.Num.zero Ops_naked.Num.one Ops_naked.Num.minus_one
      Ops_naked.Num.equal Ops_naked.op_lhs_unknown.

Definition naked_op_rhs_unknown_statement : Prop :=
  forall kind : standard_int,
    rhs_unknown_table_sound Ops_naked.Num.t (int_width kind)
      Ops_naked.Num.zero Ops_naked.Num.one Ops_naked.Num.minus_one
      Ops_naked.Num.equal Ops_naked.op_rhs_unknown.

(* [Int_ops_for_binary_arith_int8]: the numbers of
   [Number_adjuncts.For_int8s].
   The compiler's kind for it: [Standard_naked_int8], 8 bits. *)
Definition int8_op_lhs_unknown_statement : Prop :=
  forall kind : standard_int,
    lhs_unknown_table_sound Ops_int8.Num.t (int_width kind)
      Ops_int8.Num.zero Ops_int8.Num.one Ops_int8.Num.minus_one
      Ops_int8.Num.equal Ops_int8.op_lhs_unknown.

Definition int8_op_rhs_unknown_statement : Prop :=
  forall kind : standard_int,
    rhs_unknown_table_sound Ops_int8.Num.t (int_width kind)
      Ops_int8.Num.zero Ops_int8.Num.one Ops_int8.Num.minus_one
      Ops_int8.Num.equal Ops_int8.op_rhs_unknown.

(* [Int_ops_for_binary_arith_int16]: the numbers of
   [Number_adjuncts.For_int16s].
   The compiler's kind for it: [Standard_naked_int16], 16 bits. *)
Definition int16_op_lhs_unknown_statement : Prop :=
  forall kind : standard_int,
    lhs_unknown_table_sound Ops_int16.Num.t (int_width kind)
      Ops_int16.Num.zero Ops_int16.Num.one Ops_int16.Num.minus_one
      Ops_int16.Num.equal Ops_int16.op_lhs_unknown.

Definition int16_op_rhs_unknown_statement : Prop :=
  forall kind : standard_int,
    rhs_unknown_table_sound Ops_int16.Num.t (int_width kind)
      Ops_int16.Num.zero Ops_int16.Num.one Ops_int16.Num.minus_one
      Ops_int16.Num.equal Ops_int16.op_rhs_unknown.

(* [Int_ops_for_binary_arith_int32]: the numbers of
   [Number_adjuncts.For_int32s].
   The compiler's kind for it: [Standard_naked_int32], 32 bits. *)
Definition int32_op_lhs_unknown_statement : Prop :=
  forall kind : standard_int,
    lhs_unknown_table_sound Ops_int32.Num.t (int_width kind)
      Ops_int32.Num.zero Ops_int32.Num.one Ops_int32.Num.minus_one
      Ops_int32.Num.equal Ops_int32.op_lhs_unknown.

Definition int32_op_rhs_unknown_statement : Prop :=
  forall kind : standard_int,
    rhs_unknown_table_sound Ops_int32.Num.t (int_width kind)
      Ops_int32.Num.zero Ops_int32.Num.one Ops_int32.Num.minus_one
      Ops_int32.Num.equal Ops_int32.op_rhs_unknown.

(* [Int_ops_for_binary_arith_int64]: the numbers of
   [Number_adjuncts.For_int64s].
   The compiler's kind for it: [Standard_naked_int64], 64 bits. *)
Definition int64_op_lhs_unknown_statement : Prop :=
  forall kind : standard_int,
    lhs_unknown_table_sound Ops_int64.Num.t (int_width kind)
      Ops_int64.Num.zero Ops_int64.Num.one Ops_int64.Num.minus_one
      Ops_int64.Num.equal Ops_int64.op_lhs_unknown.

Definition int64_op_rhs_unknown_statement : Prop :=
  forall kind : standard_int,
    rhs_unknown_table_sound Ops_int64.Num.t (int_width kind)
      Ops_int64.Num.zero Ops_int64.Num.one Ops_int64.Num.minus_one
      Ops_int64.Num.equal Ops_int64.op_rhs_unknown.

(* [Int_ops_for_binary_arith_nativeint]: the numbers of
   [Number_adjuncts.For_nativeints].
   The compiler's kind for it: [Standard_naked_nativeint], 64 bits in the model
   (the 64-bit target only). *)
Definition nativeint_op_lhs_unknown_statement : Prop :=
  forall kind : standard_int,
    lhs_unknown_table_sound Ops_nativeint.Num.t (int_width kind)
      Ops_nativeint.Num.zero Ops_nativeint.Num.one Ops_nativeint.Num.minus_one
      Ops_nativeint.Num.equal Ops_nativeint.op_lhs_unknown.

Definition nativeint_op_rhs_unknown_statement : Prop :=
  forall kind : standard_int,
    rhs_unknown_table_sound Ops_nativeint.Num.t (int_width kind)
      Ops_nativeint.Num.zero Ops_nativeint.Num.one Ops_nativeint.Num.minus_one
      Ops_nativeint.Num.equal Ops_nativeint.op_rhs_unknown.

(* ======================================================================== *)
(* This file and FlambdaPortIntArithTableSpec.v                             *)
(* ======================================================================== *)

(* The two statements of FlambdaPortIntArithTableSpec.v follow from the
   two of the tagged immediates here: the model's [tagged_width] is the
   width of the kind [Standard_tagged_immediate]. *)
Definition tagged_statements_agree_statement : Prop :=
  (tagged_op_lhs_unknown_statement -> op_lhs_unknown_statement)
  /\ (tagged_op_rhs_unknown_statement -> op_rhs_unknown_statement).
