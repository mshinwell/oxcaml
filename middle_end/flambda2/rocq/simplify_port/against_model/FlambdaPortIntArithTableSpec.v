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
   arithmetic of integers with one argument unknown: the table as the
   port has it, against the model's semantics of the operation.

   This file is to be reviewed: the two maps, the contracts and the two
   statements. The proofs are in FlambdaPortIntArithTableProofs.v. Read
   README.md of this folder first. This file follows no file of the
   compiler.

   THE MODEL'S SIDE. simplify/FlambdaSimplifyArithSpec.v of the model
   says what Simplify does with [Int_arith] on tagged immediates. It does
   not have Simplify's table for the case where one argument is a known
   number and the other is not. It has
   [int_arith_identities_statement]: of each place of the table that
   answers [Exactly], [The_other_side] or [Invalid], what the model's
   operation ([eval_int_arith], of semantics/FlambdaPrimitiveSpec.v) is
   there. The model proves it ([int_arith_identities], in
   FlambdaSimplifyArithProofs.v). That those facts are the places of the
   table was, until this file, a reading of the model beside the
   compiler.

   THE PORT'S SIDE. Simplify_binary_primitive.v of the port has the
   table itself, as the compiler's simplify_binary_primitive.ml has it:
   the functor [Int_ops_for_binary_arith] with
   [symmetric_op_one_side_unknown], [op_lhs_unknown] and
   [op_rhs_unknown]. This file is about that functor at the tagged
   immediates: the port's module
   [Int_ops_for_binary_arith_tagged_immediate].

   WHAT IS STATED: SOUNDNESS OF THE COVERED ANSWERS. For a machine
   width, an operation and a known right argument that fits that machine
   width, the ported [op_lhs_unknown] never raises, and if it returns an
   answer, the state is as it was and, for every number [j] in the range
   of the model's tagged immediates as the left argument:
   - if the answer is [Exactly r], the model's operation has the result
     that [r] reads as;
   - if it is [The_other_side], the model's operation has the result [j];
   - if it is [Invalid], the model's operation has no result.
   The same for [op_rhs_unknown], with the known argument on the left.

   THE BRIDGE between the compiler's types and the model's (README.md
   has the three ways):
   - A MAP, defined here: the port's [binary_int_arith_op] and
     [Scalar.Signedness.t], which decl/ has as inductive types with the
     compiler's constructors, to the model's types of the same names,
     constructor for constructor. The map reads a value of the port as a
     value of the model; it gives no parameter a definition.
   - CONTRACTS. The numbers of the table are of the type [Num.t] of
     [Number_adjuncts.For_tagged_immediates], which decl/ declares as a
     parameter, as the compiler's interface keeps it abstract. The
     table calls four functions of that module: [Num.zero], [Num.one],
     [Num.minus_one] and [Num.equal]. They are parameters too. What the
     statements assume of them is written here as four named
     propositions, in the form of contracts/README.md of the port, and
     each statement has the four as premises. EACH IS A CLAIM ABOUT THE
     COMPILER THAT IS NOT PROVED. They are stated with three things that
     the reader chooses: the machine width, a reading of a number as an
     integer ([value]), and the numbers that fit that machine width
     ([compatible]). The statements hold for every choice that has the
     four contracts. Nothing says that [Num.t] is [Target_ocaml_int.t],
     or that every number is compatible.

   WHAT IS NOT SAID.
   - NOT COMPLETENESS, and not that two tables are equal. The answers
     [Cannot_simplify], [Negation_of_the_other_side] and
     [Bitwise_not_of_the_other_side] have no obligation: a table that
     answered [Cannot_simplify] everywhere would have both statements.
     A simplification that the table misses is not found; a wrong answer
     among the three covered ones is. The places of the negation and of
     the bitwise complement are not in the model's statement: each
     needs a lemma on the model's side first.
   - NOTHING OF A RUN THAT IS OUT OF FUEL. A function of which every run
     is out of fuel has both statements: no termination is claimed
     (GUIDE.md of the port, section 8). A run that raises is not such a
     run: the statements forbid it.
   - NOT THAT THE COMPILER'S NUMBERS HAVE 63 BITS. The model is of the
     64-bit target only: its tagged immediates have 63 bits
     ([tagged_width]). The statements are about the model's operation at
     that width, for any machine width that the table is given. For a
     machine width other than 64 bits they are true sentences about the
     model's 63-bit operation, and they are not the model's word on the
     compiler's 31-bit immediates.
   - NOTHING NEW ABOUT DIVISION BY ZERO. That [Div] and [Mod] by zero
     have no result is the model's own decision (the comment at
     [eval_int_arith]); it is not a result about traps.
   - Nothing of the compiler's arithmetic on its numbers ([Num.add],
     [Num.mul], ..): the table does not compute, it compares the known
     number with three constants.
   - That the extracted OCaml does what the Rocq text of the port says
     is not proved here (the same section of the guide). *)

From Stdlib Require Import ZArith Bool.
From OxCamlFlambda2 Require Import FlambdaPrimitiveModel
  FlambdaPrimitiveSpec.
From OxCamlFlambda2Types Require Import FlambdaSimplifyArithSpec.
From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort Require Simplify_binary_primitive.
From SimplifyPort.decl Require Flambda_primitive Scalar Target_system.

Local Open Scope Z_scope.

(* The port's side and the model's: each name of a constructor below is
   written with its side. [P] is decl/Flambda_primitive.v of the port;
   [Model] is terms/FlambdaPrimitiveModel.v of the model. The names of the
   ported file Simplify_binary_primitive.v are written whole, from
   [SimplifyPort]: decl/ has a file of that name too. *)
Module P := SimplifyPort.decl.Flambda_primitive.
Module Model := OxCamlFlambda2.FlambdaPrimitiveModel.

(* ======================================================================== *)
(* The port's operation read as the model's                                 *)
(* ======================================================================== *)

(* [Scalar.Signedness.t] of the compiler, as decl/ has it, read as the
   model's [signedness]. *)
Definition signedness_of_port (s : Scalar.Signedness.t) : Model.signedness :=
  match s with
  | Scalar.Signedness.Signed => Model.Signed
  | Scalar.Signedness.Unsigned => Model.Unsigned
  end.

(* [Flambda_primitive.binary_int_arith_op] of the compiler, as decl/ has
   it, read as the model's [binary_int_arith_op]. *)
Definition int_arith_op_of_port (op : P.binary_int_arith_op)
    : Model.binary_int_arith_op :=
  match op with
  | P.Add => Model.Add
  | P.Sub => Model.Sub
  | P.Mul => Model.Mul
  | P.Div s => Model.Div (signedness_of_port s)
  | P.Mod s => Model.Mod (signedness_of_port s)
  | P.And => Model.And
  | P.Or => Model.Or
  | P.Xor => Model.Xor
  end.

(* ======================================================================== *)
(* What a contract and a statement say of a call                            *)
(* ======================================================================== *)

(* The computation never raises; if it returns, [Q] holds of the value and
   the state is as it was. This is for every fuel and every state. A run
   that is out of fuel is allowed: nothing says that the computation
   returns. *)
Definition pure_if_returns {A : Type} (m : M A) (Q : A -> Prop) : Prop :=
  forall (n : nat) (s : ocaml_state),
    wp m (fun a s' => Q a /\ s' = s) no_exn n s.

(* ======================================================================== *)
(* The form of the contracts                                                *)
(* ======================================================================== *)

(* Of any type of numbers, with a reading of a number as an integer and
   a set of numbers, the compatible ones. For the compiler's numbers the
   compatible ones are those that fit the machine width that the table
   is given: the compiler's test of equality ends in a fatal error on two
   numbers that fit different machine widths, and its constants are made
   to fit the machine width that they are given. *)
Section Any_numbers.

  Variable num : Type.
  Variable value : num -> Z.
  Variable compatible : num -> Prop.

  (* Of any computation of a number: it never raises; if it returns, the
     number is compatible and reads as [c], and the state is as it was. *)
  Definition constant_reads_as (constant : M num) (c : Z) : Prop :=
    pure_if_returns constant (fun z => compatible z /\ value z = c).

  (* Of any function of the type of [Num.equal]: on two compatible
     numbers it never raises; if it returns, it says whether the two read
     as the same integer, and the state is as it was. Nothing is said of
     it on another pair. *)
  Definition tests_equality (equal : num -> num -> M bool) : Prop :=
    forall a b : num,
      compatible a -> compatible b ->
      pure_if_returns (equal a b) (fun r => r = (value a =? value b)).

End Any_numbers.

Arguments constant_reads_as {num}.
Arguments tests_equality {num}.

(* THE CONTRACTS HAVE A MODEL. A number of the model is an integer with a
   mark that says whether the number fits; the compatible numbers are
   those that fit; the test of equality ends in a fatal error on two
   numbers with different marks. So the four contracts together are no
   contradiction, and the contract of the test does not ask it to return
   on every pair. A model does not show that a contract is true of the
   compiler. *)
Definition model_equal (a b : bool * Z) : M bool :=
  if Bool.eqb (fst a) (fst b)
  then ret (snd a =? snd b)
  else raise_ Fatal_error tt.

Definition contracts_have_a_model_statement : Prop :=
  let value := fun x : bool * Z => snd x in
  let compatible := fun x : bool * Z => fst x = true in
  constant_reads_as value compatible (ret (true, 0)) 0
  /\ constant_reads_as value compatible (ret (true, 1)) 1
  /\ constant_reads_as value compatible (ret (true, -1)) (-1)
  /\ tests_equality value compatible model_equal.

(* ======================================================================== *)
(* What an answer of the table says of the model's operation                *)
(* ======================================================================== *)

(* The answers of the table, over a type of numbers: the port's
   [binary_arith_outcome_for_one_side_only]. *)
Definition answer (num : Type) : Type :=
  SimplifyPort.Simplify_binary_primitive.binary_arith_outcome_for_one_side_only
    num.

(* [result j] is the model's result when the unknown argument is [j]. The
   answer is sound if, for every [j] in the range of the integers of the
   width, the result is what the answer says. The range is needed: the
   model's operation wraps, and is the other argument only on a number in
   range. The four other answers say nothing: they are sound whatever the
   result is. *)
Definition answer_is_sound {num : Type} (width : Z) (value : num -> Z)
    (a : answer num) (result : Z -> option Z) : Prop :=
  forall j : Z,
    in_range width j = true ->
    match a with
    | SimplifyPort.Simplify_binary_primitive.Exactly r =>
      result j = Some (value r)
    | SimplifyPort.Simplify_binary_primitive.The_other_side =>
      result j = Some j
    | SimplifyPort.Simplify_binary_primitive.Invalid =>
      result j = None
    | SimplifyPort.Simplify_binary_primitive.Negation_of_the_other_side
    | SimplifyPort.Simplify_binary_primitive.Bitwise_not_of_the_other_side _
    | SimplifyPort.Simplify_binary_primitive.Float_negation_of_the_other_side _
    | SimplifyPort.Simplify_binary_primitive.Cannot_simplify =>
      True
    end.

(* ======================================================================== *)
(* The tagged immediates                                                    *)
(* ======================================================================== *)

(* The port's table at the tagged immediates, and the module of its
   numbers, which is [Number_adjuncts.For_tagged_immediates.Num] of
   decl/Number_adjuncts.v: declared entries, not the definitions of the
   ported Number_adjuncts.v. *)
Module Tagged :=
  SimplifyPort.Simplify_binary_primitive
    .Int_ops_for_binary_arith_tagged_immediate.
Module Num := Tagged.Num.

Section Tagged_immediates.

  (* THREE THINGS THAT THE READER CHOOSES: the machine width that the
     table is given, a reading of a number as an integer, and the numbers
     that fit that machine width. *)
  Variable machine_width : Target_system.Machine_width.t.
  Variable value : Num.t -> Z.
  Variable compatible : Num.t -> Prop.

  (* THE FOUR CONTRACTS. Each is a claim about the compiler that is not
     proved. *)

  (* [Num.zero] at the machine width never raises; if it returns, the
     number is compatible and reads as 0, and the state is as it was. *)
  Definition zero_is_0 : Prop :=
    constant_reads_as value compatible (Num.zero machine_width) 0.

  (* [Num.one]: the same, 1. *)
  Definition one_is_1 : Prop :=
    constant_reads_as value compatible (Num.one machine_width) 1.

  (* [Num.minus_one]: the same, -1. *)
  Definition minus_one_is_m1 : Prop :=
    constant_reads_as value compatible (Num.minus_one machine_width) (-1).

  (* [Num.equal], ON TWO COMPATIBLE NUMBERS, never raises; if it returns,
     it says whether the two read as the same integer, and the state is as
     it was. *)
  Definition equal_is_equality : Prop :=
    tests_equality value compatible Num.equal.

  (* WHAT IS CONCLUDED. What [op_lhs_unknown] answers for an operation
     and a compatible right argument is sound for the model's operation
     at the width of the model's tagged immediates, the unknown argument
     on the left. (The model's result is written as the premise [results]
     of the model's [let_int_arith_tagged_statement] has it.) *)
  Definition op_lhs_unknown_answers_soundly : Prop :=
    forall (op : P.binary_int_arith_op) (rhs : Num.t),
      compatible rhs ->
      pure_if_returns (Tagged.op_lhs_unknown machine_width op rhs)
        (fun a =>
           answer_is_sound tagged_width value a
             (fun j =>
                eval_int_arith tagged_width (int_arith_op_of_port op) j
                  (value rhs))).

  (* The same for [op_rhs_unknown], the unknown argument on the right. *)
  Definition op_rhs_unknown_answers_soundly : Prop :=
    forall (op : P.binary_int_arith_op) (lhs : Num.t),
      compatible lhs ->
      pure_if_returns (Tagged.op_rhs_unknown machine_width op lhs)
        (fun a =>
           answer_is_sound tagged_width value a
             (fun j =>
                eval_int_arith tagged_width (int_arith_op_of_port op)
                  (value lhs) j)).

End Tagged_immediates.

(* THE TWO STATEMENTS. For every machine width, every reading and every
   set of compatible numbers that have the four contracts. *)
Definition op_lhs_unknown_statement : Prop :=
  forall (machine_width : Target_system.Machine_width.t)
    (value : Num.t -> Z) (compatible : Num.t -> Prop),
    zero_is_0 machine_width value compatible ->
    one_is_1 machine_width value compatible ->
    minus_one_is_m1 machine_width value compatible ->
    equal_is_equality value compatible ->
    op_lhs_unknown_answers_soundly machine_width value compatible.

Definition op_rhs_unknown_statement : Prop :=
  forall (machine_width : Target_system.Machine_width.t)
    (value : Num.t -> Z) (compatible : Num.t -> Prop),
    zero_is_0 machine_width value compatible ->
    one_is_1 machine_width value compatible ->
    minus_one_is_m1 machine_width value compatible ->
    equal_is_equality value compatible ->
    op_rhs_unknown_answers_soundly machine_width value compatible.
