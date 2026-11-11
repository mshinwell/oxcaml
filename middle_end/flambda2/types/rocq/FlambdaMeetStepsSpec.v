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



(* What the functions that the meet is made of keep, one function at a
   time.

   This file is to be reviewed: the statements, which are about the
   functions of FlambdaMeet.v. The contract of the whole meet is in
   FlambdaMeetSpec.v; it is to be proved from statements of this kind,
   and the join of types uses some of these functions too. The proofs
   are in FlambdaMeetStepsProofs.v, which needs no review.

   What is stated so far.
   - [reduce_head_of_kind_naked_immediate] loses no value
     ([reduce_head_of_kind_naked_immediate_sound_statement]): under a
     valuation that satisfies the environment strictly, a value that
     has a head of naked immediates has the head that the function
     answers, and the function does not answer bottom. Nothing else is
     asked of the environment or of the head. The function reads, for
     each relation of the head, the canonical element of the name that
     the relation is on: a constant gives the number, by the
     compiler's reading of a relation on a constant
     ([Relation.of_const]), and the relation goes; a name replaces the
     name. That the number so read is the number that the relation
     relates the constant to is a statement of
     FlambdaTypeMeaningSpec.v, which on the branch that this one is
     made from still has the older meaning of relations, in which
     [Is_int] relates a poison constant to every number. Until the
     amended statement is under this file it is a premise here
     ([relation_of_const_exact]), which is then to go. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaMeetGrammar FlambdaExpandHead FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec.
Import ListNotations.

(* ======================================================================== *)
(* The relations of a naked immediate, reduced                              *)
(* ======================================================================== *)

(* The compiler's reading of a relation on a constant is the relation:
   if a relation relates a constant to a number, and the compiler reads
   a number for it, it is that one. This is the statement
   [relation_of_const_sound_statement] of FlambdaTypeMeaningSpec.v as
   it is once [Is_int] and [Get_tag] relate no poison (decision D26,
   as revised): the owner of that file has proved it on its own branch.
   It is false of the meaning on the branch that this one is made from.
   It is here as a premise and is to be replaced by that theorem. *)
Definition relation_of_const_exact : Prop :=
  ∀ (statics : static_env) (relation : Relation.t) (c : const) (i n : Z),
    relation_holds statics relation (Value_const c) i ->
    Relation.of_const relation c = Or_bottom.Ok n ->
    i = n.

(* [reduce_head_of_kind_naked_immediate] loses no value. *)
Definition reduce_head_of_kind_naked_immediate_sound_statement : Prop :=
  relation_of_const_exact ->
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t)
    (head : head_of_kind_naked_immediate) (v : value),
    typing_env_satisfied_strictly statics valuation tenv ->
    head_of_kind_naked_immediate_satisfied statics valuation v head ->
    ∃ head' : head_of_kind_naked_immediate,
      reduce_head_of_kind_naked_immediate tenv head = Or_bottom.Ok head'
      ∧ head_of_kind_naked_immediate_satisfied statics valuation v head'.
