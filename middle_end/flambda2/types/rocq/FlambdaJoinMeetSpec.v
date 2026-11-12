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


(* What is stated of the join put together with the meet
   (FlambdaJoinMeet.v).

   This file is to be reviewed: the statements. The proofs are in
   FlambdaJoinMeetProofs.v, which needs no review.

   - The conversion between the two transcriptions of expanded types
     keeps the type and the kind ([join_expanded_to_type_statement]).
   - The parameters fixed there have what the statements about the
     join of environments suppose of parameters
     ([join_parameters_sound_statement]): [fresh_avoids],
     [parameters_type_eqb_sound], [env_extension_eqb_sound],
     [expand_const_sound].
   - The expansion of heads meets the contract that the join of types
     supposes of it ([expand_head_for_join_sound_statement]), by the
     statements of FlambdaExpandHeadSpec.v. (The reduction of heads of
     naked immediates meets its contract by
     [reduce_head_of_kind_naked_immediate_sound_statement] of
     FlambdaMeetStepsSpec.v, which is that contract.)
   - So what the join adds to the target is true
     ([model_join_true_statement]): [join_adds_true] of
     FlambdaJoinDefineSpec.v for [model_join], with the premises of
     [join_with_true_statement] on the inputs and none on a join of
     types or on parameters. It is for any choices, any depth and any
     fuel, and for the functions of [Meet_env]; as there, nothing is
     said of what those functions answer.

   Examples of what [model_join] computes are in
   FlambdaJoinMeetExamplesSpec.v. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvKindedSpec FlambdaJoinEnv
  FlambdaJoinSpec FlambdaJoinEnvSpec FlambdaJoinStateSpec
  FlambdaJoinDefineSpec FlambdaJoinTypes FlambdaJoinTypesSpec
  FlambdaMeetGrammar FlambdaExpandHead FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec FlambdaJoinMeet.
Import ListNotations.

(* An expanded type and its conversion are the same type, of the same
   kind. *)
Definition join_expanded_to_type_statement : Prop :=
  ∀ expanded : FlambdaExpandHead.Expanded_type.t,
    FlambdaJoinTypes.Expanded_type.to_type (join_expanded expanded)
    = FlambdaExpandHead.Expanded_type.to_type expanded
    ∧ FlambdaJoinTypes.Expanded_type.kind (join_expanded expanded)
      = FlambdaExpandHead.Expanded_type.kind expanded.

(* The parameters have what is supposed of parameters. *)
Definition join_parameters_sound_statement : Prop :=
  ∀ join_depth : nat,
    fresh_avoids (join_parameters join_depth)
    ∧ parameters_type_eqb_sound (join_parameters join_depth)
    ∧ env_extension_eqb_sound (join_parameters join_depth)
    ∧ expand_const_sound (join_parameters join_depth).

(* The expansion of heads meets the contract of FlambdaJoinTypesSpec.v,
   with the invariant of typing environments for what an environment
   must be. *)
Definition expand_head_for_join_sound_statement : Prop :=
  FlambdaJoinTypesSpec.expand_head_sound typing_env_invariant
    expand_head_for_join.

(* What the join that Simplify calls adds to the target is true. *)
Definition model_join_true_statement : Prop :=
  ∀ (A : Type) (join_choices : Join_env.choices) (meet_choices : meet_choices)
    (join_depth : nat) (fuel : fuels) (avoid : list variable)
    (inputs : join_inputs A) (target : Typing_env.t) (analysis : Analysis.t A),
    join_inputs_well_formed typing_env_invariant avoid inputs ->
    uses_kinded inputs ->
    uses_agree_with_source_on_kinds inputs ->
    (∃ (index : Index.t) (use : Typing_env.t),
       use_at inputs index use ∧ Typing_env.is_bottom use = false) ->
    model_join join_choices meet_choices join_depth fuel avoid inputs
    = Some (target, analysis) ->
    join_adds_true meet_env_functions
      (model_meet_expanded_head join_choices meet_choices join_depth fuel)
      inputs target analysis.
