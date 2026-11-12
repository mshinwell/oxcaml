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


(* The proofs of the statements of FlambdaJoinMeetSpec.v. This file
   needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaNameAbstractionSpec
  FlambdaNameAbstractionProofs.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeEqualSpec FlambdaTypeEqualProofs
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvInvariantSpec
  FlambdaTypingEnvKindedSpec FlambdaJoinEnv FlambdaJoinSpec
  FlambdaJoinEnvSpec FlambdaJoinStateSpec FlambdaJoinStateProofs
  FlambdaJoinDefineSpec FlambdaJoinDefineProofs FlambdaJoinTypes
  FlambdaJoinTypesSpec FlambdaJoinTypesWithEnvSpec
  FlambdaJoinTypesWithEnvProofs FlambdaMeetGrammar FlambdaExpandHead
  FlambdaExpandHeadSpec FlambdaExpandHeadProofs FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec FlambdaMeetStepsSpec FlambdaMeetStepsProofs
  FlambdaJoinMeet FlambdaJoinMeetSpec.
Import ListNotations.

Theorem join_expanded_to_type : join_expanded_to_type_statement.
Proof.
  intros [k [ | [head | head | k' head | head | head] | ]];
    split; reflexivity.
Qed.

Theorem join_parameters_sound : join_parameters_sound_statement.
Proof.
  intros join_depth. split; [ | split; [ | split ] ].
  - intros names Hin. cbn [Join_env.fresh join_parameters] in Hin.
    pose proof (fresh_name_fresh names) as Hfresh.
    apply (proj2 (among_In _ _)) in Hin. congruence.
  - intros t t' statics valuation v Heqb Hsat.
    exact (proj2 (type_equal_satisfied statics valuation v t t' Heqb) Hsat).
  - intros extension extension' statics valuation Heqb Hsat.
    exact (proj1 (env_extension_equal_satisfied statics valuation extension
                    extension' Heqb) Hsat).
  - intros c. cbn [Join_env.expand_const join_parameters].
    split; [ exact (create_const_free_variables c) | ].
    split; [ intros tenv; exact (create_const_kinded tenv c) | ].
    intros statics valuation. exact (create_const_sound statics valuation c).
Qed.

Theorem expand_head_for_join_sound : expand_head_for_join_sound_statement.
Proof.
  intros tenv ty expanded Hexpand. unfold expand_head_for_join in Hexpand.
  destruct (FlambdaExpandHead.expand_head tenv ty) as [expanded0 | ] eqn:H0;
    [ | discriminate ].
  injection Hexpand as <-.
  destruct (join_expanded_to_type expanded0) as [Htype Hkind].
  rewrite Htype, Hkind.
  split; [ | split; [ | split ] ].
  - intros statics valuation v Hsat Hty.
    exact (FlambdaExpandHeadProofs.expand_head_sound statics valuation tenv
             ty expanded0 v Hsat Hty H0).
  - intros Hinvariant Hscope x Hx.
    exact (expand_head_closed tenv ty expanded0
             (invariant_types_closed tenv Hinvariant) Hscope H0 x Hx).
  - intros Hkinded Hty.
    exact (expand_head_kinded tenv ty expanded0 (proj1 Hkinded) Hty H0).
  - intros Hconstants Hty.
    exact (expand_head_kind tenv ty expanded0 Hconstants Hty H0).
Qed.

Theorem model_join_true : model_join_true_statement.
Proof.
  intros A join_choices meet_choices join_depth fuel avoid inputs target
    analysis Hinputs Hkinded Hagree Hsome Hjoin.
  destruct (join_parameters_sound join_depth)
    as [Hfresh [Heqb [Hextension Hconst]]].
  assert (Hreduce :
            FlambdaJoinTypesSpec.reduce_head_of_kind_naked_immediate_sound
              reduce_head_of_kind_naked_immediate).
  { intros tenv statics valuation v head Hsat Hhead.
    exact (FlambdaMeetStepsProofs.reduce_head_of_kind_naked_immediate_sound
             statics valuation tenv head v Hsat Hhead). }
  exact (join_with_true A Meet_env.t meet_expanded_head meet_env_functions
           (join_parameters join_depth) (fuel_of_env fuel) join_choices
           (model_join_of_types join_depth fuel)
           (model_meet_expanded_head join_choices meet_choices join_depth
              fuel)
           avoid inputs target analysis
           (n_way_join_of_types_true (source inputs)
              (join_parameters join_depth) (fuel_of_env fuel)
              expand_head_for_join reduce_head_of_kind_naked_immediate
              (fuel_of_types fuel) Hfresh Heqb Hextension
              expand_head_for_join_sound Hreduce)
           (n_way_join_keeps_envs (join_parameters join_depth)
              (fuel_of_env fuel) (fuel_of_types fuel) expand_head_for_join
              reduce_head_of_kind_naked_immediate type_eqb block_shape_eqb)
           Hfresh Heqb Hconst Hinputs Hkinded Hagree Hsome Hjoin).
Qed.
