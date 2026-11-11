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



(* What the functions of [Meet_env] keep.

   This file is to be reviewed: the statements, which are about the
   functions of FlambdaMeetEnv.v ([Meet_env], types/env/meet_env.ml):
   the functions through which a meet, and the join that it calls,
   change a typing environment. Each statement says that a function
   answers an environment that is the one given, extended
   ([meet_env_extends], FlambdaMeetSpec.v), and in which a meet may be
   made ([typing_env_fits]). No value and no valuation is supposed.
   The proofs are in FlambdaMeetEnvProofs.v, which needs no review.

   What is stated so far: of [Meet_env.make_bottom]
   ([make_bottom_keeps_statement]) and of
   [Meet_env.add_variable_definition]
   ([add_variable_definition_keeps_statement]). The second asks that
   the variable is not bound (the compiler refuses one that is, when
   invariant checks are on, and the invariant of typing environments
   is kept only then), and that the unknown type of the kind is well
   formed, which is a fact about the predicate of well-formed types
   that is a parameter here until that predicate is under this
   branch. The functions that add an equation are to come. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvKindedSpec
  FlambdaMeetGrammar FlambdaExpandHead FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec.
Import ListNotations.

(* [Meet_env.make_bottom]. *)
Definition make_bottom_keeps_statement : Prop :=
  ∀ (type_well_formed : flambda_type -> bool) (menv : Meet_env.t),
    typing_env_fits type_well_formed (Meet_env.typing_env menv) ->
    meet_env_extends menv (Meet_env.make_bottom menv)
    ∧ typing_env_fits type_well_formed
        (Meet_env.typing_env (Meet_env.make_bottom menv)).

(* [Meet_env.add_variable_definition], of a variable that is not
   bound. *)
Definition add_variable_definition_keeps_statement : Prop :=
  ∀ (type_well_formed : flambda_type -> bool) (menv : Meet_env.t)
    (var : variable) (kind : flambda_kind) (name_mode : Name_mode.t),
    let menv' := Meet_env.add_variable_definition menv var kind name_mode in
    typing_env_fits type_well_formed (Meet_env.typing_env menv) ->
    Typing_env.mem None (Meet_env.typing_env menv) (Name_var var) = false ->
    type_well_formed (unknown kind) = true ->
    meet_env_extends menv menv'
    ∧ typing_env_fits type_well_formed (Meet_env.typing_env menv').
