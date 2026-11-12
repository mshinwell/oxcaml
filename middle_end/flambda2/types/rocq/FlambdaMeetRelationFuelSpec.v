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

(* The fuel of the meet that a [Switch] makes where it enters an arm,
   for a scrutinee that is the result of a relation: two units are
   enough.

   This file is to be reviewed: the definitions and the statements.
   It goes on from FlambdaMeetTerminationSpec.v (what it is for the
   fuel to be enough; the meet of an alias of a name with the type of
   a constant) and from FlambdaMeetDepthSpec.v (the meet with a bare
   shape). The functions are those of FlambdaMeet.v and
   FlambdaMeetEnv.v. The proofs are in FlambdaMeetRelationFuelProofs.v,
   which needs no review.

   The meet. Where Simplify enters an arm of a [Switch] it meets the
   type of the scrutinee, an alias of a variable, with the type of the
   number of the arm, an alias of a constant. If the variable is the
   result of [Is_int], [Get_tag] or [Is_null] of a name, the type that
   the environment has for it is a head of naked immediates with an
   inverse relation to that name. The meet then does three things, one
   inside the other.
   - The variable is demoted to the constant, and the type that it
     had is met with the head of the constant
     (FlambdaMeetTerminationSpec.v, [alias_const_fuel_enough_statement]).
   - That is a meet of two heads of naked immediates. The numbers are
     met, and where they get fewer the relation says what the name it
     is a relation of can be, as a type that is added to that name
     ([reduce_inverse_relations]): [any_block] or
     [any_tagged_immediate] for [Is_int], [any_non_null_value] or
     [null] for [Is_null], and for [Get_tag] the type that the choices
     of the meet give for the tags.
   - Adding that type to the name meets it with the type that the
     environment has for the canonical element of the name.
   The last is the meet of a bare shape with a type of the environment
   (FlambdaMeetDepthSpec.v), for which one unit is enough; the second
   is one step more.

   What is stated. [relation_const_fuel_enough_statement]: two units
   of fuel are enough for the meet of the two types, where
   - the canonical element that the meet reads for the first type is
     a name that is canonical, in aliases that are consistent, as in
     [alias_const_fuel_enough_statement];
   - the type that the environment has for that name is a head of
     naked immediates with one inverse relation at most;
   - every type of kind value that the environment has for a name is
     an alias or has no extension ([values_extension_free]);
   - the types that the choices give for [Get_tag] are bare shapes of
     kind value ([get_tag_shapes]); those of the compiler's choice and
     of the repaired choice are ([choices_get_tag_shapes_statement]);
   - the join has [join_of_nothing] (FlambdaMeetDepthSpec.v); the
     join of the model has it where there is fuel for the join of
     environments ([model_join_of_nothing_statement], same file).
   The constant is any constant. Enough is [meet_fuel_enough]: the
   answer is the same whatever is answered where the fuel runs out.
   That the meet answers is not said.

   What the hypotheses are for. One relation at most: each relation
   adds an equation, and after the first the environment is another,
   of which the third hypothesis would have to be shown again; that
   needs that the meet of a bare shape answers a type with no
   extension, which is not stated. Types of kind value with no
   extension: the type that the environment has for the name of the
   relation, or for what that name is an alias of, is met with the
   shape; with an extension in it the meet would add the equations of
   the extension, for which no bound is known. The name of the
   relation is not asked to be canonical, nor to be another than the
   scrutinee: whatever its canonical element is, the type of that is
   an alias or has no extension, or the canonical element is a
   constant and the shape is met with its head, or the name is one
   that an equation is being added to and the equation is passed over.

   An example ([example_relation_fuel_statement]): the environment
   after [let tag = Get_tag p] of FlambdaMeetExamplesSpec.v has what
   is supposed, so two units are enough for the arm for 0, with every
   join and all choices that have what is supposed of them; and with
   the meet that is to be proved and the join that forgets, one unit
   is not enough.

   What is not here: a scrutinee with more relations than one; an
   environment in which a type of kind value has an extension; and
   what the meet answers. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaMeetGrammar
  FlambdaExpandHead FlambdaMeetEnv FlambdaMeet FlambdaMeetSpec
  FlambdaMeetTerminationSpec FlambdaMeetDepthSpec.
From OxCamlFlambda2Types Require FlambdaMeetExamplesSpec.
Import ListNotations.

(* ======================================================================== *)
(* What is supposed of the environment and of the choices                   *)
(* ======================================================================== *)

(* Every type of kind value that the environment has for a name is an
   alias or has no extension. *)
Definition values_extension_free (tenv : Typing_env.t) : Prop :=
  ∀ (name : name) (ty : flambda_type),
    Typing_env.find tenv name (Some Value) = Some ty ->
    get_alias_opt ty <> None ∨ extension_free ty = true.

(* The types that the choices of the meet give for [Get_tag] are bare
   shapes, of kind value. *)
Definition get_tag_shapes (choices : meet_choices) : Prop :=
  ∀ (tags : list Z) (alloc_mode : Alloc_mode.t),
    bare_shape (type_of_get_tag_scrutinee choices tags alloc_mode) = true
    ∧ kind (type_of_get_tag_scrutinee choices tags alloc_mode) = Value.

Definition choices_get_tag_shapes_statement : Prop :=
  get_tag_shapes compiler_choices ∧ get_tag_shapes repaired_choices.

(* ======================================================================== *)
(* The meet for an arm                                                      *)
(* ======================================================================== *)

(* The meet of a type that is an alias of a canonical name with the
   type of a constant, where the type that the environment has for
   the name is a head of naked immediates with one inverse relation
   at most. *)
Definition relation_const_fuel_enough_statement : Prop :=
  ∀ (join : join_scoped_envs) (choices : meet_choices) (tenv : Typing_env.t)
    (t : flambda_type) (n : name) (head : head_of_kind_naked_immediate)
    (c : const),
    join_of_nothing join ->
    get_tag_shapes choices ->
    values_extension_free tenv ->
    aliases_consistent (Typing_env.aliases tenv) ->
    is_canonical (Typing_env.aliases tenv) (simple_of_name n) ->
    Typing_env.get_alias_then_canonical_simple_exn tenv
      (Some Name_mode.in_types) None t
    = Some (Some (simple_of_name n)) ->
    Typing_env.find tenv n (Some (kind t))
    = Some (Type_naked_immediate (Ok (No_alias head))) ->
    length (inverse_relations head) <= 1 ->
    meet_fuel_enough join choices 2 tenv t (this_const c).

(* ======================================================================== *)
(* An example                                                               *)
(* ======================================================================== *)

(* The environment after [let tag = Get_tag p] of
   FlambdaMeetExamplesSpec.v, and the meet for the arm for 0 of a
   [Switch] on [tag]. The environment has what is supposed, so two
   units of fuel are enough, with every join and all choices that have
   what is supposed of them. One unit is not enough, with the meet
   that is to be proved and the join that forgets. *)
Definition example_relation_fuel_statement : Prop :=
  (∀ (join : join_scoped_envs) (choices : meet_choices),
    join_of_nothing join ->
    get_tag_shapes choices ->
    meet_fuel_enough join choices 2 FlambdaMeetExamplesSpec.example_get_tag_env
      FlambdaMeetExamplesSpec.example_tag_type
      FlambdaMeetExamplesSpec.example_zero_type)
  ∧ ¬ meet_fuel_enough FlambdaMeetExamplesSpec.forgetful_join repaired_choices
        1 FlambdaMeetExamplesSpec.example_get_tag_env
        FlambdaMeetExamplesSpec.example_tag_type
        FlambdaMeetExamplesSpec.example_zero_type.
