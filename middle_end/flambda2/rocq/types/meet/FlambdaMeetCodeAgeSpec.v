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

(* The meet of two code ids, in terms of the order that the code age
   relation stands for.

   This file is to be reviewed: the statements, which are about
   [meet_code_id] of FlambdaMeet.v. The proofs are in
   FlambdaMeetCodeAgeProofs.v, which needs no review.

   [meet_code_id] is the compiler's function of that name
   (types/meet_and_n_way_join.ml). It reads the code age relation of the
   typing environment in which the meet works
   ([Meet_env.code_age_relation]) and asks [Code_age_relation.meet]
   (FlambdaCodeAgeRelation.v) which of two code ids is the newer. What a
   relation stands for is the order [same_or_newer] of
   FlambdaCodeAgeRelationSpec.v: [same_or_newer rel id id'] says that
   [id] is [id'] or a newer version of it. The statements here say what
   [meet_code_id] answers in terms of that order.

   What is said.
   - Two code ids that are the same: both inputs
     ([meet_code_id_same_statement]).
   - What an answer entails, of every relation. An answer that is not
     bottom has the environment that was given, and it is one of the
     inputs: no third code id is answered. Both inputs entails that the
     two code ids are the same. The left input entails that they are
     different and that the left one is a newer version of the right
     one; the right input entails the reverse
     ([meet_code_id_ok_statement]). This is not the converse: on a
     relation with a cycle the left code id can be a newer version of
     the right one where the answer is the right input. An answer that
     is bottom entails that neither code id is the other or a newer
     version of it ([meet_code_id_bottom_statement]).
   - Which answer there is, on a relation that is [well_formed]
     (following the relation from a code id, in one step or more, never
     comes back to it): the newer of two code ids
     of which one is a newer version of the other
     ([meet_code_id_left_statement], [meet_code_id_right_statement]),
     and bottom for two that are not so related
     ([meet_code_id_unrelated_statement]). So on such a relation there
     is always an answer ([meet_code_id_answers_statement]). On a
     relation that is not well-formed there may be none: the steps
     that [meet_code_id] gives [Code_age_relation.meet] run out, where
     the compiler's function need not return.
   - No code is lost and none is gained, on a well-formed relation. A
     code id that is at or above both inputs (it is each of them or a
     newer version of it) is at or above the code id answered, and the
     answer is then not bottom
     ([meet_code_id_no_code_lost_statement]). And the code id answered
     is at or above both inputs, of every relation
     ([meet_code_id_newer_statement]).
   - Two code ids to which the relation gives no older version: equal,
     or bottom ([meet_code_id_no_link_statement]). That is what
     [meet_code_id] was before it read the relation. It is so in every
     environment whose relation is empty, and [Typing_env.create]
     makes one.
   - An example: a relation with one code, two newer versions of it,
     and a newer version of one of those
     ([meet_code_id_example_statement]).

   What is not said. These statements do not change the meaning of a
   function type (FlambdaTypeMeaningSpec.v): a function type is still
   true only of a closure of the very code that it names, and for that
   meaning two function types that name two different codes have no
   closure in common. So, for two different codes, the clause "no value
   is lost" of the contract of the meet of function types
   ([meet_function_type_ok_statement], FlambdaMeetProductsSpec.v;
   [meet_call_ok], FlambdaMeetStepsSpec.v) is true because no value has
   both types. What that contract asks of every answer that is not
   bottom stays: the environment answered extends the one given and
   fits, the part answered fits it, and [new_names_avoided] holds
   (FlambdaMeetSpec.v). Here the environment answered is the one
   given, so no variable is introduced. That a closure of a newer
   version has the type that names the older code, and so that the
   answers here lose no closure, is for the meaning to say
   (discrepancy T4-4). The statements are of one compilation unit, as
   the model's environment is: nothing is said of a relation that
   another unit gives. *)

From Stdlib Require Import PArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaCodeAgeRelation FlambdaCodeAgeRelationSpec FlambdaTypingEnv
  FlambdaMeetEnv FlambdaMeet.
Import ListNotations.

(* ======================================================================== *)
(* What an answer says                                                      *)
(* ======================================================================== *)

(* Two code ids that are the same: both inputs. *)
Definition meet_code_id_same_statement : Prop :=
  ∀ (menv : Meet_env.t) (id : code_id),
    meet_code_id menv id id = Some (Meet_result.Ok Both_inputs menv).

(* What an answer that is not bottom entails, of every relation. Its
   environment is the one given. Both inputs entails that the two code
   ids are the same; the left input entails that they are different and
   that the left one is a newer version of the right one; the right
   input entails the reverse. No third code id is answered. Which answer
   there is, is said below of a well-formed relation, and not here. *)
Definition meet_code_id_ok_statement : Prop :=
  ∀ (menv menv' : Meet_env.t) (id1 id2 : code_id)
    (r : meet_return_value code_id),
    meet_code_id menv id1 id2 = Some (Meet_result.Ok r menv') ->
    menv' = menv
    ∧ ((r = Both_inputs ∧ id1 = id2)
       ∨ (r = Left_input
          ∧ id1 <> id2
          ∧ same_or_newer (Meet_env.code_age_relation menv) id1 id2)
       ∨ (r = Right_input
          ∧ id1 <> id2
          ∧ same_or_newer (Meet_env.code_age_relation menv) id2 id1)).

(* What an answer that is bottom entails, of every relation: neither
   code id is the other or a newer version of it. *)
Definition meet_code_id_bottom_statement : Prop :=
  ∀ (menv : Meet_env.t) (id1 id2 : code_id) (r : meet_return_value unit),
    meet_code_id menv id1 id2 = Some (Meet_result.Bottom r) ->
    ~ same_or_newer (Meet_env.code_age_relation menv) id1 id2
    ∧ ~ same_or_newer (Meet_env.code_age_relation menv) id2 id1.

(* The code id answered is at or above both inputs, of every relation:
   no code is gained. *)
Definition meet_code_id_newer_statement : Prop :=
  ∀ (menv menv' : Meet_env.t) (id1 id2 : code_id)
    (r : meet_return_value code_id),
    meet_code_id menv id1 id2 = Some (Meet_result.Ok r menv') ->
    same_or_newer (Meet_env.code_age_relation menv)
      (extract_value r id1 id2) id1
    ∧ same_or_newer (Meet_env.code_age_relation menv)
        (extract_value r id1 id2) id2.

(* ======================================================================== *)
(* Which answer there is, on a well-formed relation                         *)
(* ======================================================================== *)

(* The left code id is a newer version of the right one: the left
   input. *)
Definition meet_code_id_left_statement : Prop :=
  ∀ (menv : Meet_env.t) (id1 id2 : code_id),
    well_formed (Meet_env.code_age_relation menv) ->
    id1 <> id2 ->
    same_or_newer (Meet_env.code_age_relation menv) id1 id2 ->
    meet_code_id menv id1 id2 = Some (Meet_result.Ok Left_input menv).

(* The right code id is a newer version of the left one: the right
   input. *)
Definition meet_code_id_right_statement : Prop :=
  ∀ (menv : Meet_env.t) (id1 id2 : code_id),
    well_formed (Meet_env.code_age_relation menv) ->
    id1 <> id2 ->
    same_or_newer (Meet_env.code_age_relation menv) id2 id1 ->
    meet_code_id menv id1 id2 = Some (Meet_result.Ok Right_input menv).

(* Neither is the other or a newer version of it: bottom. *)
Definition meet_code_id_unrelated_statement : Prop :=
  ∀ (menv : Meet_env.t) (id1 id2 : code_id),
    well_formed (Meet_env.code_age_relation menv) ->
    ~ same_or_newer (Meet_env.code_age_relation menv) id1 id2 ->
    ~ same_or_newer (Meet_env.code_age_relation menv) id2 id1 ->
    meet_code_id menv id1 id2 = Some (Meet_result.Bottom (New_result tt)).

(* There is always an answer. *)
Definition meet_code_id_answers_statement : Prop :=
  ∀ (menv : Meet_env.t) (id1 id2 : code_id),
    well_formed (Meet_env.code_age_relation menv) ->
    ∃ result : Meet_result.t code_id,
      meet_code_id menv id1 id2 = Some result.

(* No code is lost: a code id that is at or above both inputs is at or
   above the code id answered, and the answer is not bottom. *)
Definition meet_code_id_no_code_lost_statement : Prop :=
  ∀ (menv : Meet_env.t) (id1 id2 code : code_id),
    well_formed (Meet_env.code_age_relation menv) ->
    same_or_newer (Meet_env.code_age_relation menv) code id1 ->
    same_or_newer (Meet_env.code_age_relation menv) code id2 ->
    ∃ r : meet_return_value code_id,
      meet_code_id menv id1 id2 = Some (Meet_result.Ok r menv)
      ∧ same_or_newer (Meet_env.code_age_relation menv) code
          (extract_value r id1 id2).

(* ======================================================================== *)
(* Where the relation has no link                                           *)
(* ======================================================================== *)

(* Two code ids to which the relation gives no older version: equal, or
   bottom. *)
Definition meet_code_id_no_link_statement : Prop :=
  ∀ (menv : Meet_env.t) (id1 id2 : code_id),
    Code_age_relation.get_older_version_of (Meet_env.code_age_relation menv)
      id1
    = None ->
    Code_age_relation.get_older_version_of (Meet_env.code_age_relation menv)
      id2
    = None ->
    meet_code_id menv id1 id2
    = Some
        (if Pos.eqb id1 id2
         then Meet_result.Ok Both_inputs menv
         else Meet_result.Bottom (New_result tt)).

(* ======================================================================== *)
(* An example                                                               *)
(* ======================================================================== *)

(* An environment whose relation says that code 2 and code 3 are newer
   versions of code 1, and code 4 a newer version of code 2. The three
   links are added by [Typing_env.add_to_code_age_relation], the
   function by which Simplify adds a link. They are data of the
   relation only: no code is defined here. *)
Definition code_age_example_env : Meet_env.t :=
  Meet_env.create
    (Typing_env.add_to_code_age_relation
       (Typing_env.add_to_code_age_relation
          (Typing_env.add_to_code_age_relation Typing_env.create 2%positive
             (Some 1%positive))
          3%positive (Some 1%positive))
       4%positive (Some 2%positive)).

(* The relation is well-formed. Code 4 is met with code 1, two links
   below it: the newer, on either side. Code 4 and code 3 are both
   newer versions of code 1 and neither is one of the other: bottom. *)
Definition meet_code_id_example_statement : Prop :=
  well_formed (Meet_env.code_age_relation code_age_example_env)
  ∧ meet_code_id code_age_example_env 4%positive 1%positive
    = Some (Meet_result.Ok Left_input code_age_example_env)
  ∧ meet_code_id code_age_example_env 1%positive 4%positive
    = Some (Meet_result.Ok Right_input code_age_example_env)
  ∧ meet_code_id code_age_example_env 4%positive 3%positive
    = Some (Meet_result.Bottom (New_result tt)).
