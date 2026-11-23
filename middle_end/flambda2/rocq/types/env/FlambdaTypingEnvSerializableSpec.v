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


(* What a compilation unit exports of its typing environment: the two
   functions of [Typing_env.Serializable] that the model has.

   This file is to be reviewed: [relations_agree], [names_disjoint] and
   the statements. The record and the two functions,
   [predefined_exceptions] and [merge], are in FlambdaTypingEnv.v
   ([Serializable] of middle_end/flambda2/types/env/typing_env.ml). The
   compiler calls the first for the unit of the predefined exceptions
   (cmx/flambda_cmx.ml) and the second where it reads a .cmx file that
   has the exports of several units
   (cmx/flambda_cmx_format.ml, [import_typing_env_and_code]). The model
   reads no .cmx file, and no function of it makes a typing environment
   from a [Serializable.t]: nothing here is about what satisfies one.

   What is stated.
   - [predefined_exceptions]: the symbols given, no pair of the code
     age relation and no type.
   - [merge] answers exactly when the two relations give no code id two
     different older versions and no name is bound in both
     ([merge_defined_statement]). Where it answers, the symbols are
     those of the first followed by those of the second; a code id has
     an older version in the answer exactly when it has that one in one
     of the two; a name has a type, with its binding time and name
     mode, in the answer exactly when it has that one in one of the two
     ([merge_answer_statement]). So a code that is another one or a newer
     version of it in one of the two is so in the answer
     ([merge_order_statement]).
   - [merge] does not keep relations well formed: there are two
     relations, each well formed, of which the first makes code 1 a
     newer version of code 2 and the second makes code 2 a newer
     version of code 1, and [merge] answers a relation that has both
     pairs ([merge_not_well_formed_statement]). The compiler's function
     checks no more than this one does.
   - What [predefined_exceptions] gives, merged with a
     [Serializable.t], is that one with the symbols in front.
   - A [Serializable.t] merged with itself: there is an answer exactly
     when it binds no name ([merge_with_itself_statement]). Here the
     model differs from the compiler, whose [Name.Map.disjoint_union]
     answers its first argument when its two arguments are one map in
     memory (the head of FlambdaTypingEnv.v, "The differences").

   The proofs are in FlambdaTypingEnvSerializableProofs.v, which needs
   no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaCodeAgeRelation FlambdaCodeAgeRelationSpec FlambdaTypingEnv.
Import ListNotations.

(* ======================================================================== *)
(* [predefined_exceptions]                                                  *)
(* ======================================================================== *)

Definition predefined_exceptions_statement : Prop :=
  ∀ symbols : list symbol,
    let t := Typing_env.Serializable.predefined_exceptions symbols in
    Typing_env.Serializable.defined_symbols_without_equations t = symbols
    ∧ (∀ id : code_id,
        Code_age_relation.get_older_version_of
          (Typing_env.Serializable.code_age_relation t) id
        = None)
    ∧ (∀ n : name,
        Keyed.lookup name_eqb n (Typing_env.Serializable.names_to_types t)
        = None).

(* ======================================================================== *)
(* [merge]                                                                  *)
(* ======================================================================== *)

(* The two relations give no code id two different older versions. *)
Definition relations_agree (rel1 rel2 : Code_age_relation.t) : Prop :=
  ∀ id older1 older2 : code_id,
    Code_age_relation.get_older_version_of rel1 id = Some older1 ->
    Code_age_relation.get_older_version_of rel2 id = Some older2 ->
    older1 = older2.

(* No name is bound in both maps. *)
Definition names_disjoint {A : Type} (names1 names2 : Keyed.finite_map name A)
    : Prop :=
  ∀ n : name,
    Keyed.is_bound name_eqb n names1 = true ->
    Keyed.is_bound name_eqb n names2 = false.

(* When [merge] answers. *)
Definition merge_defined_statement : Prop :=
  ∀ t1 t2 : Typing_env.Serializable.t,
    Typing_env.Serializable.merge t1 t2 <> None
    <-> relations_agree (Typing_env.Serializable.code_age_relation t1)
          (Typing_env.Serializable.code_age_relation t2)
        ∧ names_disjoint (Typing_env.Serializable.names_to_types t1)
            (Typing_env.Serializable.names_to_types t2).

(* What it answers. *)
Definition merge_answer_statement : Prop :=
  ∀ t1 t2 t : Typing_env.Serializable.t,
    Typing_env.Serializable.merge t1 t2 = Some t ->
    Typing_env.Serializable.defined_symbols_without_equations t
    = Typing_env.Serializable.defined_symbols_without_equations t1
      ++ Typing_env.Serializable.defined_symbols_without_equations t2
    ∧ (∀ id older : code_id,
        Code_age_relation.get_older_version_of
          (Typing_env.Serializable.code_age_relation t) id
        = Some older
        <-> Code_age_relation.get_older_version_of
              (Typing_env.Serializable.code_age_relation t1) id
            = Some older
            ∨ Code_age_relation.get_older_version_of
                (Typing_env.Serializable.code_age_relation t2) id
              = Some older)
    ∧ (∀ (n : name) (entry : flambda_type * Binding_time.With_name_mode.t),
        Keyed.lookup name_eqb n (Typing_env.Serializable.names_to_types t)
        = Some entry
        <-> Keyed.lookup name_eqb n
              (Typing_env.Serializable.names_to_types t1)
            = Some entry
            ∨ Keyed.lookup name_eqb n
                (Typing_env.Serializable.names_to_types t2)
              = Some entry).

(* A code that is another one or a newer version of it in one of the
   two is so in the answer. *)
Definition merge_order_statement : Prop :=
  ∀ (t1 t2 t : Typing_env.Serializable.t) (id id' : code_id),
    Typing_env.Serializable.merge t1 t2 = Some t ->
    same_or_newer (Typing_env.Serializable.code_age_relation t1) id id'
    ∨ same_or_newer (Typing_env.Serializable.code_age_relation t2) id id' ->
    same_or_newer (Typing_env.Serializable.code_age_relation t) id id'.

(* Two well-formed relations whose merge is not well formed. *)
Definition merge_not_well_formed_statement : Prop :=
  let t1 :=
    Typing_env.Serializable.Build_t []
      (Code_age_relation.add Code_age_relation.empty 1%positive 2%positive)
      []
  in
  let t2 :=
    Typing_env.Serializable.Build_t []
      (Code_age_relation.add Code_age_relation.empty 2%positive 1%positive)
      []
  in
  well_formed (Typing_env.Serializable.code_age_relation t1)
  ∧ well_formed (Typing_env.Serializable.code_age_relation t2)
  ∧ ∃ t : Typing_env.Serializable.t,
      Typing_env.Serializable.merge t1 t2 = Some t
      ∧ ~ well_formed (Typing_env.Serializable.code_age_relation t).

(* What [predefined_exceptions] gives, merged with a [Serializable.t],
   is that one with the symbols in front. *)
Definition merge_predefined_exceptions_statement : Prop :=
  ∀ (symbols : list symbol) (t : Typing_env.Serializable.t),
    Typing_env.Serializable.merge
      (Typing_env.Serializable.predefined_exceptions symbols) t
    = Some
        (Typing_env.Serializable.Build_t
           (symbols
            ++ Typing_env.Serializable.defined_symbols_without_equations t)
           (Typing_env.Serializable.code_age_relation t)
           (Typing_env.Serializable.names_to_types t)).

(* A [Serializable.t] merged with itself: there is an answer exactly
   when it binds no name. *)
Definition merge_with_itself_statement : Prop :=
  ∀ t : Typing_env.Serializable.t,
    Typing_env.Serializable.merge t t <> None
    <-> Typing_env.Serializable.names_to_types t = [].
