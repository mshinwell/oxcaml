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


(* The code age relation of a typing environment: which functions of
   the environment change it, and when it is well formed.

   This file is to be reviewed: [same_but_code_age_relation],
   [code_ages_well_formed] and the statements. The functions are those
   of FlambdaTypingEnv.v ([Typing_env] of
   middle_end/flambda2/types/env/typing_env.ml). The relation is
   FlambdaCodeAgeRelation.v; the order that it stands for
   ([same_or_newer]: a code is another one or a newer version of it)
   and what it is for a relation to be well formed ([well_formed]) are
   FlambdaCodeAgeRelationSpec.v.

   What is stated.
   - The relation of the environment that [create] makes is the empty
     one.
   - Two functions change the relation. [with_code_age_relation] puts
     the relation that it is given. [add_to_code_age_relation] makes a
     code id a newer version of another, or does nothing where it is
     given no older code id. Neither changes anything else of the
     environment: the seven other fields are those of the argument
     ([same_but_code_age_relation]).
   - Every other function of [Typing_env] that answers an environment
     answers one that has the relation of its argument
     ([code_age_relation_kept_statement]).
   - [Typing_env.code_age_relation] reads the relation. Eight
     functions that look a name up, give the aliases or cut the levels
     do not: of two environments that differ in their relations only,
     they answer the same
     ([same_but_code_age_relation_reads_statement]: [names_to_types],
     [aliases], [find], [find_with_binding_time_and_mode], [mem],
     [cut], [type_simple_in_term_exn] and
     [get_canonical_simple_exn]), and the invariant of the
     environment, [types_well_formed] and [typing_env_kinded] hold of
     the one exactly when they hold of the other. Nothing is said here
     of a function that is not one of those.
   - The order. After [add_to_code_age_relation] the new code is a
     newer version of the old one, and the order that the environment
     had still holds if the new code had no older version. If it had
     one, that one is forgotten: [Code_age_relation.add] gives the code
     id a new older version in place of it
     ([add_to_code_age_relation_forgets_statement]). The compiler calls
     the function where it defines a piece of code
     ([Downwards_env.define_code]), with the older version that the
     code states, if it states one.
   - [code_ages_well_formed]: the relation of the environment is well
     formed, which is to say that following it from a code id, in one
     step or more, never comes back to that code id. It reads the
     relation only, so every function that keeps the relation keeps
     it. It holds of [create].
     [add_to_code_age_relation] keeps it exactly when the old code is
     not the new one or a newer version of it; the function does not
     check that, as [Code_age_relation.add] does not.

   [code_ages_well_formed] is beside the invariant of the environment
   (FlambdaTypingEnvInvariantSpec.v), as [types_well_formed] is, and is
   not a conjunct of it: [add_to_code_age_relation] keeps the invariant
   whatever code ids it is given, and one call of it makes, from
   [create], an environment that has the invariant and whose relation
   is not well formed
   ([add_to_code_age_relation_not_well_formed_statement]). Whether the
   relation of every environment that the compiler makes is well formed
   is the question of the comment before [well_formed] in
   FlambdaCodeAgeRelationSpec.v.

   What is not stated here: what the relation says of the values of a
   run. What satisfies an environment (FlambdaTypingEnvSpec.v) does not
   read the relation.

   The proofs are in FlambdaTypingEnvCodeAgeProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaCodeAgeRelation FlambdaCodeAgeRelationSpec
  FlambdaTypingEnv FlambdaTypingEnvInvariantSpec FlambdaTypingEnvKindedSpec.
Import ListNotations.

(* ======================================================================== *)
(* Which functions change the relation                                      *)
(* ======================================================================== *)

Definition create_code_age_relation_statement : Prop :=
  Typing_env.code_age_relation Typing_env.create = Code_age_relation.empty.

(* [tenv'] is [tenv] but for its code age relation, which may be
   another. *)
Definition same_but_code_age_relation (tenv tenv' : Typing_env.t) : Prop :=
  Typing_env.defined_symbols tenv' = Typing_env.defined_symbols tenv
  ∧ Typing_env.prev_levels tenv' = Typing_env.prev_levels tenv
  ∧ Typing_env.current_level tenv' = Typing_env.current_level tenv
  ∧ Typing_env.just_after_level tenv' = Typing_env.just_after_level tenv
  ∧ Typing_env.next_binding_time tenv' = Typing_env.next_binding_time tenv
  ∧ Typing_env.min_binding_time tenv' = Typing_env.min_binding_time tenv
  ∧ Typing_env.is_bottom tenv' = Typing_env.is_bottom tenv.

(* [with_code_age_relation] puts the relation, and changes nothing
   else... *)
Definition with_code_age_relation_statement : Prop :=
  ∀ (tenv : Typing_env.t) (rel : Code_age_relation.t),
    Typing_env.code_age_relation (Typing_env.with_code_age_relation tenv rel)
    = rel
    ∧ same_but_code_age_relation tenv
        (Typing_env.with_code_age_relation tenv rel).

(* ... so that to put the relation that the environment has is to
   change nothing. *)
Definition with_code_age_relation_same_statement : Prop :=
  ∀ tenv : Typing_env.t,
    Typing_env.with_code_age_relation tenv (Typing_env.code_age_relation tenv)
    = tenv.

(* [add_to_code_age_relation] changes the relation only. *)
Definition add_to_code_age_relation_same_but_statement : Prop :=
  ∀ (tenv : Typing_env.t) (new_code_id : code_id)
    (old_code_id : option code_id),
    same_but_code_age_relation tenv
      (Typing_env.add_to_code_age_relation tenv new_code_id old_code_id).

(* With no older code id it changes nothing. *)
Definition add_to_code_age_relation_none_statement : Prop :=
  ∀ (tenv : Typing_env.t) (new_code_id : code_id),
    Typing_env.add_to_code_age_relation tenv new_code_id None = tenv.

(* With one, the older version of the new code id is that one, and the
   older version of every other code id is the one that it had. *)
Definition add_to_code_age_relation_older_version_statement : Prop :=
  ∀ (tenv : Typing_env.t) (new_code_id old_code_id id : code_id),
    Code_age_relation.get_older_version_of
      (Typing_env.code_age_relation
         (Typing_env.add_to_code_age_relation tenv new_code_id
            (Some old_code_id)))
      id
    = if Pos.eqb id new_code_id
      then Some old_code_id
      else
        Code_age_relation.get_older_version_of
          (Typing_env.code_age_relation tenv) id.

(* Every other function of [Typing_env] that answers an environment
   answers one that has the relation of its argument. *)
Definition code_age_relation_kept_statement : Prop :=
  ∀ tenv : Typing_env.t,
    let rel := Typing_env.code_age_relation tenv in
    Typing_env.code_age_relation (Typing_env.make_bottom tenv) = rel
    ∧ (∀ (current_level : Typing_env.One_level.t)
         (just_after_level : Cached_level.t),
        Typing_env.code_age_relation
          (Typing_env.with_current_level tenv current_level just_after_level)
        = rel)
    ∧ (∀ (current_level : Typing_env.One_level.t)
         (just_after_level : Cached_level.t)
         (next_binding_time : Binding_time.t),
        Typing_env.code_age_relation
          (Typing_env.with_current_level_and_next_binding_time tenv
             current_level just_after_level next_binding_time)
        = rel)
    ∧ (∀ aliases : Aliases.t,
        Typing_env.code_age_relation (Typing_env.with_aliases tenv aliases)
        = rel)
    ∧ Typing_env.code_age_relation (Typing_env.increment_scope tenv) = rel
    ∧ Typing_env.code_age_relation (Typing_env.bump_current_level_scope tenv)
      = rel
    ∧ (∀ (var : variable) (kind : flambda_kind) (name_mode : Name_mode.t),
        Typing_env.code_age_relation
          (Typing_env.add_variable_definition tenv var kind name_mode)
        = rel)
    ∧ (∀ sym : symbol,
        Typing_env.code_age_relation
          (Typing_env.add_symbol_definition tenv sym)
        = rel)
    ∧ (∀ syms : list symbol,
        Typing_env.code_age_relation
          (Typing_env.add_symbol_definitions tenv syms)
        = rel)
    ∧ (∀ (n : name) (name_mode : Name_mode.t) (kind : flambda_kind)
         (tenv' : Typing_env.t),
        Typing_env.add_definition tenv n name_mode kind = Some tenv' ->
        Typing_env.code_age_relation tenv' = rel)
    ∧ (∀ params : list (variable * flambda_kind),
        Typing_env.code_age_relation
          (Typing_env.add_definitions_of_params tenv params)
        = rel)
    ∧ (∀ (n : name) (ty : flambda_type),
        Typing_env.code_age_relation (Typing_env.replace_equation tenv n ty)
        = rel)
    ∧ (∀ (canonical_element1 canonical_element2 : simple)
         (result : Typing_env.add_alias_result),
        Typing_env.add_alias tenv canonical_element1 canonical_element2
        = Some (Ok result) ->
        Typing_env.code_age_relation (Typing_env.add_alias_result_t result)
        = rel)
    ∧ Typing_env.code_age_relation (Typing_env.closure_env tenv) = rel.

(* ======================================================================== *)
(* The lookups, the aliases and [cut] do not read the relation              *)
(* ======================================================================== *)

(* Of two environments that differ in their relations only, these eight
   functions answer the same. [Typing_env.code_age_relation] is the
   function that tells the two apart. *)
Definition same_but_code_age_relation_reads_statement : Prop :=
  ∀ tenv tenv' : Typing_env.t,
    same_but_code_age_relation tenv tenv' ->
    Typing_env.names_to_types tenv' = Typing_env.names_to_types tenv
    ∧ Typing_env.aliases tenv' = Typing_env.aliases tenv
    ∧ (∀ (n : name) (kind : option flambda_kind),
        Typing_env.find tenv' n kind = Typing_env.find tenv n kind)
    ∧ (∀ (n : name) (kind : option flambda_kind),
        Typing_env.find_with_binding_time_and_mode tenv' n kind
        = Typing_env.find_with_binding_time_and_mode tenv n kind)
    ∧ (∀ (min_name_mode : option Name_mode.t) (n : name),
        Typing_env.mem min_name_mode tenv' n
        = Typing_env.mem min_name_mode tenv n)
    ∧ (∀ cut_after : Scope.t,
        Typing_env.cut tenv' cut_after = Typing_env.cut tenv cut_after)
    ∧ (∀ (min_name_mode : option Name_mode.t) (s : simple),
        Typing_env.type_simple_in_term_exn tenv' min_name_mode s
        = Typing_env.type_simple_in_term_exn tenv min_name_mode s)
    ∧ (∀ (min_name_mode name_mode_of_existing_simple : option Name_mode.t)
         (s : simple),
        Typing_env.get_canonical_simple_exn tenv' min_name_mode
          name_mode_of_existing_simple s
        = Typing_env.get_canonical_simple_exn tenv min_name_mode
            name_mode_of_existing_simple s).

(* The invariant of the environment, that its types are well formed and
   that it is kinded hold of the one exactly when they hold of the
   other. So [with_code_age_relation] and [add_to_code_age_relation]
   keep the three. *)
Definition same_but_code_age_relation_invariant_statement : Prop :=
  ∀ tenv tenv' : Typing_env.t,
    same_but_code_age_relation tenv tenv' ->
    (typing_env_invariant tenv' <-> typing_env_invariant tenv)
    ∧ (types_well_formed tenv' <-> types_well_formed tenv)
    ∧ (typing_env_kinded tenv' <-> typing_env_kinded tenv).

(* ======================================================================== *)
(* The order                                                                *)
(* ======================================================================== *)

(* After [add_to_code_age_relation], the new code is a newer version of
   the old one. *)
Definition add_to_code_age_relation_newer_statement : Prop :=
  ∀ (tenv : Typing_env.t) (new_code_id old_code_id : code_id),
    same_or_newer
      (Typing_env.code_age_relation
         (Typing_env.add_to_code_age_relation tenv new_code_id
            (Some old_code_id)))
      new_code_id old_code_id.

(* If the new code had no older version, the order that the environment
   had still holds. *)
Definition add_to_code_age_relation_order_grows_statement : Prop :=
  ∀ (tenv : Typing_env.t) (new_code_id : code_id)
    (old_code_id : option code_id) (id id' : code_id),
    Code_age_relation.get_older_version_of
      (Typing_env.code_age_relation tenv) new_code_id
    = None ->
    same_or_newer (Typing_env.code_age_relation tenv) id id' ->
    same_or_newer
      (Typing_env.code_age_relation
         (Typing_env.add_to_code_age_relation tenv new_code_id old_code_id))
      id id'.

(* If it had one, that one is forgotten: here code 1 is made a newer
   version of code 2 and then of code 3, and after that it is not a
   newer version of code 2. *)
Definition add_to_code_age_relation_forgets_statement : Prop :=
  let tenv :=
    Typing_env.add_to_code_age_relation Typing_env.create 1%positive
      (Some 2%positive)
  in
  let tenv' :=
    Typing_env.add_to_code_age_relation tenv 1%positive (Some 3%positive)
  in
  same_or_newer (Typing_env.code_age_relation tenv) 1%positive 2%positive
  ∧ ~ same_or_newer (Typing_env.code_age_relation tenv') 1%positive
        2%positive.

(* ======================================================================== *)
(* A well-formed relation                                                   *)
(* ======================================================================== *)

(* The code age relation of the environment is well formed. *)
Definition code_ages_well_formed (tenv : Typing_env.t) : Prop :=
  well_formed (Typing_env.code_age_relation tenv).

Definition create_code_ages_well_formed_statement : Prop :=
  code_ages_well_formed Typing_env.create.

Definition with_code_age_relation_well_formed_statement : Prop :=
  ∀ (tenv : Typing_env.t) (rel : Code_age_relation.t),
    code_ages_well_formed (Typing_env.with_code_age_relation tenv rel)
    <-> well_formed rel.

(* [add_to_code_age_relation] keeps the relation well formed exactly
   when the old code is not the new one or a newer version of it. *)
Definition add_to_code_age_relation_well_formed_statement : Prop :=
  ∀ (tenv : Typing_env.t) (new_code_id old_code_id : code_id),
    code_ages_well_formed tenv ->
    (code_ages_well_formed
       (Typing_env.add_to_code_age_relation tenv new_code_id
          (Some old_code_id))
     <-> ~ same_or_newer (Typing_env.code_age_relation tenv) old_code_id
           new_code_id).

(* It does not check that: a code that is made a newer version of
   itself gives an environment that has the invariant and whose
   relation is not well formed. *)
Definition add_to_code_age_relation_not_well_formed_statement : Prop :=
  let tenv :=
    Typing_env.add_to_code_age_relation Typing_env.create 1%positive
      (Some 1%positive)
  in
  typing_env_invariant tenv ∧ ~ code_ages_well_formed tenv.
