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


(* Renaming the variables of a typing environment: the action, the free
   variables, and that the functions of the environment commute with it.

   This file is to be reviewed: the action ([rename_level],
   [rename_cached_level], [rename_one_level], [rename_typing_env]), the
   free variables ([level_free_variables], [typing_env_free_variables]),
   the two instances of the interface for things that contain names, and
   the statements. The compiler has no [apply_renaming] for
   [Typing_env.t] or for a level. It has one for what a unit exports of
   its environment ([Typing_env.Serializable.apply_renaming], which
   renames each name and its type and keeps the binding time and the
   name mode, as [rename_cached_level] does of the same map), and one
   for an extension with its existential variables
   ([Typing_env_extension.With_extra_variables.apply_renaming]). The
   model has not the first structure; the second, with its action, is
   in FlambdaTypingEnvExtension.v. The action is here
   because everything that holds names is to have its renaming and its
   free names, with the laws of the interface for things that contain
   names (FlambdaNameAbstractionSpec.v, in ../../rocq/), and the
   functions on it are to commute with renaming.

   A renaming (FlambdaNominalSpec.renaming) permutes variables; a typing
   environment holds no continuation. Symbols, constants, kinds, scopes,
   binding times and name modes are not renamed. The action renames
   every variable that the environment writes:
   - in a level, the variables that the level defines, in both of the
     maps that list them, and its equations: the name that each is on
     ([FlambdaTypeRenameSpec.rename_name]) and its type
     ([FlambdaTypeRenameSpec.rename_type]);
   - in what the environment knows of its names
     ([Cached_level.names_to_types]), each name and its type; the
     binding time and the name mode of a name stay with it;
   - the aliases, by the action of FlambdaEnvAliasesRenamingSpec.v
     ([rename_aliases]).

   The free variables of an environment are every variable written in
   it, also in a binding that is shadowed. A typing environment is the
   context of a term, and it records the identity of each variable
   that its levels define: those in scope in the term, and also those
   that no term may mention, which are the variables of the name modes
   [In_types] and [Phantom] and the variables bound before
   [min_binding_time], which are out of scope. All of them are free in
   the environment: the action renames them and abstracts none. They
   are not bound by it. (Where a level is taken out of
   an environment and its variables are to be made anew, as for the
   levels that a join is given, the level with what it scopes over is
   a name abstraction; that is not stated here.) So the equality of the
   two instances is that of Rocq, as for types and for the aliases.

   The statements:
   - the renamings act on levels and on environments as a group, two
     renamings that rename the free variables alike rename alike, and
     one that fixes them changes nothing; the free variables of what is
     renamed are the renamed free variables. So a level and an
     environment are things that contain names, with the laws of the
     interface ([level_names_nominal_statement],
     [typing_env_names_nominal_statement]).

   Nothing is trusted here. The proofs are in FlambdaEnvRenameProofs.v,
   which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaSemanticsSpec FlambdaNominalSpec FlambdaAlphaSpec
  FlambdaNameAbstractionSpec FlambdaNominalInstancesSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesRenamingSpec
  FlambdaTypingEnv FlambdaTypeRenameSpec FlambdaTypeNominalSpec.
Import ListNotations.
Import Nominal.

(* ======================================================================== *)
(* The action                                                               *)
(* ======================================================================== *)

(* A level: the variables it defines, in the map of their kinds and in
   the lists by binding time, and its equations. *)
Definition rename_level (r : renaming) (level : Typing_env_level.t)
    : Typing_env_level.t :=
  Typing_env_level.create
    (Keyed.map_keys (rename_variable r) (Typing_env_level.defined_vars level))
    (Keyed.map_values (map (rename_variable r))
       (Typing_env_level.binding_times level))
    (Keyed.map_bindings (rename_name r) (rename_type r)
       (Typing_env_level.equations level)).

(* What the environment knows of a name: the type is renamed, and the
   binding time and the name mode are kept. *)
Definition rename_binding (r : renaming)
    (binding : flambda_type * Binding_time.With_name_mode.t)
    : flambda_type * Binding_time.With_name_mode.t :=
  (rename_type r (fst binding), snd binding).

Definition rename_cached_level (r : renaming) (cached : Cached_level.t)
    : Cached_level.t :=
  {| Cached_level.names_to_types :=
       Keyed.map_bindings (rename_name r) (rename_binding r)
         (Cached_level.names_to_types cached);
     Cached_level.aliases := rename_aliases r (Cached_level.aliases cached) |}.

Definition rename_one_level (r : renaming)
    (one_level : Typing_env.One_level.t) : Typing_env.One_level.t :=
  Typing_env.One_level.create (Typing_env.One_level.scope one_level)
    (rename_level r (Typing_env.One_level.level one_level)).

Definition rename_typing_env (r : renaming) (tenv : Typing_env.t)
    : Typing_env.t :=
  {| Typing_env.defined_symbols := Typing_env.defined_symbols tenv;
     Typing_env.prev_levels :=
       map (rename_one_level r) (Typing_env.prev_levels tenv);
     Typing_env.current_level :=
       rename_one_level r (Typing_env.current_level tenv);
     Typing_env.just_after_level :=
       rename_cached_level r (Typing_env.just_after_level tenv);
     Typing_env.next_binding_time := Typing_env.next_binding_time tenv;
     Typing_env.min_binding_time := Typing_env.min_binding_time tenv;
     Typing_env.is_bottom := Typing_env.is_bottom tenv |}.

(* ======================================================================== *)
(* Free variables                                                           *)
(* ======================================================================== *)

(* The variables written in a level. A variable may be listed more than
   once, as for a type (FlambdaTypeGrammar.free_variables). *)
Definition level_free_variables (level : Typing_env_level.t)
    : list variable :=
  map fst (Typing_env_level.defined_vars level)
  ++ flat_map snd (Typing_env_level.binding_times level)
  ++ flat_map
       (fun equation =>
          free_variables_of_name (fst equation)
          ++ free_variables (snd equation))
       (Typing_env_level.equations level).

Definition cached_level_free_variables (cached : Cached_level.t)
    : list variable :=
  flat_map
    (fun binding =>
       free_variables_of_name (fst binding)
       ++ free_variables (fst (snd binding)))
    (Cached_level.names_to_types cached)
  ++ aliases_free_variables (Cached_level.aliases cached).

Definition typing_env_free_variables (tenv : Typing_env.t) : list variable :=
  flat_map
    (fun one_level =>
       level_free_variables (Typing_env.One_level.level one_level))
    (Typing_env.prev_levels tenv)
  ++ level_free_variables
       (Typing_env.One_level.level (Typing_env.current_level tenv))
  ++ cached_level_free_variables (Typing_env.just_after_level tenv).

(* ======================================================================== *)
(* The renamings act on levels and on environments                          *)
(* ======================================================================== *)

Definition rename_level_identity_statement : Prop :=
  ∀ level : Typing_env_level.t, rename_level identity_renaming level = level.

Definition rename_level_compose_statement : Prop :=
  ∀ (second first : renaming) (level : Typing_env_level.t),
    rename_level (compose_renaming second first) level
    = rename_level second (rename_level first level).

(* Two renamings that rename the free variables of a level alike rename
   the level alike. *)
Definition rename_level_extensional_statement : Prop :=
  ∀ (r r' : renaming) (level : Typing_env_level.t),
    (∀ x : variable,
      x ∈ level_free_variables level ->
      rename_variable r x = rename_variable r' x) ->
    rename_level r level = rename_level r' level.

(* So a renaming that fixes the free variables of a level leaves it as
   it is. *)
Definition rename_level_fixes_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t),
    (∀ x : variable, x ∈ level_free_variables level -> rename_variable r x = x)
    ->
    rename_level r level = level.

Definition rename_level_inverse_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t),
    rename_level (inverse_renaming r) (rename_level r level) = level.

Definition free_variables_rename_level_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t),
    level_free_variables (rename_level r level)
    = map (rename_variable r) (level_free_variables level).

(* The same of an environment. *)
Definition rename_typing_env_identity_statement : Prop :=
  ∀ tenv : Typing_env.t, rename_typing_env identity_renaming tenv = tenv.

Definition rename_typing_env_compose_statement : Prop :=
  ∀ (second first : renaming) (tenv : Typing_env.t),
    rename_typing_env (compose_renaming second first) tenv
    = rename_typing_env second (rename_typing_env first tenv).

Definition rename_typing_env_extensional_statement : Prop :=
  ∀ (r r' : renaming) (tenv : Typing_env.t),
    (∀ x : variable,
      x ∈ typing_env_free_variables tenv ->
      rename_variable r x = rename_variable r' x) ->
    rename_typing_env r tenv = rename_typing_env r' tenv.

Definition rename_typing_env_fixes_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t),
    (∀ x : variable,
      x ∈ typing_env_free_variables tenv -> rename_variable r x = x) ->
    rename_typing_env r tenv = tenv.

Definition rename_typing_env_inverse_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t),
    rename_typing_env (inverse_renaming r) (rename_typing_env r tenv) = tenv.

Definition free_variables_rename_typing_env_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t),
    typing_env_free_variables (rename_typing_env r tenv)
    = map (rename_variable r) (typing_env_free_variables tenv).

(* ======================================================================== *)
(* Levels and environments are things that contain names                    *)
(* ======================================================================== *)

(* [Contains_names.S] at the sort of variables: a permutation of the
   variables acts by the renaming that permutes no continuation
   (FlambdaNominalInstancesSpec.variables_renaming), the free names are the
   free variables, and the equality is that of Rocq. *)
Definition level_names : contains_names Typing_env_level.t :=
  Contains_names (fun p level => rename_level (variables_renaming p) level)
    level_free_variables eq.

Definition typing_env_names : contains_names Typing_env.t :=
  Contains_names (fun p tenv => rename_typing_env (variables_renaming p) tenv)
    typing_env_free_variables eq.

Definition level_names_nominal_statement : Prop := nominal level_names.

Definition typing_env_names_nominal_statement : Prop :=
  nominal typing_env_names.
