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
     [typing_env_names_nominal_statement]);
   - the functions of a level ([Typing_env_level]) and of what the
     environment knows of its names ([Cached_level]) commute with
     renaming;
   - so does what an environment is asked ([Typing_env]): [find] and
     the functions beside it, the binding time and the name mode of a
     name, [mem], and the canonical element of a [Simple] at a name
     mode.

   Each statement about a function is an equation and holds of every
   level or environment: nothing is asked of it, its invariant
   included. One has a premise, on an argument that is a function
   ([Typing_env_level.fold_on_defined_vars]). No function here makes a
   name, and none goes by the order of names. Where the order in which
   names were bound matters (the variables of a level in order, the
   choice of a canonical element), it
   is read from binding times, which a name keeps when it is renamed;
   and a tie is settled by the order of a list of the model, which the
   action keeps. The compiler settles such a tie by an order on names
   (FlambdaEnvAliasesSpec.v, "Differences"; FlambdaTypingEnv.v, on
   [fold_on_defined_vars]).

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

(* ======================================================================== *)
(* The functions of a level                                                 *)
(* ======================================================================== *)

Definition level_empty_equivariant_statement : Prop :=
  ∀ r : renaming,
    rename_level r Typing_env_level.empty = Typing_env_level.empty.

Definition level_defined_variables_equivariant_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t),
    Typing_env_level.defined_variables (rename_level r level)
    = map (rename_variable r) (Typing_env_level.defined_variables level).

Definition level_defined_names_equivariant_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t),
    Typing_env_level.defined_names (rename_level r level)
    = map (rename_name r) (Typing_env_level.defined_names level).

Definition level_find_kind_equivariant_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t) (var : variable),
    Typing_env_level.find_kind (rename_level r level) (rename_variable r var)
    = Typing_env_level.find_kind level var.

Definition level_variable_is_defined_equivariant_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t) (var : variable),
    Typing_env_level.variable_is_defined (rename_level r level)
      (rename_variable r var)
    = Typing_env_level.variable_is_defined level var.

Definition level_is_empty_equivariant_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t),
    Typing_env_level.is_empty (rename_level r level)
    = Typing_env_level.is_empty level.

Definition level_add_definition_equivariant_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t) (var : variable)
    (kind : flambda_kind) (binding_time : Binding_time.t),
    Typing_env_level.add_definition (rename_level r level)
      (rename_variable r var) kind binding_time
    = rename_level r
        (Typing_env_level.add_definition level var kind binding_time).

Definition level_add_or_replace_equation_equivariant_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t) (name : name)
    (ty : flambda_type),
    Typing_env_level.add_or_replace_equation (rename_level r level)
      (rename_name r name) (rename_type r ty)
    = rename_level r (Typing_env_level.add_or_replace_equation level name ty).

(* Where the two levels cannot be made one, the two renamed cannot. *)
Definition level_concat_equivariant_statement : Prop :=
  ∀ (r : renaming) (earlier later : Typing_env_level.t),
    Typing_env_level.concat (rename_level r earlier) (rename_level r later)
    = option_map (rename_level r) (Typing_env_level.concat earlier later).

Definition level_as_extension_equivariant_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t),
    Typing_env_level.as_extension_without_bindings (rename_level r level)
    = rename_env_extension r
        (Typing_env_level.as_extension_without_bindings level).

(* The variables of a level in the order of their binding times, and
   within one binding time in the order of the model's list: a renaming
   keeps both. *)
Definition level_variables_in_order_equivariant_statement : Prop :=
  ∀ (r : renaming) (level : Typing_env_level.t),
    Typing_env_level.variables_in_order (rename_level r level)
    = map (rename_variable r) (Typing_env_level.variables_in_order level).

(* The fold over the variables that a level defines, for a function that
   commutes with the renaming of the variable it is given and of what it
   accumulates. *)
Definition level_fold_on_defined_vars_equivariant_statement : Prop :=
  ∀ (A : Type) (r : renaming) (rename_acc : A -> A)
    (f f' : variable -> flambda_kind -> A -> A) (level : Typing_env_level.t)
    (init : A),
    (∀ (var : variable) (kind : flambda_kind) (acc : A),
      f' (rename_variable r var) kind (rename_acc acc)
      = rename_acc (f var kind acc)) ->
    Typing_env_level.fold_on_defined_vars f' (rename_level r level)
      (rename_acc init)
    = option_map rename_acc
        (Typing_env_level.fold_on_defined_vars f level init).

(* ======================================================================== *)
(* What the environment knows of its names                                  *)
(* ======================================================================== *)

Definition cached_level_empty_equivariant_statement : Prop :=
  ∀ r : renaming, rename_cached_level r Cached_level.empty = Cached_level.empty.

Definition cached_level_add_or_replace_binding_equivariant_statement : Prop :=
  ∀ (r : renaming) (cached : Cached_level.t) (name : name)
    (ty : flambda_type) (binding_time : Binding_time.t)
    (name_mode : Name_mode.t),
    Cached_level.add_or_replace_binding (rename_cached_level r cached)
      (rename_name r name) (rename_type r ty) binding_time name_mode
    = rename_cached_level r
        (Cached_level.add_or_replace_binding cached name ty binding_time
           name_mode).

Definition cached_level_replace_variable_binding_equivariant_statement : Prop :=
  ∀ (r : renaming) (cached : Cached_level.t) (var : variable)
    (ty : flambda_type),
    Cached_level.replace_variable_binding (rename_cached_level r cached)
      (rename_variable r var) (rename_type r ty)
    = rename_cached_level r
        (Cached_level.replace_variable_binding cached var ty).

Definition cached_level_with_aliases_equivariant_statement : Prop :=
  ∀ (r : renaming) (cached : Cached_level.t) (aliases : Aliases.t),
    Cached_level.with_aliases (rename_cached_level r cached)
      (rename_aliases r aliases)
    = rename_cached_level r (Cached_level.with_aliases cached aliases).

(* ======================================================================== *)
(* What an environment is asked                                             *)
(* ======================================================================== *)

Definition create_equivariant_statement : Prop :=
  ∀ r : renaming, rename_typing_env r Typing_env.create = Typing_env.create.

Definition aliases_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t),
    Typing_env.aliases (rename_typing_env r tenv)
    = rename_aliases r (Typing_env.aliases tenv).

Definition names_to_types_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t),
    Typing_env.names_to_types (rename_typing_env r tenv)
    = Keyed.map_bindings (rename_name r) (rename_binding r)
        (Typing_env.names_to_types tenv).

Definition current_scope_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t),
    Typing_env.current_scope (rename_typing_env r tenv)
    = Typing_env.current_scope tenv.

Definition name_domain_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t),
    Typing_env.name_domain (rename_typing_env r tenv)
    = map (rename_name r) (Typing_env.name_domain tenv).

(* [Typing_env.find_with_binding_time_and_mode'], the one that does not
   scope the name mode: the type found is the renamed type, with the
   same binding time and name mode; where the one is a fatal error the
   other is. *)
Definition find_unscoped_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t) (name : name)
    (kind : option flambda_kind),
    Typing_env.find_with_binding_time_and_mode' (rename_typing_env r tenv)
      (rename_name r name) kind
    = option_map (rename_binding r)
        (Typing_env.find_with_binding_time_and_mode' tenv name kind).

Definition find_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t) (name : name)
    (kind : option flambda_kind),
    Typing_env.find (rename_typing_env r tenv) (rename_name r name) kind
    = option_map (rename_type r) (Typing_env.find tenv name kind).

Definition find_with_binding_time_and_mode_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t) (name : name)
    (kind : option flambda_kind),
    Typing_env.find_with_binding_time_and_mode (rename_typing_env r tenv)
      (rename_name r name) kind
    = option_map (rename_binding r)
        (Typing_env.find_with_binding_time_and_mode tenv name kind).

(* A name keeps its binding time and its name mode. *)
Definition binding_time_and_mode_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t) (name : name),
    Typing_env.binding_time_and_mode (rename_typing_env r tenv)
      (rename_name r name)
    = Typing_env.binding_time_and_mode tenv name.

Definition binding_time_and_mode_of_simple_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t) (simple : simple),
    Typing_env.binding_time_and_mode_of_simple (rename_typing_env r tenv)
      (rename_simple r simple)
    = Typing_env.binding_time_and_mode_of_simple tenv simple.

Definition binding_time_resolver_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t) (name : name),
    Typing_env.binding_time_resolver (rename_typing_env r tenv)
      (rename_name r name)
    = Typing_env.binding_time_resolver tenv name.

Definition mem_equivariant_statement : Prop :=
  ∀ (r : renaming) (min_name_mode : option Name_mode.t) (tenv : Typing_env.t)
    (name : name),
    Typing_env.mem min_name_mode (rename_typing_env r tenv)
      (rename_name r name)
    = Typing_env.mem min_name_mode tenv name.

Definition mem_simple_equivariant_statement : Prop :=
  ∀ (r : renaming) (min_name_mode : option Name_mode.t) (tenv : Typing_env.t)
    (simple : simple),
    Typing_env.mem_simple min_name_mode (rename_typing_env r tenv)
      (rename_simple r simple)
    = Typing_env.mem_simple min_name_mode tenv simple.

Definition alias_is_bound_strictly_earlier_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t) (bound_name : name) (alias : simple),
    Typing_env.alias_is_bound_strictly_earlier (rename_typing_env r tenv)
      (rename_name r bound_name) (rename_simple r alias)
    = Typing_env.alias_is_bound_strictly_earlier tenv bound_name alias.

(* The canonical element of a renamed [Simple] is the renamed canonical
   element. The order that chooses it is by binding times, which names
   keep; where two are equally early the model takes the first of a
   list, which a renaming keeps (FlambdaEnvAliasesRenamingSpec.v). *)
Definition get_canonical_ignoring_name_mode_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t) (simple : simple),
    Typing_env.get_canonical_simple_ignoring_name_mode
      (rename_typing_env r tenv) (rename_simple r simple)
    = rename_simple r
        (Typing_env.get_canonical_simple_ignoring_name_mode tenv simple).

Definition get_canonical_simple_exn_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t)
    (min_name_mode name_mode_of_existing_simple : option Name_mode.t)
    (simple : simple),
    Typing_env.get_canonical_simple_exn (rename_typing_env r tenv)
      min_name_mode name_mode_of_existing_simple (rename_simple r simple)
    = option_map (option_map (rename_simple r))
        (Typing_env.get_canonical_simple_exn tenv min_name_mode
           name_mode_of_existing_simple simple).

Definition get_alias_then_canonical_simple_exn_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t)
    (min_name_mode name_mode_of_existing_simple : option Name_mode.t)
    (typ : flambda_type),
    Typing_env.get_alias_then_canonical_simple_exn (rename_typing_env r tenv)
      min_name_mode name_mode_of_existing_simple (rename_type r typ)
    = option_map (option_map (rename_simple r))
        (Typing_env.get_alias_then_canonical_simple_exn tenv min_name_mode
           name_mode_of_existing_simple typ).

(* The type of a [Simple] in a term, with the canonical element that the
   type is an alias to. *)
Definition type_simple_in_term_exn_equivariant_statement : Prop :=
  ∀ (r : renaming) (tenv : Typing_env.t) (min_name_mode : option Name_mode.t)
    (simple : simple),
    Typing_env.type_simple_in_term_exn (rename_typing_env r tenv)
      min_name_mode (rename_simple r simple)
    = option_map
        (option_map
           (fun typed =>
              (rename_type r (fst typed), rename_simple r (snd typed))))
        (Typing_env.type_simple_in_term_exn tenv min_name_mode simple).
