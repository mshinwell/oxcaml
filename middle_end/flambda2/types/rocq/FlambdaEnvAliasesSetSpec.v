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

(* Sets of aliases, and making a name the alias of every element of a
   set.

   This file is to be reviewed, with the functions of [Aliases.Alias_set]
   and [Aliases.add_alias_set] in FlambdaEnvAliases.v, against
   [Alias_set] and [add_alias_set] in
   middle_end/flambda2/types/env/aliases.ml. The functions are read
   against the OCaml; what they answer is stated here.

   A set of aliases ([Aliases.Alias_set.t]) is the aliases of one simple:
   at most one constant, and names. [Aliases.get_aliases] makes one
   (FlambdaEnvAliasesSpec.v, [get_aliases_statement]). The binary join
   and two rewrites of the simplifier work on such sets: they intersect
   the sets that the environments of the uses give for a name, keep the
   elements that the environment at the join knows, and either choose
   one element ([find_best], [get_singleton]) or record all of them as
   aliases of the name ([Aliases.add_alias_set]). The n-way join uses
   none of this.

   What is stated.
   - Of each function on sets, which simples the answer has
     ([alias_set_has]): [singleton], [empty], [is_empty], [inter],
     [filter].
   - [find_best] answers an element of the set, and one that no element
     is better than: a constant is better than a symbol, which is
     better than a variable ([alias_rank]). It has no answer only for
     the empty set.
   - [get_singleton] answers when the set has exactly one element.
   - [choose_opt] answers an element of the set. It has no answer for
     the empty set, and none for a set that has a constant and names
     ([choose_opt_none_statement]; discrepancy T3-4: nothing in the
     compiler calls it).
   - [Aliases.add_alias_set]: the classes afterwards are those before
     with the class of the name and the classes of the elements of the
     set merged into one, and nothing else ([add_alias_set_aliased]);
     respect is kept when the elements have the value of the name;
     consistency and the name modes recorded are kept; there is no
     fatal error when some environment respects the structure and
     gives the elements the value of the name; the names spoken of
     afterwards are among those before, the name and the names of the
     set.
   - The functions on sets and [Aliases.add_alias_set] commute with
     renaming, with no premise (the renamings are in
     FlambdaEnvAliasesRenamingSpec.v); [filter] with the test renamed.

   Differences from the OCaml, all deliberate.
   - The names of a set are a list where the OCaml has a map from names
     to coercions; there are no coercions (FlambdaEnvAliasesSpec.v,
     "Differences"). A name may be in the list twice; nothing depends
     on it.
   - Where the OCaml chooses among several names by the order on names
     ([find_best] among the symbols, or among the variables;
     [choose_opt]), the model takes the first of the list. The
     statements say only what holds of either choice (discrepancy
     T3-7).
   - [Aliases.add_alias_set] goes through the names of the set in the
     order of the list, the OCaml in the order of names. The classes
     afterwards do not depend on the order; the structure as it is
     written may.
   - The fatal error of the OCaml's [add_alias_set] on two different
     constants ("Discovered Bottom during alias join") is [None], as
     are those of [Aliases.add0].
   - That the canonical element of the merged class is the earliest is
     not stated: [Aliases.add] keeps the order only for two elements of
     which one is earlier than the other
     (FlambdaEnvAliasesSpec.v, [add_earliest_statement]).

   The proofs are in FlambdaEnvAliasesSetProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaNominalSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeRenameSpec FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaEnvAliasesRenamingSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The functions on sets                                                    *)
(* ======================================================================== *)

Definition singleton_has_statement : Prop :=
  ∀ e e' : simple,
    alias_set_has (Aliases.Alias_set.singleton e) e' <-> e' = e.

Definition empty_has_statement : Prop :=
  ∀ e : simple, ~ alias_set_has Aliases.Alias_set.empty e.

Definition is_empty_has_statement : Prop :=
  ∀ set : Aliases.Alias_set.t,
    Aliases.Alias_set.is_empty set = true
    <-> (∀ e : simple, ~ alias_set_has set e).

Definition inter_has_statement : Prop :=
  ∀ (set set' : Aliases.Alias_set.t) (e : simple),
    alias_set_has (Aliases.Alias_set.inter set set') e
    <-> alias_set_has set e ∧ alias_set_has set' e.

Definition filter_has_statement : Prop :=
  ∀ (set : Aliases.Alias_set.t) (f : simple -> bool) (e : simple),
    alias_set_has (Aliases.Alias_set.filter set f) e
    <-> alias_set_has set e ∧ f e = true.

(* ======================================================================== *)
(* Choosing an element                                                      *)
(* ======================================================================== *)

(* Which alias is better: a constant, then a symbol, then a variable.
   The lesser the better. *)
Definition alias_rank (e : simple) : Z :=
  match e with
  | Const _ => 0
  | Symbol _ => 1
  | Var _ => 2
  end.

Definition find_best_has_statement : Prop :=
  ∀ (set : Aliases.Alias_set.t) (e : simple),
    Aliases.Alias_set.find_best set = Some e -> alias_set_has set e.

Definition find_best_best_statement : Prop :=
  ∀ (set : Aliases.Alias_set.t) (e e' : simple),
    Aliases.Alias_set.find_best set = Some e ->
    alias_set_has set e' ->
    alias_rank e <= alias_rank e'.

Definition find_best_none_statement : Prop :=
  ∀ set : Aliases.Alias_set.t,
    Aliases.Alias_set.find_best set = None
    <-> Aliases.Alias_set.is_empty set = true.

(* The one element of a set that has exactly one. *)
Definition get_singleton_statement : Prop :=
  ∀ (set : Aliases.Alias_set.t) (e : simple),
    Aliases.Alias_set.get_singleton set = Some e
    <-> (∀ e' : simple, alias_set_has set e' <-> e' = e).

Definition choose_opt_has_statement : Prop :=
  ∀ (set : Aliases.Alias_set.t) (e : simple),
    Aliases.Alias_set.choose_opt set = Some e -> alias_set_has set e.

(* [choose_opt] has no answer for the empty set, and none for a set that
   has a constant and a name, though that set is not empty. The OCaml is
   the same (discrepancy T3-4). *)
Definition choose_opt_none_statement : Prop :=
  ∀ set : Aliases.Alias_set.t,
    Aliases.Alias_set.choose_opt set = None
    <-> Aliases.Alias_set.is_empty set = true
        ∨ (∃ (c : const) (n : name),
            alias_set_has set (Const c)
            ∧ alias_set_has set (simple_of_name n)).

(* ======================================================================== *)
(* Adding a set of aliases                                                  *)
(* ======================================================================== *)

(* A simple that [Aliases.add_alias_set t name aliases] puts in the
   class of [name]: one that was in it, or one that was in the class of
   an element of the set. *)
Definition merged_by_set (t : Aliases.t) (name : name)
    (aliases : Aliases.Alias_set.t) (e : simple) : Prop :=
  aliased t e (simple_of_name name)
  ∨ (∃ e' : simple, alias_set_has aliases e' ∧ aliased t e e').

(* The classes afterwards: two simples are known to be equal exactly
   when they were, or both are put in the class of the name. So the
   name and the elements of the set are in one class, and no other
   class has changed. *)
Definition add_alias_set_aliased_statement : Prop :=
  ∀ (A : Type) (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (name : name) (aliases : Aliases.Alias_set.t)
    (t' : Aliases.t) (e e' : simple),
    aliases_consistent t ->
    Aliases.add_alias_set binding_time_resolver binding_times_and_modes t
      name aliases
    = Some t' ->
    (aliased t' e e'
     <-> aliased t e e'
         ∨ (merged_by_set t name aliases e ∧ merged_by_set t name aliases e')).

(* Respect is kept when every element of the set has the value of the
   name. Nothing is asked of the structure. *)
Definition add_alias_set_respected_statement : Prop :=
  ∀ (A : Type) (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (name : name) (aliases : Aliases.Alias_set.t)
    (t' : Aliases.t) (vars : env),
    Aliases.add_alias_set binding_time_resolver binding_times_and_modes t
      name aliases
    = Some t' ->
    aliases_respected t vars ->
    (∀ e : simple,
      alias_set_has aliases e ->
      eval_simple vars e = value_of_name vars name) ->
    aliases_respected t' vars.

Definition add_alias_set_consistent_statement : Prop :=
  ∀ (A : Type) (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (name : name) (aliases : Aliases.Alias_set.t)
    (t' : Aliases.t),
    aliases_consistent t ->
    Aliases.add_alias_set binding_time_resolver binding_times_and_modes t
      name aliases
    = Some t' ->
    aliases_consistent t'.

Definition add_alias_set_name_modes_recorded_statement : Prop :=
  ∀ (A : Type) (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (name : name) (aliases : Aliases.Alias_set.t)
    (t' : Aliases.t),
    name_modes_recorded binding_times_and_modes t ->
    Aliases.add_alias_set binding_time_resolver binding_times_and_modes t
      name aliases
    = Some t' ->
    name_modes_recorded binding_times_and_modes t'.

(* There is no fatal error when the structure is consistent and some
   environment respects it and gives every element of the set the value
   of the name: then no two different constants meet. As for
   [add_defined_statement], this is about the model, whose resolver is
   total. *)
Definition add_alias_set_defined_statement : Prop :=
  ∀ (A : Type) (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (name : name) (aliases : Aliases.Alias_set.t)
    (vars : env),
    aliases_consistent t ->
    aliases_respected t vars ->
    (∀ e : simple,
      alias_set_has aliases e ->
      eval_simple vars e = value_of_name vars name) ->
    Aliases.add_alias_set binding_time_resolver binding_times_and_modes t
      name aliases
    <> None.

(* The names that the structure speaks of afterwards are among those it
   spoke of, the name and the names of the set. *)
Definition add_alias_set_mentioned_statement : Prop :=
  ∀ (A : Type) (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (name : name) (aliases : Aliases.Alias_set.t)
    (t' : Aliases.t) (n : FlambdaTypeGrammar.name),
    Aliases.add_alias_set binding_time_resolver binding_times_and_modes t
      name aliases
    = Some t' ->
    aliases_mention t' n ->
    aliases_mention t n ∨ n = name ∨ alias_set_has aliases (simple_of_name n).

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

(* The functions on sets and [Aliases.add_alias_set] commute with
   renaming. None has a premise: where a function chooses among names
   it takes the first of a list, which renaming keeps. *)

Definition rename_alias_set_has_statement : Prop :=
  ∀ (r : renaming) (set : Aliases.Alias_set.t) (e : simple),
    alias_set_has (rename_alias_set r set) (rename_simple r e)
    <-> alias_set_has set e.

Definition rename_singleton_statement : Prop :=
  ∀ (r : renaming) (e : simple),
    Aliases.Alias_set.singleton (rename_simple r e)
    = rename_alias_set r (Aliases.Alias_set.singleton e).

Definition rename_is_empty_statement : Prop :=
  ∀ (r : renaming) (set : Aliases.Alias_set.t),
    Aliases.Alias_set.is_empty (rename_alias_set r set)
    = Aliases.Alias_set.is_empty set.

Definition rename_inter_statement : Prop :=
  ∀ (r : renaming) (set set' : Aliases.Alias_set.t),
    Aliases.Alias_set.inter (rename_alias_set r set)
      (rename_alias_set r set')
    = rename_alias_set r (Aliases.Alias_set.inter set set').

(* [filter] of the renamed set with a test is the renamed [filter] of
   the set with the test of the renamed simple. *)
Definition rename_filter_statement : Prop :=
  ∀ (r : renaming) (set : Aliases.Alias_set.t) (f : simple -> bool),
    Aliases.Alias_set.filter (rename_alias_set r set) f
    = rename_alias_set r
        (Aliases.Alias_set.filter set (fun e => f (rename_simple r e))).

Definition rename_find_best_statement : Prop :=
  ∀ (r : renaming) (set : Aliases.Alias_set.t),
    Aliases.Alias_set.find_best (rename_alias_set r set)
    = option_map (rename_simple r) (Aliases.Alias_set.find_best set).

Definition rename_get_singleton_statement : Prop :=
  ∀ (r : renaming) (set : Aliases.Alias_set.t),
    Aliases.Alias_set.get_singleton (rename_alias_set r set)
    = option_map (rename_simple r) (Aliases.Alias_set.get_singleton set).

Definition rename_choose_opt_statement : Prop :=
  ∀ (r : renaming) (set : Aliases.Alias_set.t),
    Aliases.Alias_set.choose_opt (rename_alias_set r set)
    = option_map (rename_simple r) (Aliases.Alias_set.choose_opt set).

Definition rename_add_alias_set_statement : Prop :=
  ∀ (A : Type) (r : renaming)
    (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (name : name) (aliases : Aliases.Alias_set.t),
    Aliases.add_alias_set (rename_resolver r binding_time_resolver)
      (rename_binding_times r binding_times_and_modes) (rename_aliases r t)
      (rename_name r name) (rename_alias_set r aliases)
    = option_map (rename_aliases r)
        (Aliases.add_alias_set binding_time_resolver binding_times_and_modes
           t name aliases).
