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


(* The environment side of the n-way join of typing environments: what
   it is given and what it returns beside the joined environment.

   This file is to be reviewed line by line against
   middle_end/flambda2/types/env/join_env.ml, as FlambdaTypingEnv.v is
   against typing_env.ml. It holds definitions only, in modules that
   have the compiler's names. What the join guarantees is
   FlambdaJoinSpec.v.

   It is the first part of the transcription: the indices of the
   environments joined, the vectors of [Simple]s across them, and the
   analysis that the join returns for Simplify to read. The join itself
   ([cut_and_n_way_join0] and what it calls) is to come in this file,
   and the header will then say function by function what the model has.

   What is here, against join_env.ml:
   - [Index]: the environments joined are numbered from 0 in the order
     of the list given ([Index.fold_list]). An index is a position, not
     a name: renaming leaves it alone.
   - [Simples_in_joined_envs.t]: a [Simple] for each of some of the
     indices, as a map read with [Index.equal]. In the compiler it is
     also the key of a map ([Simples_in_joined_envs.Map]); two vectors
     are the same key when they bind the same indices to the same
     [Simple]s. [choose_a_suitable_name] is left out: the names of the
     model are numbers.
   - [Analysis.t]: the three fields of the compiler's record. The
     identifiers that Simplify gives the uses ([external_ids]) are of
     any type, as in the compiler.
   - [Analysis.simple_refined_at_join], with
     [Variable_refined_at_join.fold_values_at_uses] as the list
     [values_at_uses], and [fold_variables_created_at_join] with
     [Simples_at_join.fold_definitions_at_uses] as the list
     [variables_created_at_join]: what Simplify reads
     (simplify/join_points.ml, simplify_switch_expr.ml,
     specialization_cost.ml).

   The differences:
   - A [Simple] of the model has no coercion (the terms have no
     [Rec_info]), so the wrappers that keep a coercion beside a name
     are plain [simple]s.
   - The wrappers that tell the environment a name belongs to
     ([Variable_in_target_env], [Simple_in_one_joined_env], ...) are
     the plain types: they are a discipline of the compiler's types and
     hold no data.
   - A fold is the list of what it visits, in the order of the map that
     the model has, which is not the compiler's (the order of the
     keys). No statement depends on the order.
   - A fatal error of the compiler is [None]: in [values_at_uses] and
     [variables_created_at_join], an index with no external
     identifier.
   - [Analysis.print] is left out. [Analysis.create] comes with the
     join. *)

From Stdlib Require Import ZArith List Bool PeanoNat.
From OxCamlStdlib Require Import OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaTypingEnv.
Import ListNotations.

(* ======================================================================== *)
(* The environments joined, and vectors of [Simple]s across them            *)
(* ======================================================================== *)

(* [Index.t]: the number of one of the environments joined. *)
Module Index.

  Definition t : Type := nat.

  Definition equal (index index' : t) : bool := Nat.eqb index index'.

  (* [Index.fold_list], as the list of the elements with their indices:
     the first has index 0. *)
  Definition number {A : Type} (xs : list A) : list (t * A) :=
    combine (seq 0 (length xs)) xs.

End Index.

(* [Simples_in_joined_envs.t]: a [Simple] in each of some of the
   environments joined. *)
Module Simples_in_joined_envs.

  Definition t : Type := Keyed.finite_map Index.t simple.

  Definition find (index : Index.t) (simples : t) : option simple :=
    Keyed.lookup Index.equal index simples.

End Simples_in_joined_envs.

(* ======================================================================== *)
(* The analysis of a join                                                   *)
(* ======================================================================== *)

Module Analysis.

  (* [Join_env.Analysis.t]. [definitions_in_joined_envs]: for some
     variables of the joined environment, the canonical [Simple] that
     each stands for in the environments joined.
     [canonical_definitions_at_normal_mode]: the same for those of the
     variables that stand, in every environment where they stand for
     something, for a [Simple] that may occur in terms there.
     [external_ids]: the identifier that the caller gave each
     environment joined that is not bottom. *)
  Record t (A : Type) : Type := {
    definitions_in_joined_envs :
      finite_map (Simples_in_joined_envs.t * flambda_kind);
    canonical_definitions_at_normal_mode :
      finite_map (Simples_in_joined_envs.t * flambda_kind);
    external_ids : Keyed.finite_map Index.t A
  }.

  Arguments definitions_in_joined_envs {A} _.
  Arguments canonical_definitions_at_normal_mode {A} _.
  Arguments external_ids {A} _.

  (* The analysis that says nothing: that of a join of no environment. *)
  Definition empty {A : Type} : t A :=
    {| definitions_in_joined_envs := [];
       canonical_definitions_at_normal_mode := [];
       external_ids := [] |}.

  (* The values that a variable has at the uses, as
     [Variable_refined_at_join.fold_values_at_uses] gives them: a
     constant where the variable stands for one, and unknown where it
     stands for a name. [None] is a fatal error of the compiler: an
     index with no identifier. *)
  Definition value_at_use (simple : simple) : Or_unknown.t const :=
    match simple with
    | Const const => Or_unknown.Known const
    | Var _ | Symbol _ => Or_unknown.Unknown
    end.

  Fixpoint values_at_uses {A : Type}
      (external_ids : Keyed.finite_map Index.t A)
      (canonicals_in_joined_envs : Simples_in_joined_envs.t)
      : option (list (A * Or_unknown.t const)) :=
    match canonicals_in_joined_envs with
    | [] => Some []
    | (index, simple) :: canonicals_in_joined_envs =>
      let* external_id := Keyed.lookup Index.equal index external_ids in
      let* values := values_at_uses external_ids canonicals_in_joined_envs in
      Some ((external_id, value_at_use simple) :: values)
    end.

  (* [Join_env.Analysis.simple_refined_at_join]. *)
  Inductive simple_refined_at_join : Type :=
    | Not_refined_at_join
    | Invariant_in_all_uses (simple : simple)
    | Variable_refined_at_these_uses
        (canonicals_in_joined_envs : Simples_in_joined_envs.t)
        (kind : flambda_kind).

  (* What the join did to a [Simple] of the environment [env], which is
     the joined environment or one made from it. *)
  Definition simple_refined_at_join_of {A : Type} (analysis : t A)
      (env : Typing_env.t) (simple : simple) : simple_refined_at_join :=
    match Typing_env.get_canonical_simple_ignoring_name_mode env simple with
    | Const const => Invariant_in_all_uses (Const const)
    | Symbol symbol => Invariant_in_all_uses (Symbol symbol)
    | Var var =>
      match lookup var (definitions_in_joined_envs analysis) with
      | None => Not_refined_at_join
      | Some (canonicals_in_joined_envs, kind) =>
        Variable_refined_at_these_uses canonicals_in_joined_envs kind
      end
    end.

  (* The [Simple] that may be given, at each use, for a variable that
     the join made: [Simples_at_join.fold_definitions_at_uses]. [None]
     as for [values_at_uses]. *)
  Fixpoint definitions_at_uses {A : Type}
      (external_ids : Keyed.finite_map Index.t A)
      (canonicals_in_joined_envs : Simples_in_joined_envs.t)
      : option (list (A * simple)) :=
    match canonicals_in_joined_envs with
    | [] => Some []
    | (index, simple) :: canonicals_in_joined_envs =>
      let* external_id := Keyed.lookup Index.equal index external_ids in
      let* definitions :=
        definitions_at_uses external_ids canonicals_in_joined_envs
      in
      Some ((external_id, simple) :: definitions)
    end.

  (* [Join_env.Analysis.fold_variables_created_at_join]: the variables
     that have a definition at the normal name mode, each with that
     definition and its kind. *)
  Definition variables_created_at_join {A : Type} (analysis : t A)
      : list (variable * Simples_in_joined_envs.t * flambda_kind) :=
    map
      (fun binding =>
         (fst binding, fst (snd binding), snd (snd binding)))
      (compact (canonical_definitions_at_normal_mode analysis)).

End Analysis.
