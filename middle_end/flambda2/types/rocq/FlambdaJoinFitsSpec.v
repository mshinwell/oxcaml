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


(* That what the n-way join adds to the target fits it: the variables,
   the kinds of the aliases and the kinds of the names of equations
   of the types that the last phase of the join makes.

   This file is to be reviewed: the statements. The proofs are in
   FlambdaJoinFitsProofs.v, which needs no review.

   The meet's environment adds an extension only if it fits
   ([env_extension_fits], FlambdaMeetSpec.v): the environment knows
   the names of its equations and the variables of their types, the
   aliases of those types and the names of the equations inside them
   are of the kinds at which the types have them, and the types are
   well formed. The types of the two extensions that the join adds
   are made by [project_variables_out] (FlambdaTypeProject.v) from
   the types of the state. What is here so far is about that
   function alone, for any variables to remove and any types put for
   them:
   - the variables ([project_variables_out_scope_statement]): if the
     variables of the type that are not removed have a property, and
     so have the variables of the types put for those removed, then
     the variables of the type answered have it. (The property is to
     be "a variable of the target".)
   - the aliases ([project_variables_out_kinded_statement]): the same
     of the aliases with their kinds ([aliases_with_kinds]), where an
     alias of a variable that is removed is supposed to be at the
     kind of the type put for it. (An alias is replaced by that type
     only if the kinds agree; but a variable that holds the result of
     [Is_int], [Get_tag] or [Is_null] is replaced by the variable
     that the type put for it is an alias of, whatever the kind of
     that type.)
   - the names of the equations inside the type
     ([project_variables_out_equations_kinded_statement]): the same
     of [equation_names_with_kinds]. An equation on a variable that
     is removed is dropped, so nothing is supposed of it.
   - the kind ([project_variables_out_kind_statement]): the type
     answered is of the kind of the type given.
   - well-formedness ([project_variables_out_well_formed_statement]):
     the type answered is well formed ([type_well_formed],
     FlambdaTypeWellFormedSpec.v) if the type given is and the types
     put for the variables removed are.
   Each but the kind is stated of a type and of an environment
   extension.

   And about the function that the last phase gives the projection
   for the types to put ([Join_env.expand_variable], FlambdaJoinEnv.v:
   the type kept for a variable that is removed, in which the
   variables that are removed are replaced in turn): the variables of
   a type that it answers have a property if those of the types kept
   that are not removed have it ([expand_variable_scope_statement]);
   and the type is well formed if the types kept are
   ([expand_variable_well_formed_statement]).

   Not here yet: the kinds of what [Join_env.expand_variable] answers;
   and these properties of the equations that the state of a join
   holds, through the phases of the join, which is what would give
   them of the two extensions. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeWellFormedSpec FlambdaTypeProject FlambdaTypingEnv FlambdaJoinEnv.
Import ListNotations.

(* The type answered is of the kind of the type given. *)
Definition project_variables_out_kind_statement : Prop :=
  ∀ (to_project : list variable) (expand : variable -> option flambda_type)
    (t t' : flambda_type),
    project_variables_out to_project expand t = Some t' -> kind t' = kind t.

(* The variables. *)
Definition project_variables_out_scope_statement : Prop :=
  ∀ (to_project : list variable) (expand : variable -> option flambda_type)
    (in_target : variable -> Prop),
    (∀ (e : variable) (ty : flambda_type) (x : variable),
       among e to_project = true ->
       expand e = Some ty ->
       x ∈ free_variables ty ->
       in_target x) ->
    (∀ t t' : flambda_type,
       project_variables_out to_project expand t = Some t' ->
       (∀ x : variable,
          x ∈ free_variables t -> among x to_project = false -> in_target x)
       ->
       ∀ x : variable, x ∈ free_variables t' -> in_target x)
    ∧ ∀ extension extension' : env_extension,
        project_env_extension to_project expand extension = Some extension'
        ->
        (∀ x : variable,
           x ∈ free_variables_of_env_extension extension ->
           among x to_project = false ->
           in_target x) ->
        ∀ x : variable,
          x ∈ free_variables_of_env_extension extension' -> in_target x.

(* What is supposed of an alias of the type given, at a kind: if it is
   of a variable that is removed, the type put for the variable is of
   that kind; otherwise it has the property. *)
Definition alias_before (to_project : list variable)
    (expand : variable -> option flambda_type)
    (of_kind : simple -> flambda_kind -> Prop)
    (alias : simple * flambda_kind) : Prop :=
  match fst alias with
  | Var e =>
    if among e to_project
    then ∀ ty : flambda_type, expand e = Some ty -> kind ty = snd alias
    else of_kind (fst alias) (snd alias)
  | Symbol _ | Const _ => of_kind (fst alias) (snd alias)
  end.

(* The aliases, with their kinds. *)
Definition project_variables_out_kinded_statement : Prop :=
  ∀ (to_project : list variable) (expand : variable -> option flambda_type)
    (of_kind : simple -> flambda_kind -> Prop),
    (∀ (e : variable) (ty : flambda_type) (s : simple) (k : flambda_kind),
       among e to_project = true ->
       expand e = Some ty ->
       (s, k) ∈ aliases_with_kinds ty ->
       of_kind s k) ->
    (∀ t t' : flambda_type,
       project_variables_out to_project expand t = Some t' ->
       (∀ alias : simple * flambda_kind,
          alias ∈ aliases_with_kinds t ->
          alias_before to_project expand of_kind alias) ->
       ∀ (s : simple) (k : flambda_kind),
         (s, k) ∈ aliases_with_kinds t' -> of_kind s k)
    ∧ ∀ extension extension' : env_extension,
        project_env_extension to_project expand extension = Some extension'
        ->
        (∀ alias : simple * flambda_kind,
           alias ∈ aliases_of_env_extension extension ->
           alias_before to_project expand of_kind alias) ->
        ∀ (s : simple) (k : flambda_kind),
          (s, k) ∈ aliases_of_env_extension extension' -> of_kind s k.

(* A name that is not a variable that is removed. *)
Definition name_kept (to_project : list variable) (n : name) : Prop :=
  match n with
  | Name_var e => among e to_project = false
  | Name_symbol _ => True
  end.

(* The names of the equations inside the type, with their kinds. *)
Definition project_variables_out_equations_kinded_statement : Prop :=
  ∀ (to_project : list variable) (expand : variable -> option flambda_type)
    (of_kind : name -> flambda_kind -> Prop),
    (∀ (e : variable) (ty : flambda_type) (n : name) (k : flambda_kind),
       among e to_project = true ->
       expand e = Some ty ->
       (n, k) ∈ equation_names_with_kinds ty ->
       of_kind n k) ->
    (∀ t t' : flambda_type,
       project_variables_out to_project expand t = Some t' ->
       (∀ (n : name) (k : flambda_kind),
          (n, k) ∈ equation_names_with_kinds t ->
          name_kept to_project n ->
          of_kind n k) ->
       ∀ (n : name) (k : flambda_kind),
         (n, k) ∈ equation_names_with_kinds t' -> of_kind n k)
    ∧ ∀ extension extension' : env_extension,
        project_env_extension to_project expand extension = Some extension'
        ->
        (∀ (n : name) (k : flambda_kind),
           (n, k) ∈ equation_names_of_env_extension extension ->
           name_kept to_project n ->
           of_kind n k) ->
        ∀ (n : name) (k : flambda_kind),
          (n, k) ∈ equation_names_of_env_extension extension' -> of_kind n k.

(* Well-formedness. *)
Definition project_variables_out_well_formed_statement : Prop :=
  ∀ (to_project : list variable) (expand : variable -> option flambda_type),
    (∀ (e : variable) (ty : flambda_type),
       among e to_project = true ->
       expand e = Some ty ->
       type_well_formed ty = true) ->
    (∀ t t' : flambda_type,
       project_variables_out to_project expand t = Some t' ->
       type_well_formed t = true ->
       type_well_formed t' = true)
    ∧ ∀ extension extension' : env_extension,
        project_env_extension to_project expand extension = Some extension'
        ->
        env_extension_well_formed extension = true ->
        env_extension_well_formed extension' = true.

(* ======================================================================== *)
(* The types put for the variables that the last phase removes              *)
(* ======================================================================== *)

(* The variables of a type that [Join_env.expand_variable] answers:
   they have a property if every variable of a type kept that is not
   itself removed has it. (With "is not removed" as part of the
   property: no variable that is removed is left.) *)
Definition expand_variable_scope_statement : Prop :=
  ∀ (to_expand : finite_map flambda_type) (in_target : variable -> Prop),
    (∀ (e : variable) (ty : flambda_type) (x : variable),
       lookup e to_expand = Some ty ->
       x ∈ free_variables ty ->
       among x (domain to_expand) = false ->
       in_target x) ->
    ∀ (fuel : nat) (e : variable) (ty : flambda_type) (x : variable),
      Join_env.expand_variable fuel to_expand e = Some ty ->
      x ∈ free_variables ty ->
      in_target x.

(* A type that it answers is well formed if the types kept are. *)
Definition expand_variable_well_formed_statement : Prop :=
  ∀ to_expand : finite_map flambda_type,
    (∀ (e : variable) (ty : flambda_type),
       lookup e to_expand = Some ty -> type_well_formed ty = true) ->
    ∀ (fuel : nat) (e : variable) (ty : flambda_type),
      Join_env.expand_variable fuel to_expand e = Some ty ->
      type_well_formed ty = true.
