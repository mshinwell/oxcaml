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


(* What is stated of the join put together with the meet
   (FlambdaJoinMeet.v).

   This file is to be reviewed: the statements. The proofs are in
   FlambdaJoinMeetProofs.v, which needs no review.

   - The conversion between the two transcriptions of expanded types
     keeps the type and the kind ([join_expanded_to_type_statement]).
   - The parameters fixed there have what the statements about the
     join of environments suppose of parameters
     ([join_parameters_sound_statement]): [fresh_avoids],
     [parameters_type_eqb_sound], [env_extension_eqb_sound],
     [expand_const_sound].
   - The expansion of heads meets the contract that the join of types
     supposes of it ([expand_head_for_join_sound_statement]), by the
     statements of FlambdaExpandHeadSpec.v. (The reduction of heads of
     naked immediates meets its contract by
     [reduce_head_of_kind_naked_immediate_sound_statement] of
     FlambdaMeetStepsSpec.v, which is that contract.)
   - So what the join adds to the target is true
     ([model_join_true_statement]): [join_adds_true] of
     FlambdaJoinDefineSpec.v for [model_join], with the premises of
     [join_with_true_statement] on the inputs and none on a join of
     types or on parameters. It is for any choices, any depth and any
     fuel, and for the functions of [Meet_env]; as there, nothing is
     said of what those functions answer.

   - The variables that the join defines, in the environment of the
     meet ([variables_defined_kept_statement],
     [target_variables_defined_statement]): defining variables that
     the environment does not know, each once, keeps it
     ([meet_env_kept], FlambdaMeetEnvSpec.v), and the environment
     answered knows them, at their kinds, and nothing else that it
     did not know. So, for a valid state of the join whose source is
     the typing environment of the environment given: the environment
     in which the variables brought in and some of the variables made
     are defined knows exactly the variables that the target is to
     have ([in_final_target], FlambdaJoinFitsSpec.v), each at the
     kind that the state has for it.
   - So the names of the equations that the last phase adds, and the
     variables of their types, are known to the environment that the
     first extension is added to
     ([last_phase_names_known_statement]): by
     [last_phase_adds_in_scope_statement] of FlambdaJoinAddsSpec.v.
     This is about that environment, before the first extension is
     added: that the second extension is added to an environment
     that still knows them needs the first to fit entirely (kinds
     and well-formedness too), which is not shown yet.
   - And their kinds are known to it
     ([last_phase_kinds_known_statement]): the name of each equation
     is of the kind of its type there, and each alias of the type is
     of the kind at which it stands, by
     [last_phase_adds_kinded_statement] of FlambdaJoinKindsSpec.v.
     For an alias that is a symbol this has as a premise that the
     environment knows the symbol: what is shown of the state says
     of a symbol only that it stands at kind [Value].
   - So the two extensions are added as the statements about the
     meet's environment suppose (FlambdaMeetEnvSpec.v,
     [add_env_extension_keeps_statement]), and each environment on
     the way to the target is the one before, extended, and one in
     which a meet may be made ([last_phase_kept_statement]). This
     has a premise that is not shown yet of the join
     ([types_fit_otherwise]): the types of the equations are well
     formed, the names of the equations inside them are of the kinds
     of their types, and the symbols that they have aliases to are
     known. The rest of what an extension must have to fit
     ([env_extension_fits], [env_extension_kinded]) is from the
     statements above: the names and the variables are known, the
     names are of the kinds of their types, the aliases are of their
     kinds.

   Examples of what [model_join] computes are in
   FlambdaJoinMeetExamplesSpec.v. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeWellFormedSpec FlambdaTypingEnv
  FlambdaTypingEnvSpec
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvKindedSpec FlambdaJoinEnv
  FlambdaJoinSpec FlambdaJoinEnvSpec FlambdaJoinStateSpec
  FlambdaJoinDefineSpec FlambdaJoinFitsSpec FlambdaJoinAddsSpec
  FlambdaJoinKindsSpec FlambdaTypeAliasKindsSpec
  FlambdaJoinTypes FlambdaJoinTypesSpec FlambdaMeetGrammar FlambdaExpandHead
  FlambdaMeetEnv FlambdaMeet FlambdaMeetSpec FlambdaMeetStepsSpec
  FlambdaMeetEnvSpec FlambdaJoinMeet.
Import ListNotations.

(* An expanded type and its conversion are the same type, of the same
   kind. *)
Definition join_expanded_to_type_statement : Prop :=
  ∀ expanded : FlambdaExpandHead.Expanded_type.t,
    FlambdaJoinTypes.Expanded_type.to_type (join_expanded expanded)
    = FlambdaExpandHead.Expanded_type.to_type expanded
    ∧ FlambdaJoinTypes.Expanded_type.kind (join_expanded expanded)
      = FlambdaExpandHead.Expanded_type.kind expanded.

(* The parameters have what is supposed of parameters. *)
Definition join_parameters_sound_statement : Prop :=
  ∀ join_depth : nat,
    fresh_avoids (join_parameters join_depth)
    ∧ parameters_type_eqb_sound (join_parameters join_depth)
    ∧ env_extension_eqb_sound (join_parameters join_depth)
    ∧ expand_const_sound (join_parameters join_depth).

(* The expansion of heads meets the contract of FlambdaJoinTypesSpec.v,
   with the invariant of typing environments for what an environment
   must be. *)
Definition expand_head_for_join_sound_statement : Prop :=
  FlambdaJoinTypesSpec.expand_head_sound typing_env_invariant
    expand_head_for_join.

(* What the join that Simplify calls adds to the target is true. *)
Definition model_join_true_statement : Prop :=
  ∀ (A : Type) (join_choices : Join_env.choices) (meet_choices : meet_choices)
    (join_depth : nat) (fuel : fuels) (avoid : list variable)
    (inputs : join_inputs A) (target : Typing_env.t) (analysis : Analysis.t A),
    join_inputs_well_formed typing_env_invariant avoid inputs ->
    uses_kinded inputs ->
    uses_agree_with_source_on_kinds inputs ->
    (∃ (index : Index.t) (use : Typing_env.t),
       use_at inputs index use ∧ Typing_env.is_bottom use = false) ->
    model_join join_choices meet_choices join_depth fuel avoid inputs
    = Some (target, analysis) ->
    join_adds_true meet_env_functions
      (model_meet_expanded_head join_choices meet_choices join_depth fuel)
      inputs target analysis.

(* ======================================================================== *)
(* The variables that the join defines, in the environment of the meet      *)
(* ======================================================================== *)

(* Variables that the environment does not know, each once, are
   defined: the environment is kept; the one answered knows each at
   its kind, and knows a variable only if the first knew it or it is
   one of them; and the names to avoid are the same. *)
Definition variables_defined_kept_statement : Prop :=
  ∀ (vars : list (variable * flambda_kind)) (menv : Meet_env.t),
    typing_env_fits (Meet_env.typing_env menv) ->
    NoDup (map fst vars) ->
    (∀ x : variable,
       x ∈ map fst vars ->
       Typing_env.mem None (Meet_env.typing_env menv) (Name_var x) = false) ->
    meet_env_kept menv (variables_defined meet_env_functions menv vars)
    ∧ (∀ (x : variable) (kind : flambda_kind),
         (x, kind) ∈ vars ->
         simple_of_kind
           (Meet_env.typing_env
              (variables_defined meet_env_functions menv vars))
           (Var x) kind)
    ∧ (∀ x : variable,
         Typing_env.mem None
           (Meet_env.typing_env
              (variables_defined meet_env_functions menv vars))
           (Name_var x)
         = true
         <-> Typing_env.mem None (Meet_env.typing_env menv) (Name_var x) = true
             ∨ x ∈ map fst vars)
    ∧ Meet_env.names_to_avoid (variables_defined meet_env_functions menv vars)
      = Meet_env.names_to_avoid menv.

(* For a valid state of the join whose source is the typing
   environment of the environment given, and variables that the join
   has made, each once: the environment in which the variables
   brought in and those are defined is kept, knows exactly the
   variables that the target is to have, and has each at the kind
   that the state has for it. *)
Definition target_variables_defined_statement : Prop :=
  ∀ (s : Join_env.t) (menv : Meet_env.t)
    (kept : list (variable * flambda_kind)),
    state_valid s ->
    Meet_env.typing_env menv = Join_env.source_env s ->
    typing_env_fits (Meet_env.typing_env menv) ->
    (∀ binding : variable * flambda_kind,
       binding ∈ kept ->
       binding
       ∈ Bindings_in_target_env.existential_variables_in_order
           (Join_env.bindings s)) ->
    NoDup (map fst kept) ->
    let menv' :=
      variables_defined meet_env_functions menv
        (Bindings_in_target_env.imported_variables_in_order
           (Join_env.bindings s)
         ++ kept)
    in
    meet_env_kept menv menv'
    ∧ (∀ x : variable,
         in_final_target s kept x
         <-> Typing_env.mem None (Meet_env.typing_env menv') (Name_var x)
             = true)
    ∧ (∀ (x : variable) (kind : flambda_kind),
         in_final_target s kept x ->
         kind_in_target_env s x = Some kind ->
         simple_of_kind (Meet_env.typing_env menv') (Var x) kind)
    ∧ Meet_env.names_to_avoid menv' = Meet_env.names_to_avoid menv.

(* The names of the equations that the last phase adds, and the
   variables of their types, are known to the environment in which
   the variables are defined: the one that the first extension is
   added to. *)
Definition last_phase_names_known_statement : Prop :=
  ∀ (tenv : Typing_env.t) (fuel : nat) (source : Typing_env.t)
    (s : Join_env.t) (relations : Join_env.inverse_relations)
    (menv : Meet_env.t) (kept : list (variable * flambda_kind))
    (equations relation_equations : list (name * flambda_type))
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind)),
    state_true source s ->
    relations_hold s relations ->
    relations_nonempty relations ->
    state_scoped s ->
    Meet_env.typing_env menv = source ->
    typing_env_fits (Meet_env.typing_env menv) ->
    last_phase_adds tenv fuel s relations kept equations relation_equations
      definitions ->
    let menv' :=
      variables_defined meet_env_functions menv
        (Bindings_in_target_env.imported_variables_in_order
           (Join_env.bindings s)
         ++ kept)
    in
    meet_env_kept menv menv'
    ∧ ∀ (n : name) (ty : flambda_type),
        (n, ty) ∈ equations ++ relation_equations ->
        Typing_env.mem None (Meet_env.typing_env menv') n = true
        ∧ ∀ x : variable,
            x ∈ free_variables ty ->
            Typing_env.mem None (Meet_env.typing_env menv') (Name_var x)
            = true.

(* The kinds of the equations that the last phase adds are known to
   the environment in which the variables are defined: the name of
   each is of the kind of its type, and each alias of its type is of
   the kind at which it stands ([aliases_with_kinds],
   FlambdaTypeAliasKindsSpec.v). For an alias that is a symbol, if
   the environment knows the symbol. *)
Definition last_phase_kinds_known_statement : Prop :=
  ∀ (tenv : Typing_env.t) (fuel : nat) (source : Typing_env.t)
    (s : Join_env.t) (relations : Join_env.inverse_relations)
    (menv : Meet_env.t) (kept : list (variable * flambda_kind))
    (equations relation_equations : list (name * flambda_type))
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind)),
    state_true source s ->
    relations_hold s relations ->
    relations_nonempty relations ->
    state_scoped s ->
    state_kinded s ->
    joined_envs_are typing_env_kinded s ->
    equations_kinded s ->
    relations_kinded s relations ->
    Meet_env.typing_env menv = source ->
    typing_env_fits (Meet_env.typing_env menv) ->
    last_phase_adds tenv fuel s relations kept equations relation_equations
      definitions ->
    let menv' :=
      variables_defined meet_env_functions menv
        (Bindings_in_target_env.imported_variables_in_order
           (Join_env.bindings s)
         ++ kept)
    in
    ∀ (n : name) (ty : flambda_type),
      (n, ty) ∈ equations ++ relation_equations ->
      simple_of_kind (Meet_env.typing_env menv') (simple_of_name n) (kind ty)
      ∧ ∀ (simple : simple) (k : flambda_kind),
          (simple, k) ∈ aliases_with_kinds ty ->
          (∀ sym : symbol,
             simple = Symbol sym ->
             Typing_env.mem None (Meet_env.typing_env menv') (Name_symbol sym)
             = true) ->
          simple_of_kind (Meet_env.typing_env menv') simple k.

(* What is not shown yet of the types of equations that the join
   adds: each is well formed, the names of the equations inside it are
   of the kinds of their types in the environment, and the symbols
   that it has aliases to are known there. *)
Definition types_fit_otherwise (tenv : Typing_env.t)
    (equations : list (name * flambda_type)) : Prop :=
  ∀ (n : name) (ty : flambda_type),
    (n, ty) ∈ equations ->
    type_well_formed ty = true
    ∧ type_equations_kinded tenv ty
    ∧ ∀ (sym : symbol) (k : flambda_kind),
        (Symbol sym, k) ∈ aliases_with_kinds ty ->
        Typing_env.mem None tenv (Name_symbol sym) = true.

(* The last phase in the environment of the meet, given a meet of
   expanded types that has what the meet's contract for its join
   supposes of it ([meet_expanded_head_keeps]) and types that fit
   otherwise: the environment in which the variables are defined is
   the one given, extended, and a meet may be made in it; so is the
   environment after the first extension, and the variables that the
   meets of that extension define are new; and so is the target,
   after the second. The premises on the state are those of
   [last_phase_kinds_known_statement]: what the first phases answer
   ([first_phases_true_statement], [first_phases_scoped_statement],
   [first_phases_kinded_statement], [first_phases_kinds_statement]). *)
Definition last_phase_kept_statement : Prop :=
  ∀ (tenv : Typing_env.t) (fuel : nat) (source : Typing_env.t)
    (s : Join_env.t) (relations : Join_env.inverse_relations)
    (mh : meet_expanded_head) (menv menv1 target : Meet_env.t)
    (kept : list (variable * flambda_kind))
    (equations relation_equations : list (name * flambda_type))
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind)),
    state_true source s ->
    relations_hold s relations ->
    relations_nonempty relations ->
    state_scoped s ->
    state_kinded s ->
    joined_envs_are typing_env_kinded s ->
    equations_kinded s ->
    relations_kinded s relations ->
    Meet_env.typing_env menv = source ->
    typing_env_fits (Meet_env.typing_env menv) ->
    last_phase_adds tenv fuel s relations kept equations relation_equations
      definitions ->
    let menv0 :=
      variables_defined meet_env_functions menv
        (Bindings_in_target_env.imported_variables_in_order
           (Join_env.bindings s)
         ++ kept)
    in
    types_fit_otherwise (Meet_env.typing_env menv0)
      (equations ++ relation_equations) ->
    meet_expanded_head_keeps mh ->
    Meet_env.add_env_extension menv0 (Env_extension equations) mh
    = Some menv1 ->
    Meet_env.add_env_extension menv1 (Env_extension relation_equations) mh
    = Some target ->
    meet_env_kept menv menv0
    ∧ meet_env_kept_by_meet menv0 menv1
    ∧ meet_env_kept_by_meet menv1 target.
