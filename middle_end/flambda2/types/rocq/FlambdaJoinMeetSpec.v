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
     did not know. None of them may occur in a term
     ([variables_defined_not_in_terms_statement]). So, for a valid
     state of the join whose source is
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
     is of the kind of its type there, and the type is kinded there
     (each alias of the type is of the kind at which it stands), by
     [last_phase_adds_kinded_statement] of FlambdaJoinKindsSpec.v.
     For an alias that is a symbol: the state says that an
     environment joined knows it (FlambdaJoinSpec.v,
     [simple_of_kind_in_target]), and the statement supposes that
     the source knows every symbol that an environment joined knows
     ([symbols_of_joined_envs_in_source]).
   - So the two extensions are added as the statements about the
     meet's environment suppose (FlambdaMeetEnvSpec.v,
     [add_env_extension_keeps_statement]), and each environment on
     the way to the target is the one before, extended, and one in
     which a meet may be made ([last_phase_kept_statement]). This
     has a premise that is not shown yet of the join
     ([types_fit_otherwise]): the types of the equations are well
     formed, and the names of the equations inside them are of the
     kinds of their types. The rest of what an extension must have
     to fit
     ([env_extension_fits], [env_extension_kinded]) is from the
     statements above: the names and the variables are known, the
     names are of the kinds of their types, the aliases are of their
     kinds.
   - So the join that the meet calls ([model_join_scoped_envs]) has
     the conclusions of the contract that the meet has for its join
     ([join_scoped_envs_sound], FlambdaMeetSpec.v) that are not about
     values ([join_scoped_envs_keeps],
     [model_join_scoped_envs_keeps_statement]): the result is the
     environment given, extended; a meet may be made in it; a
     variable of the result that no environment given knows is none
     of the names to avoid of the environment given and is among
     those of the result; and a [Simple] that the result knows is of
     the kind that an environment joined has it at. The premises are
     those of the contract, and one more that is not shown yet of
     the join ([join_adds_types_that_fit_otherwise]: the premise
     [types_fit_otherwise] of the statement before, for the join's
     own run).
   - The conclusion of the contract about values, on the runs that
     have conditions. For the last phase
     ([last_phase_satisfied_statement]): given also a meet of
     expanded types that has its contract on values, and an
     environment whose names to avoid have those of the state, a
     valuation that satisfies the source and an environment joined
     extends to one that satisfies the target, and the equations of
     the target are on names that have a value where those of the
     source were, if the run has the
     three conditions under which the equations added are true
     (FlambdaJoinDefineSpec.v, FlambdaJoinAddsSpec.v) and every name
     of an equation added has a value in the valuation of the target
     that the state gives. The names to avoid are needed: the
     valuation answered has what the additions make of the variables
     of the target and what the valuation given has elsewhere, and a
     variable that an environment joined knows and that a meet of
     the additions defined anew could have two values. And for the
     join that the meet calls
     ([model_join_scoped_envs_satisfied_statement]), under the
     premises of the contract, with the states of the join named.
     Not here: the conclusion on every run of the contract. The
     conditions are not among its premises and do not follow from
     them (see the CRs at the conditions in FlambdaJoinDefineSpec.v,
     and at [keeps_equations_valued] in FlambdaMeetSpec.v).

   Examples of what [model_join] computes are in
   FlambdaJoinMeetExamplesSpec.v. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaClosuresSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaTypeWellFormedSpec FlambdaBindingTime
  FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvKindedSpec FlambdaJoinEnv
  FlambdaJoinSpec FlambdaJoinEnvSpec FlambdaJoinStateSpec
  FlambdaJoinDefineSpec FlambdaJoinFitsSpec FlambdaJoinAddsSpec
  FlambdaJoinKindsSpec FlambdaJoinNamesSpec FlambdaTypeAliasKindsSpec
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

(* And none of them may occur in a term: each is defined at the mode
   of the variables that exist only in types, so the environment
   answered does not know it at the mode of terms. *)
Definition variables_defined_not_in_terms_statement : Prop :=
  ∀ (vars : list (variable * flambda_kind)) (menv : Meet_env.t)
    (x : variable),
    typing_env_fits (Meet_env.typing_env menv) ->
    NoDup (map fst vars) ->
    (∀ y : variable,
       y ∈ map fst vars ->
       Typing_env.mem None (Meet_env.typing_env menv) (Name_var y) = false) ->
    x ∈ map fst vars ->
    Typing_env.mem (Some Name_mode.normal)
      (Meet_env.typing_env (variables_defined meet_env_functions menv vars))
      (Name_var x)
    = false.

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

(* A symbol that an environment joined knows is known to the source.
   (The contract of the join that Simplify calls supposes it,
   [symbols_of_uses_in_source] of FlambdaJoinSpec.v; the contract
   that the meet has for its join is to suppose it of the
   environments that it joins.) *)
Definition symbols_of_joined_envs_in_source (source : Typing_env.t)
    (s : Join_env.t) : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t) (sym : symbol),
    Join_env.joined_env s index = Some use ->
    Typing_env.mem None use (Name_symbol sym) = true ->
    Typing_env.mem None source (Name_symbol sym) = true.

(* The kinds of the equations that the last phase adds are known to
   the environment in which the variables are defined: the name of
   each is of the kind of its type, and its type is kinded there
   ([type_kinded], FlambdaTypingEnvKindedSpec.v: each alias of the
   type is of the kind at which it stands). The environments joined
   have their invariant, and know no symbol that the source does
   not. *)
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
    joined_envs_are typing_env_invariant s ->
    joined_envs_are typing_env_kinded s ->
    symbols_of_joined_envs_in_source source s ->
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
      ∧ type_kinded (Meet_env.typing_env menv') ty.

(* What is not shown yet of the types of equations that the join
   adds: each is well formed, and the names of the equations inside
   it are of the kinds of their types in the environment. *)
Definition types_fit_otherwise (tenv : Typing_env.t)
    (equations : list (name * flambda_type)) : Prop :=
  ∀ (n : name) (ty : flambda_type),
    (n, ty) ∈ equations ->
    type_well_formed ty = true ∧ type_equations_kinded tenv ty.

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
    joined_envs_are typing_env_invariant s ->
    joined_envs_are typing_env_kinded s ->
    symbols_of_joined_envs_in_source source s ->
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

(* ======================================================================== *)
(* The contract that the meet has for its join, but for the values          *)
(* ======================================================================== *)

(* The conclusions of the contract that the meet has for its join
   ([join_scoped_envs_sound], FlambdaMeetSpec.v) that are not about
   values, under its premises but the one about the values that the
   meet of expanded types keeps ([meet_expanded_head_sound]), which
   they do not need; and one more, that the first environment knows
   every symbol that an environment joined knows. *)
(* CR mshinwell: 2026-11-12. The premise on symbols is not in the
   contract as it is merged. It is on its way there as a fourth
   conjunct of [scoped_env_of] (agreed with the owner of the meet; in
   review). When it is merged the premise here goes. *)
Definition join_scoped_envs_keeps (join : join_scoped_envs) : Prop :=
  ∀ (meet_head : meet_expanded_head) (initial_env result : Meet_env.t)
    (scoped_envs : list Typing_env.t),
    let initial_tenv := Meet_env.typing_env initial_env in
    meet_expanded_head_keeps meet_head ->
    typing_env_fits initial_tenv ->
    (∀ scoped_env : Typing_env.t,
      scoped_env ∈ scoped_envs -> scoped_env_of initial_tenv scoped_env) ->
    (∀ (scoped_env : Typing_env.t) (sym : symbol),
      scoped_env ∈ scoped_envs ->
      Typing_env.mem None scoped_env (Name_symbol sym) = true ->
      Typing_env.mem None initial_tenv (Name_symbol sym) = true) ->
    scoped_envs_agree scoped_envs ->
    join meet_head (Typing_env.current_scope initial_tenv) initial_env
      initial_tenv scoped_envs
    = Some result ->
    meet_env_extends initial_env result
    ∧ typing_env_fits (Meet_env.typing_env result)
    ∧ (∀ x : variable,
        Typing_env.mem None (Meet_env.typing_env result) (Name_var x)
        = true ->
        Typing_env.mem None initial_tenv (Name_var x) = false ->
        (∀ scoped_env : Typing_env.t,
          scoped_env ∈ scoped_envs ->
          Typing_env.mem None scoped_env (Name_var x) = false) ->
        among x (Meet_env.names_to_avoid initial_env) = false
        ∧ among x (Meet_env.names_to_avoid result) = true)
    ∧ ∀ (scoped_env : Typing_env.t) (s : simple) (kind : flambda_kind),
        scoped_env ∈ scoped_envs ->
        Typing_env.mem_simple None (Meet_env.typing_env result) s = true ->
        simple_of_kind scoped_env s kind ->
        simple_of_kind (Meet_env.typing_env result) s kind.

(* What is not shown yet of the model's join, as the meet calls it on
   inputs that have what the contract supposes: the types of the
   equations that its last phase adds fit otherwise
   ([types_fit_otherwise]), in the environment in which its variables
   are defined. The states are named by the equations of the first
   phases, as in [cut_and_n_way_join0_replayed_statement]
   (FlambdaJoinAddsSpec.v). *)
Definition join_adds_types_that_fit_otherwise
    (join_choices : Join_env.choices) (join_depth : nat) (fuel : fuels)
    : Prop :=
  ∀ (initial_env : Meet_env.t) (scoped_envs : list Typing_env.t)
    (envs : Joined_envs.t) (s1 s2 s3 : Join_env.t)
    (relations2 relations3 : Join_env.inverse_relations)
    (tenv : Typing_env.t) (kept : list (variable * flambda_kind))
    (equations relation_equations : list (name * flambda_type))
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind)),
    let initial_tenv := Meet_env.typing_env initial_env in
    let p := join_parameters join_depth in
    let jt := model_join_of_types join_depth fuel in
    let avoid :=
      Meet_env.names_to_avoid initial_env
      ++ Join_env.variables_of_env initial_tenv
      ++ flat_map Join_env.variables_of_env scoped_envs
    in
    let s0 :=
      Join_env.create envs
        (Bindings_in_target_env.from_source_env avoid initial_tenv)
    in
    typing_env_fits initial_tenv ->
    (∀ scoped_env : Typing_env.t,
      scoped_env ∈ scoped_envs -> scoped_env_of initial_tenv scoped_env) ->
    (∀ (scoped_env : Typing_env.t) (sym : symbol),
      scoped_env ∈ scoped_envs ->
      Typing_env.mem None scoped_env (Name_symbol sym) = true ->
      Typing_env.mem None initial_tenv (Name_symbol sym) = true) ->
    scoped_envs_agree scoped_envs ->
    Join_env.cut_for_joins (Typing_env.current_scope initial_tenv)
      (Index.number scoped_envs)
    = Some envs ->
    Join_env.join_aliases_into_bindings p (fuel_of_env fuel) s0 envs
    = Some s1 ->
    Join_env.n_way_join_delayed_equations (fuel_of_env fuel) join_choices jt
      s1 [] (Join_env.new_equations_in_joined_envs s1 s0)
    = Some (relations2, s2) ->
    Join_env.n_way_join_loop join_depth p (fuel_of_env fuel) join_choices jt
      s2 relations2 (Join_env.new_definitions_of_existentials s2 s0)
    = Some (relations3, s3) ->
    last_phase_adds tenv (fuel_of_env fuel) s3 relations3 kept equations
      relation_equations definitions ->
    types_fit_otherwise
      (Meet_env.typing_env
         (variables_defined meet_env_functions
            (Meet_env.with_names_to_avoid initial_env
               (Bindings_in_target_env.names_to_avoid (Join_env.bindings s3)))
            (Bindings_in_target_env.imported_variables_in_order
               (Join_env.bindings s3)
             ++ kept)))
      (equations ++ relation_equations).

Definition model_join_scoped_envs_keeps_statement : Prop :=
  ∀ (join_choices : Join_env.choices) (join_depth : nat) (fuel : fuels),
    join_adds_types_that_fit_otherwise join_choices join_depth fuel ->
    join_scoped_envs_keeps
      (model_join_scoped_envs join_choices join_depth fuel).

(* ======================================================================== *)
(* The target is satisfied, on the runs that have the conditions            *)
(* ======================================================================== *)

(* The last phase in the environment of the meet, at the run of an
   environment joined. The premises are those of
   [last_phase_kept_statement], and: the meet of expanded types has
   what the meet's contract supposes of it on values
   ([meet_expanded_head_sound]); the names to avoid of the environment
   given have those of the state; the valuation satisfies the source
   and the environment joined; the run has the three conditions under
   which the equations added are true ([tags_at],
   [aliases_have_values], [relation_scrutinees_have_values]:
   [last_phase_adds_true_statement], FlambdaJoinAddsSpec.v); and
   every name of an equation added has a value in the valuation of
   the target that the state gives ([target_valuation],
   FlambdaJoinStateSpec.v). Then some valuation satisfies the target
   and has, for each variable that the environment joined knows,
   what the valuation given has ([extended_from],
   FlambdaMeetSpec.v); and whatever the scope, if the equations that
   the source has after it are on names that have a value in the
   valuation given, those that the target has after it are on names
   that have one in the valuation answered
   ([keeps_equations_valued], FlambdaMeetSpec.v). *)
Definition last_phase_satisfied_statement : Prop :=
  ∀ (tenv : Typing_env.t) (fuel : nat) (source : Typing_env.t)
    (s : Join_env.t) (relations : Join_env.inverse_relations)
    (mh : meet_expanded_head) (menv menv1 target : Meet_env.t)
    (kept : list (variable * flambda_kind))
    (equations relation_equations : list (name * flambda_type))
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) (use : Typing_env.t) (statics : static_env)
    (valuation : env),
    state_true source s ->
    relations_hold s relations ->
    relations_nonempty relations ->
    state_scoped s ->
    state_kinded s ->
    joined_envs_are typing_env_invariant s ->
    joined_envs_are typing_env_kinded s ->
    symbols_of_joined_envs_in_source source s ->
    equations_kinded s ->
    relations_kinded s relations ->
    Meet_env.typing_env menv = source ->
    typing_env_fits (Meet_env.typing_env menv) ->
    (∀ x : variable,
       x ∈ names_to_avoid s ->
       among x (Meet_env.names_to_avoid menv) = true) ->
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
    meet_expanded_head_sound mh ->
    Meet_env.add_env_extension menv0 (Env_extension equations) mh
    = Some menv1 ->
    Meet_env.add_env_extension menv1 (Env_extension relation_equations) mh
    = Some target ->
    Join_env.joined_env s index = Some use ->
    statics_valid statics ->
    typing_env_satisfied_strictly statics valuation source ->
    typing_env_satisfied_strictly statics valuation use ->
    tags_at s use statics valuation ->
    aliases_have_values s index use valuation ->
    relation_scrutinees_have_values s relations index use valuation ->
    let tv := target_valuation s index use valuation in
    (∀ (n : name) (ty : flambda_type),
       (n, ty) ∈ equations ++ relation_equations ->
       ∃ v : value, value_of_name tv n = Some v) ->
    ∃ valuation' : env,
      extended_from use valuation valuation'
      ∧ typing_env_satisfied_strictly statics valuation'
          (Meet_env.typing_env target)
      ∧ keeps_equations_valued source (Meet_env.typing_env target) valuation
          valuation'.

(* The same of the join that the meet calls, under the premises of
   the contract that the meet has for its join
   ([join_scoped_envs_sound], FlambdaMeetSpec.v) and the two more of
   [model_join_scoped_envs_keeps_statement]: at an environment
   joined, on a run that has the conditions, a valuation that
   satisfies the first environment and that one extends to one that
   satisfies the result, and the equations of the result are on
   names that have a value where those of the first environment
   were. This is the conclusion of the contract about values, on
   those runs, which are not all the runs of the contract: its
   premise on a run ([equations_valued]) is not among the conditions
   and they do not follow from it. The conditions are about
   the state that the first phases of the join answer and about what
   its last phase adds, so those are named, by the equations that
   determine them (as in [join_adds_types_that_fit_otherwise]; the
   environment in which the last phase chooses aliases is the one in
   which the variables brought in are defined). The environment
   joined is given by its index in the state, where the contract has
   a member of the list. *)
Definition model_join_scoped_envs_satisfied_statement : Prop :=
  ∀ (join_choices : Join_env.choices) (join_depth : nat) (fuel : fuels),
    join_adds_types_that_fit_otherwise join_choices join_depth fuel ->
    ∀ (meet_head : meet_expanded_head) (initial_env result : Meet_env.t)
      (scoped_envs : list Typing_env.t) (envs : Joined_envs.t)
      (s1 s2 s3 : Join_env.t)
      (relations2 relations3 : Join_env.inverse_relations)
      (kept : list (variable * flambda_kind))
      (equations relation_equations : list (name * flambda_type))
      (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind))
      (index : Index.t) (scoped_env : Typing_env.t) (statics : static_env)
      (valuation : env),
      let initial_tenv := Meet_env.typing_env initial_env in
      let p := join_parameters join_depth in
      let jt := model_join_of_types join_depth fuel in
      let avoid :=
        Meet_env.names_to_avoid initial_env
        ++ Join_env.variables_of_env initial_tenv
        ++ flat_map Join_env.variables_of_env scoped_envs
      in
      let s0 :=
        Join_env.create envs
          (Bindings_in_target_env.from_source_env avoid initial_tenv)
      in
      let menv :=
        Meet_env.with_names_to_avoid initial_env
          (Bindings_in_target_env.names_to_avoid (Join_env.bindings s3))
      in
      meet_expanded_head_sound meet_head ->
      meet_expanded_head_keeps meet_head ->
      typing_env_fits initial_tenv ->
      (∀ scoped_env : Typing_env.t,
        scoped_env ∈ scoped_envs -> scoped_env_of initial_tenv scoped_env) ->
      (∀ (scoped_env : Typing_env.t) (sym : symbol),
        scoped_env ∈ scoped_envs ->
        Typing_env.mem None scoped_env (Name_symbol sym) = true ->
        Typing_env.mem None initial_tenv (Name_symbol sym) = true) ->
      scoped_envs_agree scoped_envs ->
      model_join_scoped_envs join_choices join_depth fuel meet_head
        (Typing_env.current_scope initial_tenv) initial_env initial_tenv
        scoped_envs
      = Some result ->
      Join_env.cut_for_joins (Typing_env.current_scope initial_tenv)
        (Index.number scoped_envs)
      = Some envs ->
      Join_env.join_aliases_into_bindings p (fuel_of_env fuel) s0 envs
      = Some s1 ->
      Join_env.n_way_join_delayed_equations (fuel_of_env fuel) join_choices jt
        s1 [] (Join_env.new_equations_in_joined_envs s1 s0)
      = Some (relations2, s2) ->
      Join_env.n_way_join_loop join_depth p (fuel_of_env fuel) join_choices jt
        s2 relations2 (Join_env.new_definitions_of_existentials s2 s0)
      = Some (relations3, s3) ->
      last_phase_adds
        (Meet_env.typing_env
           (variables_defined meet_env_functions menv
              (Bindings_in_target_env.imported_variables_in_order
                 (Join_env.bindings s3))))
        (fuel_of_env fuel) s3 relations3 kept equations relation_equations
        definitions ->
      Join_env.joined_env s3 index = Some scoped_env ->
      statics_valid statics ->
      typing_env_satisfied_strictly statics valuation initial_tenv ->
      typing_env_satisfied_strictly statics valuation scoped_env ->
      tags_at s3 scoped_env statics valuation ->
      aliases_have_values s3 index scoped_env valuation ->
      relation_scrutinees_have_values s3 relations3 index scoped_env valuation
      ->
      (∀ (n : name) (ty : flambda_type),
         (n, ty) ∈ equations ++ relation_equations ->
         ∃ v : value,
           value_of_name (target_valuation s3 index scoped_env valuation) n
           = Some v) ->
      ∃ valuation' : env,
        extended_from scoped_env valuation valuation'
        ∧ typing_env_satisfied_strictly statics valuation'
            (Meet_env.typing_env result)
        ∧ keeps_equations_valued initial_tenv (Meet_env.typing_env result)
            valuation valuation'.
