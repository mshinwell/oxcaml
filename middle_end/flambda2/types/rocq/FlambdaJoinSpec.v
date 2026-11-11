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


(* What the n-way join of typing environments guarantees.

   To be reviewed: every definition and statement of this file, against
   middle_end/flambda2/types/env/join_env.ml (the header comment, which
   states what the join assumes of its inputs, and the interface
   join_env.mli), types/join_levels.ml (the entry check
   [check_join_inputs]) and the three callers in Simplify that read the
   result: simplify/join_points.ml, simplify_switch_expr.ml and
   specialization_cost.ml. The functions themselves are transcribed in
   FlambdaJoinEnv.v and FlambdaJoinTypes.v; only the first parts of
   those exist yet. This file is the contract that the transcription is
   to be proved to meet, and that the meet (FlambdaMeetSpec.v, another
   workstream) assumes of the join it is given. Until the functions are
   there, the contract is a predicate on a function
   ([sound_join_of_environments]); the statements proved now are those
   that do not need the functions.

   The compiler has two joins. The binary one (meet_and_join.ml,
   join_levels_old.ml) is the default today; the n-way one is to become
   the default and is the one specified here. The contract does not
   mention which: any join that meets it will do, and the binary one is
   kept as an oracle for the differential tests.

   What is joined. [join_inputs]: a source environment, a scope, and a
   list of use environments, each with the identifier that the caller
   has for it. In Simplify the source is the environment in which the
   handler of a continuation would be simplified if nothing were known
   of its uses, with the parameters defined; the uses are the
   environments at the [Apply_cont]s; the scope is that of the
   continuation's definition. In the meet the source is the environment
   of the meet and the uses are the environments of the branches of a
   disjunction. The use environments are numbered from 0 in the order
   of the list ([Index]). The join answers the target environment, which
   is the source with one level more, and an analysis
   ([Analysis.t], FlambdaJoinEnv.v). Inside the join, types are joined
   from lists of pairs of an index and a type that holds in the
   environment of that index ([n_way_join_type_sound]).

   What is guaranteed ([join_guarantees]), for a use and a valuation
   that satisfies it strictly: some valuation satisfies the target
   strictly, gives every variable that the use knows the value it had
   (or leaves it without one, if it had none), and gives every variable
   that has a definition in the analysis the value, at that use, of the
   [Simple] that the analysis says. It is one valuation for the whole
   target: every equation of the target, on the names of the source and
   on the names that the join made, holds under it together. A variable
   of the target that the use does not know, and that no alias forces,
   has no value in it.

   The decisions this rests on, and what is not promised.
   - Valuations are partial and satisfaction is strict. The n-way join
     imports a variable that only some uses define, under its own name,
     with the join of its types over those uses ([find_imported_var]);
     and makes an existential variable for a vector of [Simple]s that
     covers only some uses (the contributors of one case of a row-like
     structure). At another use no value need have that type: the
     variable means nothing there. So the valuation that witnesses the
     target at a use leaves such a variable without a value, and a
     type that reaches it by an alias is satisfied by no value. The
     definitions for this are the typing environment's
     ([typing_env_satisfied_strictly]); the module [Interim] below
     holds them until that file has them.
   - Poison (decision D26). Typing facts are about values that are not
     poison. The contract is stated with strict satisfaction: at a use
     that holds, a name that holds poison has a type that poison has.
     Nothing is promised of a use that is satisfied only with the
     exemption of the names that hold poison ([typing_env_satisfied]):
     a join expands aliases, and through a name that is exempt that is
     wrong (the CR at [join_admits_use]). A relation says nothing of a
     scrutinee that is poison: that is in the meaning of types
     ([relation_holds]), and the relations that the join rebuilds are
     true in that sense. Aliases are exact: the target's are respected
     by the witness, and a variable with a definition has exactly the
     value of its definition, poison included.
   - No leastness, and no equality with the binary join. The join that
     answers the source and says nothing meets this contract
     ([join_to_source_sound_statement]). What is promised of precision
     is stated separately, for named cases: today one,
     [join_keeps_constants].
   - Physical equality (decision D30) is not in the model. The three
     places where the compiler's result depends on it
     ([import_or_delay_n_way_join_of_concrete_type] and
     [n_way_join_env_extension] in join_env.ml,
     [n_way_join_int_indexed_product] in meet_and_n_way_join.ml) are to
     be transcribed as they behave under the compiler's flag that makes
     the result a function of the structure of the inputs
     (-flambda2-join-sharing, being added; with the value [structural]
     the test is an equality of types, with [none] the shortcut is
     taken only where there is one input). The contract holds of either
     branch at each.
   - That the join answers is not promised: [None] is a fatal error of
     the compiler or the model's fuel run out.
   - Code age, allocation modes and symbol projections have no meaning
     here (FlambdaTypeMeaningSpec.v, FlambdaTypingEnv.v).

   What the inputs must satisfy ([join_inputs_well_formed],
   [uses_refine_source]), against the three hypotheses of the header of
   join_env.ml.
   - "Any name defined in the source environment is also defined in all
     the joined environments." Not required here, and not true of what
     Simplify passes: [check_join_inputs] says that the source may have
     variables in types, made when lifted constants were added to it,
     that no use has; and the second hypothesis itself says that a
     symbol lifted in one branch is not defined in the others. Nothing
     checks it. What the contract needs in its place:
     [terms_in_scope_at_uses] (a variable that may occur in terms in
     the source may occur in terms at each use), and
     [uses_refine_source] (what the source says holds at each use).
   - "Any symbol defined in one of the joined environments is also
     defined in the source environment." Required
     ([symbols_of_uses_in_source]), for the target to be well formed
     only. [check_join_inputs] checks it of the set of symbols that
     Simplify passes beside the environments, not of the environments;
     the meet's calls are not checked.
   - "The relative order of variables defined in the source environment
     is preserved across all the joined environments."
     [binding_times_coherent]. Nothing checks it. It is not required
     for the guarantee: the compiler uses it to find the only source
     variable that can stand for a vector of [Simple]s, and then checks
     that it does ([equal_in_all_joined_envs]). It would be a premise
     of a statement that aliases between source variables are kept,
     which is not promised yet.
   Each difference is recorded as a discrepancy (T5-1 to T5-3).

   The known failure. The n-way join of two closure types is not an
   upper bound where one says nothing of the code of a function and the
   other names it: [n_way_join_closures_entry] keeps a function type
   that only some of the entries joined have
   ([n_way_join_function_types] in FlambdaJoinTypes.v is that part of
   it). [n_way_join_closures_entry_not_upper_bound_statement] is the
   instance. So no transcription of the compiler's function can meet
   [n_way_join_type_sound], and the contract is not weakened for it.
   With the one change of [n_way_join_function_types_proposed], which
   keeps a function type only if every entry has one, a closures entry
   that holds with the function types of one of the entries joined
   holds with those joined
   ([n_way_join_function_types_proposed_sound_statement]).
   Discrepancies T1-4 and R3-7; a program that the compiler miscompiles
   because of it is in the record of reproductions. *)

From Stdlib Require Import ZArith List Bool PeanoNat.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaJoinEnv
  FlambdaJoinTypes.
Import ListNotations.

(* ======================================================================== *)
(* Strict satisfaction, until the typing environment's file has it          *)
(* ======================================================================== *)

(* These three definitions are the typing environment's, agreed with its
   owner under these names; they are here until FlambdaTypingEnvSpec.v
   has them, and then go. A valuation may leave a name that the
   environment knows without a value; nothing is asked of such a
   name. *)
Module Interim.

(* The environment is not bottom; every name with a type that has a
   value in the valuation has a value of that type, or is exempt and
   has a value of the kind of the type; and aliases have the same
   value, or none has one. *)
Definition typing_env_satisfied_but (exempt : name -> Prop)
    (statics : static_env) (valuation : env) (tenv : Typing_env.t) : Prop :=
  Typing_env.is_bottom tenv = false
  ∧ (∀ (n : name) (ty : flambda_type)
       (binding_time_and_mode : Binding_time.With_name_mode.t) (v : value),
       Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
       = Some (ty, binding_time_and_mode) ->
       value_of_name valuation n = Some v ->
       type_satisfied statics valuation v ty
       ∨ (exempt n ∧ kind_of_value v = kind ty))
  ∧ aliases_respected (Typing_env.aliases tenv) valuation.

(* No name is exempt. *)
Definition typing_env_satisfied_strictly (statics : static_env)
    (valuation : env) (tenv : Typing_env.t) : Prop :=
  typing_env_satisfied_but (fun _ => False) statics valuation tenv.

(* The machine satisfies an environment strictly: some valuation does
   that agrees with it on the variables that may occur in terms, and
   the machine has a value for each of those. *)
Definition env_satisfies_strictly (tenv : Typing_env.t)
    (statics : static_env) (vars : env) : Prop :=
  ∃ valuation : env,
    typing_env_satisfied_strictly statics valuation tenv
    ∧ agrees_in_terms tenv valuation vars
    ∧ ∀ x : variable, in_scope_in_terms tenv x -> lookup x vars <> None.

End Interim.

Import Interim.

(* ======================================================================== *)
(* What is joined                                                           *)
(* ======================================================================== *)

(* An environment knows a variable: the variable is bound there,
   whatever its name mode and whether or not it is still in scope. This
   is the compiler's [Typing_env.mem] with no minimal name mode. *)
Definition knows (tenv : Typing_env.t) (x : variable) : Prop :=
  Typing_env.mem None tenv (Name_var x) = true.

(* The inputs of a join: the source environment, the scope after which
   the use environments are cut, and the use environments, each with
   the caller's identifier for it. *)
Record join_inputs (A : Type) : Type := {
  source : Typing_env.t;
  cut_after : Scope.t;
  uses : list (A * Typing_env.t)
}.

Arguments source {A} _.
Arguments cut_after {A} _.
Arguments uses {A} _.

(* The use environment of an index. *)
Definition use_at {A : Type} (inputs : join_inputs A) (index : Index.t)
    (use : Typing_env.t) : Prop :=
  ∃ id : A, nth_error (uses inputs) index = Some (id, use).

(* A join of environments, as a function: the variables that the names
   it makes must avoid, and the inputs. It answers the target
   environment and the analysis; [None] is a fatal error of the
   compiler, or fuel run out. *)
Definition join_of_environments (A : Type) : Type :=
  list variable -> join_inputs A -> option (Typing_env.t * Analysis.t A).

(* ======================================================================== *)
(* One valuation for the target at a use                                    *)
(* ======================================================================== *)

(* The second valuation gives every variable that the use knows what the
   first gives it: the same value, or none. *)
Definition agrees_on_known (use : Typing_env.t) (valuation valuation' : env)
    : Prop :=
  ∀ x : variable, knows use x -> lookup x valuation' = lookup x valuation.

(* The second valuation gives every variable that has a definition at
   the use of index [index] what that definition has in the first, a
   valuation of that use. *)
Definition definitions_hold
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) (valuation valuation' : env) : Prop :=
  ∀ (x : variable) (simples : Simples_in_joined_envs.t) (kind : flambda_kind)
    (simple : simple),
    lookup x definitions = Some (simples, kind) ->
    Simples_in_joined_envs.find index simples = Some simple ->
    lookup x valuation' = eval_simple valuation simple.

(* The target admits a use, of index [index]: every valuation that
   satisfies the use extends to one that satisfies the target, under
   which the definitions of the two maps of the analysis hold. *)
(* CR mshinwell: the use must be satisfied strictly: a name that holds
   poison there must have a type that poison has. The use environments
   that variant unboxing makes are satisfied only with the exemption of
   the names that hold poison (decision D26), and of those nothing is
   promised here. The statement with the exemption on both sides is
   false: if [x : block of one field (= y)] and [y : {7}] at a use where
   [y] holds poison, and [x : block of one field {5}] at another, the
   join answers [x : block of one field {5, 7}], which the value of [x]
   at the first use has not. The compiler does the same, relying on a
   parameter that holds poison never being read; nothing checks that.
   Decision D26. *)
Definition join_admits_use (use target : Typing_env.t)
    (definitions definitions_at_normal_mode
       : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) : Prop :=
  ∀ (statics : static_env) (valuation : env),
    typing_env_satisfied_strictly statics valuation use ->
    ∃ valuation' : env,
      typing_env_satisfied_strictly statics valuation' target
      ∧ agrees_on_known use valuation valuation'
      ∧ definitions_hold definitions index valuation valuation'
      ∧ definitions_hold definitions_at_normal_mode index valuation
          valuation'.

(* ======================================================================== *)
(* What the inputs must satisfy                                             *)
(* ======================================================================== *)

(* What the source says holds at a use: a valuation that satisfies the
   use extends to one that satisfies the source. In Simplify this is so
   because the use environment was made from the environment at the
   definition of the continuation by adding definitions and equations,
   and the parameters are defined at the use with the types of the
   arguments. *)
(* CR mshinwell: this is a premise about what the environments mean,
   where the header of join_env.ml has one about the names they define,
   which is false of Simplify's inputs. It may not hold of them either:
   the source has the types of the constants lifted while the body of
   the continuation was simplified, and on a path that did not go
   through the branch that defines such a symbol the symbol is bound to
   nothing, so its type is not true there. That is for the workstream
   on continuations and the owner of the typing environment: facts
   about a symbol may have to be asked only where the symbol is bound.
   Discrepancy T5-4. *)
Definition use_refines_source (source use : Typing_env.t) : Prop :=
  ∀ (statics : static_env) (valuation : env),
    typing_env_satisfied_strictly statics valuation use ->
    ∃ valuation0 : env,
      typing_env_satisfied_strictly statics valuation0 source
      ∧ agrees_on_known use valuation valuation0.

Definition uses_refine_source {A : Type} (inputs : join_inputs A) : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t),
    use_at inputs index use -> use_refines_source (source inputs) use.

(* One variable is bound strictly before another in an environment. *)
Definition bound_strictly_earlier (tenv : Typing_env.t) (x y : variable)
    : Prop :=
  ∃ time_x time_y : Binding_time.With_name_mode.t,
    Typing_env.binding_time_and_mode tenv (Name_var x) = Some time_x
    ∧ Typing_env.binding_time_and_mode tenv (Name_var y) = Some time_y
    ∧ Binding_time.strictly_earlier
        (Binding_time.With_name_mode.binding_time time_x)
        (Binding_time.With_name_mode.binding_time time_y)
      = true.

(* The third hypothesis of the header of join_env.ml: the variables of
   the source are bound in the same order at every use that knows them.
   It is not part of [join_inputs_well_formed]. *)
Definition binding_times_coherent {A : Type} (inputs : join_inputs A)
    : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t) (x y : variable),
    use_at inputs index use ->
    knows use x ->
    knows use y ->
    bound_strictly_earlier (source inputs) x y ->
    bound_strictly_earlier use x y.

Section Contract.

(* The invariant of a typing environment (binding times that differ,
   names that are bound where they are mentioned, kinds), which the
   typing environment's file is to define under this name. *)
Context (typing_env_well_formed : Typing_env.t -> Prop).

(* Every environment given is well formed. *)
Definition environments_well_formed {A : Type} (inputs : join_inputs A)
    : Prop :=
  typing_env_well_formed (source inputs)
  ∧ ∀ (index : Index.t) (use : Typing_env.t),
      use_at inputs index use -> typing_env_well_formed use.

(* Every use environment that is not bottom can be cut after the
   scope. *)
Definition cuts_defined {A : Type} (inputs : join_inputs A) : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t),
    use_at inputs index use ->
    Typing_env.is_bottom use = false ->
    ∃ level : Typing_env_level.t,
      Typing_env.cut use (cut_after inputs) = Some level.

(* A variable that may occur in terms in the source may occur in terms
   at each use. *)
Definition terms_in_scope_at_uses {A : Type} (inputs : join_inputs A)
    : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t) (x : variable),
    use_at inputs index use ->
    in_scope_in_terms (source inputs) x ->
    in_scope_in_terms use x.

(* A symbol that a use defines is defined in the source. *)
Definition symbols_of_uses_in_source {A : Type} (inputs : join_inputs A)
    : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t) (s : symbol),
    use_at inputs index use ->
    Typing_env.mem None use (Name_symbol s) = true ->
    Typing_env.mem None (source inputs) (Name_symbol s) = true.

(* The variables to avoid include every variable that the source or a
   use knows. *)
Definition avoids_known {A : Type} (avoid : list variable)
    (inputs : join_inputs A) : Prop :=
  (∀ x : variable, knows (source inputs) x -> among x avoid = true)
  ∧ ∀ (index : Index.t) (use : Typing_env.t) (x : variable),
      use_at inputs index use -> knows use x -> among x avoid = true.

Definition join_inputs_well_formed {A : Type} (avoid : list variable)
    (inputs : join_inputs A) : Prop :=
  environments_well_formed inputs
  ∧ cuts_defined inputs
  ∧ terms_in_scope_at_uses inputs
  ∧ symbols_of_uses_in_source inputs
  ∧ avoids_known avoid inputs.

(* ======================================================================== *)
(* What the join guarantees                                                 *)
(* ======================================================================== *)

(* The target is the source with more in its last level: every name
   that had a type has one, with the binding time and the name mode it
   had; the same symbols are defined; the earlier levels, the scope and
   the first binding time in scope are those of the source. *)
Definition join_keeps_source (source target : Typing_env.t) : Prop :=
  (∀ (n : name) (ty : flambda_type)
     (binding_time_and_mode : Binding_time.With_name_mode.t),
     Keyed.lookup name_eqb n (Typing_env.names_to_types source)
     = Some (ty, binding_time_and_mode) ->
     ∃ ty' : flambda_type,
       Keyed.lookup name_eqb n (Typing_env.names_to_types target)
       = Some (ty', binding_time_and_mode))
  ∧ (∀ s : symbol,
       Typing_env.mem None target (Name_symbol s)
       = Typing_env.mem None source (Name_symbol s))
  ∧ Typing_env.prev_levels target = Typing_env.prev_levels source
  ∧ Typing_env.current_scope target = Typing_env.current_scope source
  ∧ Typing_env.min_binding_time target = Typing_env.min_binding_time source.

(* A variable that the target knows and the source does not may not
   occur in terms, and either some use that is not bottom knows it (it
   was imported under its own name) or it is none of the variables to
   avoid (it was made by the join). This is said of membership only:
   which variable the join makes is not specified. *)
Definition join_introduces {A : Type} (avoid : list variable)
    (inputs : join_inputs A) (target : Typing_env.t) : Prop :=
  ∀ x : variable,
    knows target x ->
    ~ knows (source inputs) x ->
    ~ in_scope_in_terms target x
    ∧ ((∃ (index : Index.t) (use : Typing_env.t),
          use_at inputs index use
          ∧ Typing_env.is_bottom use = false
          ∧ knows use x)
       ∨ among x avoid = false).

(* What the analysis speaks of. Its identifiers are those of uses that
   are not bottom, by index. A definition is of a variable that
   the target knows, at a use with an identifier, and is a [Simple] of
   that use; a definition at the normal name mode is a [Simple] that
   may occur in terms at that use. *)
Definition analysis_describes_uses {A : Type} (inputs : join_inputs A)
    (target : Typing_env.t) (analysis : Analysis.t A) : Prop :=
  (∀ (index : Index.t) (id : A),
     Keyed.lookup Index.equal index (Analysis.external_ids analysis) = Some id
     -> ∃ use : Typing_env.t,
          nth_error (uses inputs) index = Some (id, use)
          ∧ Typing_env.is_bottom use = false)
  ∧ (∀ (x : variable) (simples : Simples_in_joined_envs.t)
       (kind : flambda_kind) (index : Index.t) (simple : simple),
       lookup x (Analysis.definitions_in_joined_envs analysis)
       = Some (simples, kind) ->
       Simples_in_joined_envs.find index simples = Some simple ->
       knows target x
       ∧ ∃ (id : A) (use : Typing_env.t),
           nth_error (uses inputs) index = Some (id, use)
           ∧ Keyed.lookup Index.equal index (Analysis.external_ids analysis)
             = Some id
           ∧ Typing_env.mem_simple None use simple = true)
  ∧ (∀ (x : variable) (simples : Simples_in_joined_envs.t)
       (kind : flambda_kind) (index : Index.t) (simple : simple),
       lookup x (Analysis.canonical_definitions_at_normal_mode analysis)
       = Some (simples, kind) ->
       Simples_in_joined_envs.find index simples = Some simple ->
       knows target x
       ∧ ∃ (id : A) (use : Typing_env.t),
           nth_error (uses inputs) index = Some (id, use)
           ∧ Keyed.lookup Index.equal index (Analysis.external_ids analysis)
             = Some id
           ∧ Typing_env.mem_simple (Some Name_mode.normal) use simple = true).

(* What a join guarantees of its result. *)
Definition join_guarantees {A : Type} (avoid : list variable)
    (inputs : join_inputs A) (target : Typing_env.t)
    (analysis : Analysis.t A) : Prop :=
  typing_env_well_formed target
  ∧ join_keeps_source (source inputs) target
  ∧ join_introduces avoid inputs target
  ∧ analysis_describes_uses inputs target analysis
  ∧ (∀ (index : Index.t) (use : Typing_env.t),
       use_at inputs index use ->
       join_admits_use use target
         (Analysis.definitions_in_joined_envs analysis)
         (Analysis.canonical_definitions_at_normal_mode analysis) index).

(* The contract of a join of environments. *)
Definition sound_join_of_environments {A : Type}
    (join : join_of_environments A) : Prop :=
  ∀ (avoid : list variable) (inputs : join_inputs A) (target : Typing_env.t)
    (analysis : Analysis.t A),
    join_inputs_well_formed avoid inputs ->
    uses_refine_source inputs ->
    join avoid inputs = Some (target, analysis) ->
    join_guarantees avoid inputs target analysis.

(* Precision, for one named case: a variable of the source that has, in
   the level cut from every use that is not bottom, an equation to the
   same constant, is that constant in the target, unless the target is
   bottom. (Simplify needs it to propagate a constant through a join
   point.) There must be such a use. *)
Definition join_keeps_constants {A : Type} (join : join_of_environments A)
    : Prop :=
  ∀ (avoid : list variable) (inputs : join_inputs A) (target : Typing_env.t)
    (analysis : Analysis.t A) (x : variable) (c : const),
    join_inputs_well_formed avoid inputs ->
    uses_refine_source inputs ->
    join avoid inputs = Some (target, analysis) ->
    knows (source inputs) x ->
    (∃ (index : Index.t) (use : Typing_env.t),
       use_at inputs index use ∧ Typing_env.is_bottom use = false) ->
    (∀ (index : Index.t) (use : Typing_env.t),
       use_at inputs index use ->
       Typing_env.is_bottom use = false ->
       ∃ (level : Typing_env_level.t) (ty : flambda_type) (alias : simple),
         Typing_env.cut use (cut_after inputs) = Some level
         ∧ Keyed.lookup name_eqb (Name_var x)
             (Typing_env_level.equations level)
           = Some ty
         ∧ get_alias_opt ty = Some alias
         ∧ Typing_env.get_canonical_simple_ignoring_name_mode use alias
           = Const c) ->
    Typing_env.is_bottom target = true
    ∨ Typing_env.get_canonical_simple_ignoring_name_mode target (Var x)
      = Const c.

End Contract.

(* ======================================================================== *)
(* The join of types, inside a join of environments                         *)
(* ======================================================================== *)

(* The functions that join types (meet_and_n_way_join.ml) thread the
   state of the join of environments ([Join_env.t]) and are given, for
   each type, the index of the environment in which it holds. What they
   need of that state is here as two readings of it: the environment of
   an index ([Join_env.joined_env]) and the definitions of the
   existential variables made so far. The contract below is what the
   join of environments assumes of the join of types that it is given
   ([n_way_join_type] in join_env.ml), and what the functions of the
   environment that the join of types calls must meet in their turn. *)
Section Join_of_types.

Context {state : Type}
  (joined_env : state -> Index.t -> option Typing_env.t)
  (definitions_of_existentials :
     state -> finite_map (Simples_in_joined_envs.t * flambda_kind)).

(* A valuation of the target extends a valuation of the input of index
   [index], as far as the state has fixed: it agrees on what that input
   knows, and the existential variables made so far have the values of
   their definitions there. *)
Definition extends_input (s : state) (index : Index.t)
    (valuation valuation' : env) : Prop :=
  ∃ use : Typing_env.t,
    joined_env s index = Some use
    ∧ agrees_on_known use valuation valuation'
    ∧ definitions_hold (definitions_of_existentials s) index valuation
        valuation'.

(* A step of the join keeps the inputs and the definitions made. *)
Definition state_grows (s s' : state) : Prop :=
  (∀ index : Index.t, joined_env s' index = joined_env s index)
  ∧ ∀ (x : variable) (definition : Simples_in_joined_envs.t * flambda_kind),
      lookup x (definitions_of_existentials s) = Some definition ->
      lookup x (definitions_of_existentials s') = Some definition.

(* The join of types: [Meet_and_n_way_join.n_way_join]. If it answers a
   type, then at each input a value of that input's type, under a
   valuation that satisfies the input, has the type answered under any
   valuation of the target that extends it. Unknown says nothing. *)
Definition n_way_join_type_sound
    (n_way_join :
       state -> list (Index.t * flambda_type)
       -> option (Or_unknown.t flambda_type * state)) : Prop :=
  ∀ (s s' : state) (ts : list (Index.t * flambda_type))
    (result : Or_unknown.t flambda_type),
    n_way_join s ts = Some (result, s') ->
    state_grows s s'
    ∧ ∀ (ty : flambda_type) (index : Index.t) (t_index : flambda_type)
        (use : Typing_env.t) (statics : static_env)
        (valuation valuation' : env) (v : value),
        result = Or_unknown.Known ty ->
        In (index, t_index) ts ->
        joined_env s' index = Some use ->
        typing_env_satisfied_strictly statics valuation use ->
        extends_input s' index valuation valuation' ->
        type_satisfied statics valuation v t_index ->
        type_satisfied statics valuation' v ty.

(* The join of [Simple]s: [Join_env.n_way_join_simples]. The [Simple]
   answered has, in the target, the value that each [Simple] given has
   in its input. *)
Definition n_way_join_simples_sound
    (n_way_join_simples :
       state -> flambda_kind -> list (Index.t * simple)
       -> option (Or_bottom.t simple * state)) : Prop :=
  ∀ (s s' : state) (kind : flambda_kind) (simples : list (Index.t * simple))
    (result : Or_bottom.t simple),
    n_way_join_simples s kind simples = Some (result, s') ->
    state_grows s s'
    ∧ ∀ (joined : simple) (index : Index.t) (simple : simple)
        (use : Typing_env.t) (statics : static_env)
        (valuation valuation' : env),
        result = Or_bottom.Ok joined ->
        In (index, simple) simples ->
        joined_env s' index = Some use ->
        typing_env_satisfied_strictly statics valuation use ->
        extends_input s' index valuation valuation' ->
        eval_simple valuation' joined = eval_simple valuation simple.

End Join_of_types.

(* ======================================================================== *)
(* Statements that do not need the functions                                *)
(* ======================================================================== *)

(* The contract is not empty: the join that answers the source, and an
   analysis that says nothing, meets it. *)
Definition join_to_source_sound_statement : Prop :=
  ∀ (typing_env_well_formed : Typing_env.t -> Prop) (A : Type),
    sound_join_of_environments typing_env_well_formed
      (fun (_ : list variable) (inputs : join_inputs A) =>
         Some (source inputs, Analysis.empty)).

(* And it is not met by everything: the join that answers a bottom
   environment does not meet it. *)
Definition join_to_bottom_unsound_statement : Prop :=
  ~ sound_join_of_environments (fun _ : Typing_env.t => True)
      (fun (_ : list variable) (inputs : join_inputs unit) =>
         Some (Typing_env.make_bottom (source inputs), Analysis.empty)).

(* In the machine. If the target admits a use, and every variable that
   may occur in terms in the target may occur in terms at the use, then
   a state of the machine that satisfies the use satisfies the target;
   and the valuation that shows it gives each variable with a
   definition at that use, by a [Simple] that may occur in terms there,
   the value that the machine has for that [Simple]. The last part is
   what entitles Simplify to add a parameter for such a variable and to
   pass that [Simple] for it at the use (join_points.ml,
   [add_extra_params_from_join_analysis]). *)
Definition join_admits_use_in_machine_statement : Prop :=
  ∀ (use target : Typing_env.t)
    (definitions definitions_at_normal_mode
       : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) (statics : static_env) (vars : env),
    join_admits_use use target definitions definitions_at_normal_mode index ->
    (∀ x : variable, in_scope_in_terms target x -> in_scope_in_terms use x) ->
    env_satisfies_strictly use statics vars ->
    ∃ valuation' : env,
      typing_env_satisfied_strictly statics valuation' target
      ∧ agrees_in_terms target valuation' vars
      ∧ (∀ x : variable, in_scope_in_terms target x -> lookup x vars <> None)
      ∧ ∀ (x : variable) (simples : Simples_in_joined_envs.t)
          (kind : flambda_kind) (simple : simple),
          lookup x definitions_at_normal_mode = Some (simples, kind) ->
          Simples_in_joined_envs.find index simples = Some simple ->
          Typing_env.mem_simple (Some Name_mode.normal) use simple = true ->
          lookup x valuation' = eval_simple vars simple.

Definition join_admits_use_env_satisfies_statement : Prop :=
  ∀ (use target : Typing_env.t)
    (definitions definitions_at_normal_mode
       : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) (statics : static_env) (vars : env),
    join_admits_use use target definitions definitions_at_normal_mode index ->
    (∀ x : variable, in_scope_in_terms target x -> in_scope_in_terms use x) ->
    env_satisfies_strictly use statics vars ->
    env_satisfies_strictly target statics vars.

(* What the analysis says of a value at a use: where
   [Analysis.value_at_use] answers a constant for the [Simple] that a
   variable stands for at a use, the variable holds that constant under
   the valuation of the target for that use. Unknown says nothing, and
   so does [Not_refined_at_join]. *)
Definition known_value_at_use_statement : Prop :=
  ∀ (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) (valuation valuation' : env) (x : variable)
    (simples : Simples_in_joined_envs.t) (kind : flambda_kind)
    (simple : simple) (c : const),
    definitions_hold definitions index valuation valuation' ->
    lookup x definitions = Some (simples, kind) ->
    Simples_in_joined_envs.find index simples = Some simple ->
    Analysis.value_at_use simple = Or_unknown.Known c ->
    lookup x valuation' = Some (Value_const c).

(* ======================================================================== *)
(* The n-way join of closures entries is not an upper bound                 *)
(* ======================================================================== *)

(* A closure type with one case, in which only the function types
   vary. *)
Definition closures_type_with (slot : function_slot)
    (index : row_like_index set_of_closures_contents unit)
    (closure_types value_slot_types : finite_map flambda_type)
    (function_types : finite_map (Or_unknown.t function_type))
    : flambda_type :=
  create_closures Alloc_mode.Heap
    (Row_like_for_closures
       [(slot,
         Row_like_case
           (Closures_entry function_types closure_types value_slot_types)
           index empty_env_extension)]).

(* There are two closure types that differ only in their function
   types, and a value that has the first, such that the value has not
   the type whose function types are those that the compiler's n-way
   join makes of the two. (The first says nothing of the code of the
   closure's own function, the second names a code, and the value's
   code is another.) So [n_way_join_closures_entry] does not meet
   [n_way_join_type_sound]. *)
Definition n_way_join_closures_entry_not_upper_bound_statement : Prop :=
  ∃ (statics : static_env) (vars : env) (v : value) (slot : function_slot)
    (index : row_like_index set_of_closures_contents unit)
    (closure_types value_slot_types : finite_map flambda_type)
    (function_types0 function_types1
       : finite_map (Or_unknown.t function_type)),
    type_satisfied statics vars v
      (closures_type_with slot index closure_types value_slot_types
         function_types0)
    ∧ ~ type_satisfied statics vars v
          (closures_type_with slot index closure_types value_slot_types
             (n_way_join_function_types
                [(0, function_types0); (1, function_types1)])).

(* With the change proposed, the function types joined say of the code
   of a function only what every entry says: a closures entry that
   holds with the function types of one of the entries joined holds
   with the function types joined. *)
Definition n_way_join_function_types_proposed_sound_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (v : value) (slot : function_slot)
    (functions : list (function_slot * code_id))
    (value_slots : list (value_slot * value))
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    (index : Index.t)
    (function_types : finite_map (Or_unknown.t function_type))
    (closure_types value_slot_types : finite_map flambda_type),
    In (index, function_types) entries ->
    closures_entry_satisfied statics vars v slot functions value_slots
      (Closures_entry function_types closure_types value_slot_types) ->
    closures_entry_satisfied statics vars v slot functions value_slots
      (Closures_entry (n_way_join_function_types_proposed entries)
         closure_types value_slot_types).
