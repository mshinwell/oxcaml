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
   environment of that index ([n_way_join_type_sound]); the section
   "The join of types, inside a join of environments" is the interface
   between the two halves of the transcription.

   What is guaranteed ([join_guarantees]), for a use and a valuation
   that satisfies it strictly: some valuation satisfies the target
   strictly, gives every variable that the use knows and that had a
   value that value, and gives every variable that has a definition in
   the analysis the value, at that use, of the [Simple] that the
   analysis says, if it has one. It is one valuation for the whole
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
     ([typing_env_satisfied_strictly], [env_satisfies_strictly]).
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
   - Physical equality (decision D30) is not in the model. In the three
     places where the compiler's result depends on it
     ([import_or_delay_n_way_join_of_concrete_type] and
     [n_way_join_env_extension] in join_env.ml,
     [n_way_join_int_indexed_product] in meet_and_n_way_join.ml) the
     model tests an equality of types, as the compiler does under
     -flambda2-join-sharing structural. The upper bound holds of either
     branch at each; what the test gives in precision (an extension, or
     a field, that is equal in every input is kept as it is) is to be
     stated separately, with the functions.
   - That the join answers is not promised: [None] is a fatal error of
     the compiler or the model's fuel run out.
   - Code age, allocation modes and symbol projections have no meaning
     here (FlambdaTypeMeaningSpec.v, FlambdaTypingEnv.v).

   What this contract does not yet cover of Simplify's joins. It is a
   foundation for runs in which one valuation satisfies a use and the
   source strictly, through environments that are kinded; three kinds
   of input that Simplify may make are outside it.
   - A use environment in which a parameter that holds poison has a
     type that poison has not: variant unboxing makes these (decision
     D26, discrepancy T5-7). Such a use is not satisfied strictly, and
     nothing here says that the handler's environment holds after it.
     The workstream on the unboxing of continuation parameters is to
     show what holds at a join that follows an unboxed continuation.
   - A source environment that holds the types of constants lifted in
     other branches (discrepancy T5-4): on a path that did not define
     such a symbol, no valuation satisfies the source. The workstream
     on continuations is to show, for the inputs it gives the join,
     that the valuation of a use satisfies the source too, once the
     typing environment's owner has said where the type of a symbol may
     be used (only where the symbol is bound).
   - A use environment in which an alias is at a kind that is not the
     kind that the environment has for its target ([uses_kinded] fails;
     discrepancy T5-9). Ill-kinded code can make such environments, and
     the compiler's join does not test for them where it makes a
     variable for [Simple]s of a kind. It is a premise here, not an
     invariant claimed of the compiler's inputs: whoever states the
     kinds of typing environments is to say where it holds.

   What the inputs must satisfy ([join_inputs_well_formed],
   [uses_kinded], and the source being satisfied with each use in
   [join_admits_use]), against the three hypotheses of the header of
   join_env.ml.
   - "Any name defined in the source environment is also defined in all
     the joined environments." Not required here, and not true of what
     Simplify passes: [check_join_inputs] says that the source may have
     variables in types, made when lifted constants were added to it,
     that no use has; and the second hypothesis itself says that a
     symbol lifted in one branch is not defined in the others. Nothing
     checks it. What the contract needs in its place: that the
     valuation of a use satisfies the source too (a premise of
     [join_admits_use], for each valuation: that a use entails the
     source is false even of the environments that the meet makes);
     and, for the caller to conclude of the machine,
     [terms_in_scope_at_uses] (a variable that may occur in terms in
     the source may occur in terms at each use).
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

(* The second valuation gives every variable that the use knows, and
   that has a value in the first, that value. A variable that the use
   knows and that has no value in the first may have one in the second:
   the join may make it an alias of a constant, where the use has for
   it a type that nothing has. *)
Definition agrees_on_known (use : Typing_env.t) (valuation valuation' : env)
    : Prop :=
  ∀ (x : variable) (v : value),
    knows use x -> lookup x valuation = Some v -> lookup x valuation' = Some v.

(* The second valuation gives every variable that has a definition at
   the use of index [index] the value that that definition has in the
   first, a valuation of that use, if it has one there. *)
Definition definitions_hold
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) (valuation valuation' : env) : Prop :=
  ∀ (x : variable) (simples : Simples_in_joined_envs.t) (kind : flambda_kind)
    (simple : simple) (v : value),
    lookup x definitions = Some (simples, kind) ->
    Simples_in_joined_envs.find index simples = Some simple ->
    eval_simple valuation simple = Some v ->
    lookup x valuation' = Some v.

(* The target admits a use, of index [index]: every valuation that
   satisfies the use and the source extends to one that satisfies the
   target, under which the definitions of the two maps of the analysis
   hold. *)
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
   So this contract does not cover the joins that follow an unboxed
   continuation: the workstream on the unboxing of continuation
   parameters owes the statement of what holds there (for instance
   that the environment tells which names may hold poison, and that the
   join leaves their types alone). Decision D26; discrepancy T5-7. *)
(* CR mshinwell: the valuation must satisfy the source too. That is a
   premise for each valuation, and about what the environments mean;
   the header of join_env.ml has one about the names they define, which
   is false of Simplify's inputs. It cannot be the premise that a use
   entails the source: an environment made from another by adding an
   equation does not entail it (the meet may forget what tied two
   names), though the valuation at hand satisfies both. And it may not
   hold of Simplify's joins: the source has the types of the constants
   lifted while the body of the continuation was simplified, and on a
   path that did not go through the branch that defines such a symbol
   the symbol is bound to nothing, so its type is not true there. Two
   owe it: the owner of the typing environment, to say where the type
   of a symbol may be used (facts about a symbol may have to be asked
   only where the symbol is bound); and the workstream on
   continuations, to show it of the inputs it gives the join.
   Discrepancy T5-4. *)
Definition join_admits_use (source use target : Typing_env.t)
    (definitions definitions_at_normal_mode
       : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) : Prop :=
  ∀ (statics : static_env) (valuation : env),
    typing_env_satisfied_strictly statics valuation use ->
    typing_env_satisfied_strictly statics valuation source ->
    ∃ valuation' : env,
      typing_env_satisfied_strictly statics valuation' target
      ∧ agrees_on_known use valuation valuation'
      ∧ agrees_on_known source valuation valuation'
      ∧ definitions_hold definitions index valuation valuation'
      ∧ definitions_hold definitions_at_normal_mode index valuation
          valuation'.

(* The machine satisfies a use and the source together: it binds the
   variables of terms of the use, and one valuation satisfies both
   strictly and gives those variables the values that the machine has
   for them. *)
Definition use_and_source_satisfied (source use : Typing_env.t)
    (statics : static_env) (vars : env) : Prop :=
  bound_in_terms use vars
  ∧ ∃ valuation : env,
      typing_env_satisfied_strictly statics valuation use
      ∧ typing_env_satisfied_strictly statics valuation source
      ∧ agrees_in_terms use valuation vars.

(* ======================================================================== *)
(* What the inputs must satisfy                                             *)
(* ======================================================================== *)

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

(* A variable that may occur in terms in the source may occur in terms
   at each use. The join does not need it: it is what the caller needs
   to conclude of the machine ([join_guarantees_in_machine_statement]),
   and it is what is left, for the variables of terms, of the first
   hypothesis of the header of join_env.ml. *)
Definition terms_in_scope_at_uses {A : Type} (inputs : join_inputs A)
    : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t) (x : variable),
    use_at inputs index use ->
    in_scope_in_terms (source inputs) x ->
    in_scope_in_terms use x.

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

(* A [Simple] is of a kind in an environment: the constant is of that
   kind, or the environment has a type of that kind for the name. *)
Definition simple_of_kind (tenv : Typing_env.t) (simple : simple)
    (kind : flambda_kind) : Prop :=
  match simple with
  | Const c => FlambdaTypeGrammar.kind (type_for_const c) = kind
  | Var x =>
    ∃ ty : flambda_type,
      Typing_env.find tenv (Name_var x) (Some kind) = Some ty
  | Symbol s =>
    ∃ ty : flambda_type,
      Typing_env.find tenv (Name_symbol s) (Some kind) = Some ty
  end.

(* The aliases of a type, each with the kind at which it stands, and
   the variables that hold the results of [Is_int], [Get_tag] and
   [Is_null], which are naked immediates: what the join of types gives
   the join of [Simple]s, with the kind at which it gives it. The
   recursion is that of [free_variables] (FlambdaTypeGrammar.v). *)
Definition aliases_of_descr {head : Type} (kind : flambda_kind)
    (aliases_of_head : head -> list (simple * flambda_kind))
    (ty : type_descr head) : list (simple * flambda_kind) :=
  match ty with
  | Ok (No_alias head) => aliases_of_head head
  | Ok (Equals s) => [(s, kind)]
  | Unknown | Bottom => []
  end.

Definition aliases_of_relation (x : option variable)
    : list (simple * flambda_kind) :=
  match x with
  | Some x => [(Var x, Naked_number Kind_naked_immediate)]
  | None => []
  end.

(* The two arguments stand for the functions being defined below. *)
Definition aliases_of_block_case
    (aliases_with_kinds : flambda_type -> list (simple * flambda_kind))
    (aliases_of_env_extension : env_extension -> list (simple * flambda_kind))
    (case : row_like_block_case) : list (simple * flambda_kind) :=
  flat_map aliases_with_kinds (case_maps_to case)
  ++ aliases_of_env_extension (case_env_extension case).

Fixpoint aliases_with_kinds (t : flambda_type)
    : list (simple * flambda_kind) :=
  match t with
  | Type_value ty =>
    aliases_of_descr Value aliases_of_head_of_kind_value ty
  | Type_naked_immediate ty =>
    aliases_of_descr (Naked_number Kind_naked_immediate) (fun _ => []) ty
  | Type_naked_number k ty =>
    aliases_of_descr (Naked_number k) (fun _ => []) ty
  | Type_rec_info ty => aliases_of_descr Rec_info (fun _ => []) ty
  | Type_region ty => aliases_of_descr Region (fun _ => []) ty
  end

with aliases_of_head_of_kind_value (head : head_of_kind_value)
    : list (simple * flambda_kind) :=
  match head with
  | Head_of_kind_value non_null is_null =>
    match non_null with
    | Ok head => aliases_of_head_of_kind_value_non_null head
    | Unknown | Bottom => []
    end
    ++ match is_null with
       | Not_null => []
       | Maybe_null is_null => aliases_of_relation is_null
       end
  end

with aliases_of_head_of_kind_value_non_null
    (head : head_of_kind_value_non_null) : list (simple * flambda_kind) :=
  match head with
  | Variant is_int immediates get_tag blocks extensions _ =>
    aliases_of_relation is_int
    ++ match immediates with
       | Or_unknown.Known ty => aliases_with_kinds ty
       | Or_unknown.Unknown => []
       end
    ++ aliases_of_relation get_tag
    ++ match blocks with
       | Or_unknown.Known blocks => aliases_of_row_like_for_blocks blocks
       | Or_unknown.Unknown => []
       end
    ++ match extensions with
       | No_extensions => []
       | Ext when_immediate when_block =>
         aliases_of_env_extension when_immediate
         ++ aliases_of_env_extension when_block
       end
  | Mutable_block _ | String _ => []
  | Boxed_number _ contents _ => aliases_with_kinds contents
  | Closures by_function_slot _ =>
    aliases_of_row_like_for_closures by_function_slot
  end

with aliases_of_row_like_for_blocks (blocks : row_like_for_blocks)
    : list (simple * flambda_kind) :=
  match blocks with
  | Row_like_for_blocks known_tags other_tags _ =>
    flat_map
      (fun case =>
         match snd case with
         | Or_unknown.Known case =>
           aliases_of_block_case aliases_with_kinds aliases_of_env_extension
             case
         | Or_unknown.Unknown => []
         end)
      known_tags
    ++ match other_tags with
       | Or_bottom.Ok case =>
         aliases_of_block_case aliases_with_kinds aliases_of_env_extension
           case
       | Or_bottom.Bottom => []
       end
  end

with aliases_of_row_like_for_closures (closures : row_like_for_closures)
    : list (simple * flambda_kind) :=
  match closures with
  | Row_like_for_closures known_closures =>
    flat_map
      (fun case =>
         aliases_of_closures_entry (case_maps_to (snd case))
         ++ aliases_of_env_extension (case_env_extension (snd case)))
      known_closures
  end

with aliases_of_closures_entry (entry : closures_entry)
    : list (simple * flambda_kind) :=
  match entry with
  | Closures_entry _ closure_types value_slot_types =>
    flat_map (fun binding => aliases_with_kinds (snd binding)) closure_types
    ++ flat_map (fun binding => aliases_with_kinds (snd binding))
         value_slot_types
  end

with aliases_of_env_extension (extension : env_extension)
    : list (simple * flambda_kind) :=
  match extension with
  | Env_extension equations =>
    flat_map (fun binding => aliases_with_kinds (snd binding)) equations
  end.

(* A type is kinded in an environment: each of its aliases is at the
   kind that the environment has for its target, and its relation
   variables are naked immediates there. *)
Definition type_kinded (tenv : Typing_env.t) (ty : flambda_type) : Prop :=
  ∀ (s : simple) (kind : flambda_kind),
    (s, kind) ∈ aliases_with_kinds ty -> simple_of_kind tenv s kind.

(* An environment is kinded: every type that it has for a name is. *)
(* CR mshinwell: this is asked of every use environment, as a premise
   of the contract ([uses_kinded]); it is not claimed that the compiler's
   environments have it. A type does not say at which kind the target
   of an alias is bound, the well-formedness of types leaves it out on
   purpose, and ill-kinded code (which Simplify must accept: decisions
   D10 and D12) may give a name an alias at another kind. The compiler's
   join makes a variable of the kind of the types joined for the
   [Simple]s that they are aliases to, and does not look at their
   kinds. It stops later with a fatal error if they differ, when it
   looks the [Simple]s up at that kind
   ([find_simples_in_joined_envs], through [Typing_env.find]) or meets
   the type joined with that of the variable; unless the depth limit of
   the join is reached first, and then it answers an environment in
   which the variable is of one kind and stands, at a use, for a
   [Simple] of another, and an analysis that says so. The model's
   function answers what the compiler answers. Whether an environment
   that is not kinded can reach a join is not known. Discrepancy
   T5-9. *)
Definition typing_env_kinded (tenv : Typing_env.t) : Prop :=
  ∀ (n : name) (ty : flambda_type)
    (binding_time_and_mode : Binding_time.With_name_mode.t),
    Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
    = Some (ty, binding_time_and_mode) ->
    type_kinded tenv ty.

Definition uses_kinded {A : Type} (inputs : join_inputs A) : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t),
    use_at inputs index use -> typing_env_kinded use.

(* What the analysis speaks of. Its identifiers are those of uses that
   are not bottom, by index. A definition is of a variable that the
   target has, with the kind given, at a use with an identifier, and is
   a [Simple] of that kind in that use; a definition at the normal name
   mode is moreover a [Simple] that may occur in terms at that use.
   (Simplify makes a parameter of the kind given and passes the
   [Simple] for it.) *)
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
       simple_of_kind target (Var x) kind
       ∧ ∃ (id : A) (use : Typing_env.t),
           nth_error (uses inputs) index = Some (id, use)
           ∧ Keyed.lookup Index.equal index (Analysis.external_ids analysis)
             = Some id
           ∧ simple_of_kind use simple kind)
  ∧ (∀ (x : variable) (simples : Simples_in_joined_envs.t)
       (kind : flambda_kind) (index : Index.t) (simple : simple),
       lookup x (Analysis.canonical_definitions_at_normal_mode analysis)
       = Some (simples, kind) ->
       Simples_in_joined_envs.find index simples = Some simple ->
       simple_of_kind target (Var x) kind
       ∧ ∃ (id : A) (use : Typing_env.t),
           nth_error (uses inputs) index = Some (id, use)
           ∧ Keyed.lookup Index.equal index (Analysis.external_ids analysis)
             = Some id
           ∧ simple_of_kind use simple kind
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
       join_admits_use (source inputs) use target
         (Analysis.definitions_in_joined_envs analysis)
         (Analysis.canonical_definitions_at_normal_mode analysis) index).

(* The contract of a join of environments. *)
Definition sound_join_of_environments {A : Type}
    (join : join_of_environments A) : Prop :=
  ∀ (avoid : list variable) (inputs : join_inputs A) (target : Typing_env.t)
    (analysis : Analysis.t A),
    join_inputs_well_formed avoid inputs ->
    uses_kinded inputs ->
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
    uses_kinded inputs ->
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

(* This section is the interface between the two halves of the
   transcription. The functions that join types (the join functions of
   meet_and_n_way_join.ml, in FlambdaJoinTypes.v) thread the state of
   the join of environments ([Join_env.t], in FlambdaJoinEnv.v) and are
   given, for each type, the index of the environment in which it
   holds. They call four functions of the environment side:
   [Join_env.joined_env], [n_way_join_simples], [import_type] and
   [n_way_join_env_extension]; and the environment side calls the join
   of types, which it is given as an argument ([n_way_join_type]).

   Neither half sees the other's definitions. The state is any type
   with three readings: the environment of an index ([joined_env]), the
   definitions of the existential variables made so far, and the
   variables that exist in the target so far (those of the source, the
   imported ones and the existential ones:
   [Bindings_in_target_env.exists_in_target_env]); and with an
   invariant, [state_valid], which is the environment side's and of
   which the join of types knows only that the four functions keep it.
   The four contracts below are what each half proves of its functions
   and assumes of the other's. Each is in three parts: the invariant is
   kept; the upper bound, under any valuation of the target that
   extends that of the input; and scope, that what is answered mentions
   only variables of the target.

   The upper bounds speak of every valuation that extends that of an
   input. That there is one is asked of the invariant
   ([valid_states_have_witnesses]): it is where it is shown that the
   variables that the join makes are new and that each has one
   definition. Without it a step could add definitions that nothing
   meets, and its upper bound would say nothing.

   Every function is given types, [Simple]s and extensions that mention
   only variables that the environment of their index knows
   ([join_args_in_scope]): the environment side gives the types that an
   input has for a name, and the join of types passes on their
   components and what [Expand_head] answers in that environment. Each
   index is given once ([join_args_distinct]). And the types given are
   kinded in the environment of their index ([type_kinded]), so that
   each [Simple] given to the join of [Simple]s is of the kind given:
   the components of a kinded type are kinded, by the definition of
   [aliases_with_kinds], and what [Expand_head] answers is kinded where
   the environment is ([joined_envs_kinded]). *)
Section Join_of_types.

Context (typing_env_well_formed : Typing_env.t -> Prop).

Context {state : Type}
  (joined_env : state -> Index.t -> option Typing_env.t)
  (definitions_of_existentials :
     state -> finite_map (Simples_in_joined_envs.t * flambda_kind))
  (exists_in_target_env : state -> variable -> bool)
  (state_valid : state -> Prop).

(* The environments joined are well formed. *)
Definition joined_envs_well_formed (s : state) : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t),
    joined_env s index = Some use -> typing_env_well_formed use.

(* The environments joined are kinded. (The join of types needs it of
   the types that it expands in them.) *)
Definition joined_envs_kinded (s : state) : Prop :=
  ∀ (index : Index.t) (use : Typing_env.t),
    joined_env s index = Some use -> typing_env_kinded use.

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

(* What the environment side must prove of its invariant: at a valid
   state, every valuation that satisfies an input extends to a
   valuation of the target. *)
Definition valid_states_have_witnesses : Prop :=
  ∀ (s : state) (index : Index.t) (use : Typing_env.t)
    (statics : static_env) (valuation : env),
    state_valid s ->
    joined_env s index = Some use ->
    typing_env_satisfied_strictly statics valuation use ->
    ∃ valuation' : env, extends_input s index valuation valuation'.

(* A step of the join keeps the inputs, the definitions made and the
   variables of the target. *)
Definition state_grows (s s' : state) : Prop :=
  (∀ index : Index.t, joined_env s' index = joined_env s index)
  ∧ (∀ (x : variable)
       (definition : Simples_in_joined_envs.t * flambda_kind),
       lookup x (definitions_of_existentials s) = Some definition ->
       lookup x (definitions_of_existentials s') = Some definition)
  ∧ ∀ x : variable,
      exists_in_target_env s x = true -> exists_in_target_env s' x = true.

(* What is given mentions only variables that an environment knows. *)
Definition simple_in_scope (tenv : Typing_env.t) (simple : simple) : Prop :=
  ∀ x : variable, x ∈ free_variables_of_simple simple -> knows tenv x.

Definition type_in_scope (tenv : Typing_env.t) (ty : flambda_type) : Prop :=
  ∀ x : variable, x ∈ free_variables ty -> knows tenv x.

Definition env_extension_in_scope (tenv : Typing_env.t)
    (extension : env_extension) : Prop :=
  ∀ x : variable,
    x ∈ free_variables_of_env_extension extension -> knows tenv x.

(* Each thing given is in the scope of the environment of its index. *)
Definition join_args_in_scope {X : Type}
    (in_scope : Typing_env.t -> X -> Prop) (s : state)
    (args : list (Index.t * X)) : Prop :=
  ∀ (index : Index.t) (x : X),
    In (index, x) args ->
    ∃ use : Typing_env.t, joined_env s index = Some use ∧ in_scope use x.

(* Each index is given once. The environment side gives the bindings of
   a map from indices; the join of types passes on, for a component, at
   most one thing for each element of a list that it was given, so its
   lists keep this. (The join of [Simple]s makes a map of its list:
   of two [Simple]s at one index it would keep one, and could not be an
   upper bound of both.) *)
Definition join_args_distinct {X : Type} (args : list (Index.t * X)) : Prop :=
  NoDup (map fst args).

(* What is answered mentions only variables of the target. *)
Definition simple_in_target (s : state) (simple : simple) : Prop :=
  ∀ x : variable,
    x ∈ free_variables_of_simple simple -> exists_in_target_env s x = true.

Definition type_in_target (s : state) (ty : flambda_type) : Prop :=
  ∀ x : variable, x ∈ free_variables ty -> exists_in_target_env s x = true.

Definition env_extension_in_target (s : state) (extension : env_extension)
    : Prop :=
  ∀ x : variable,
    x ∈ free_variables_of_env_extension extension ->
    exists_in_target_env s x = true.

(* The join of types: [Meet_and_n_way_join.n_way_join]. If it answers a
   type, then at each input a value of that input's type, under a
   valuation that satisfies the input, has the type answered under any
   valuation of the target that extends it. Unknown says nothing. This
   is what the join of types is to be proved to meet, and what the join
   of environments assumes of the one it is given. *)
Definition n_way_join_type_sound
    (n_way_join :
       state -> list (Index.t * flambda_type)
       -> option (Or_unknown.t flambda_type * state)) : Prop :=
  ∀ (s s' : state) (ts : list (Index.t * flambda_type))
    (result : Or_unknown.t flambda_type),
    state_valid s ->
    joined_envs_well_formed s ->
    joined_envs_kinded s ->
    join_args_distinct ts ->
    join_args_in_scope type_in_scope s ts ->
    join_args_in_scope type_kinded s ts ->
    n_way_join s ts = Some (result, s') ->
    state_valid s'
    ∧ state_grows s s'
    ∧ ∀ ty : flambda_type,
        result = Or_unknown.Known ty ->
        type_in_target s' ty
        ∧ ∀ (index : Index.t) (t_index : flambda_type)
            (use : Typing_env.t) (statics : static_env)
            (valuation valuation' : env) (v : value),
            In (index, t_index) ts ->
            joined_env s' index = Some use ->
            typing_env_satisfied_strictly statics valuation use ->
            extends_input s' index valuation valuation' ->
            type_satisfied statics valuation v t_index ->
            type_satisfied statics valuation' v ty.

(* The join of [Simple]s: [Join_env.n_way_join_simples]. The [Simple]
   answered has, in the target, the value that each [Simple] given has
   in its input, where it has one. Bottom is answered only for no
   [Simple]. *)
(* CR mshinwell: each [Simple] given must be of the kind given, in the
   environment of its index. The compiler's function is not given
   this, and does not test it: it makes a variable of the kind for the
   [Simple]s, whatever their kinds (see [typing_env_kinded] for when it
   stops later and when it does not). The join of types gets the
   premise from the types that it is given being kinded
   ([n_way_join_type_sound]), and those from the use environments being
   kinded ([uses_kinded]). Decisions D10 and D12; discrepancy T5-9. *)
Definition n_way_join_simples_sound
    (n_way_join_simples :
       state -> flambda_kind -> list (Index.t * simple)
       -> option (Or_bottom.t simple * state)) : Prop :=
  ∀ (s s' : state) (kind : flambda_kind) (simples : list (Index.t * simple))
    (result : Or_bottom.t simple),
    state_valid s ->
    joined_envs_well_formed s ->
    join_args_distinct simples ->
    join_args_in_scope (fun use simple => simple_of_kind use simple kind) s
      simples ->
    n_way_join_simples s kind simples = Some (result, s') ->
    state_valid s'
    ∧ state_grows s s'
    ∧ (result = Or_bottom.Bottom -> simples = [])
    ∧ ∀ joined : simple,
        result = Or_bottom.Ok joined ->
        simple_in_target s' joined
        ∧ ∀ (index : Index.t) (simple : simple) (use : Typing_env.t)
            (statics : static_env) (valuation valuation' : env) (v : value),
            In (index, simple) simples ->
            joined_env s' index = Some use ->
            typing_env_satisfied_strictly statics valuation use ->
            extends_input s' index valuation valuation' ->
            eval_simple valuation simple = Some v ->
            eval_simple valuation' joined = Some v.

(* [Join_env.import_type]: the variables of a type become variables of
   the target. The join of types calls it on a type that it puts in its
   answer as it stands. Nothing is said of values: a type means the
   same under a valuation of the target that extends that of an input
   whose environment knows its variables ([agrees_on_known]). *)
Definition import_type_sound
    (import_type : state -> flambda_type -> option state) : Prop :=
  ∀ (s s' : state) (ty : flambda_type),
    state_valid s ->
    joined_envs_well_formed s ->
    import_type s ty = Some s' ->
    state_valid s' ∧ state_grows s s' ∧ type_in_target s' ty.

(* The join of environment extensions:
   [Join_env.n_way_join_env_extension]. The extension answered holds, in
   the target, wherever one of the extensions given holds in its input.
   Bottom is answered only for no extension. (The compiler's function
   also takes the join of types and the meet, and uses neither.) *)
Definition n_way_join_env_extension_sound
    (n_way_join_env_extension :
       state -> list (Index.t * env_extension)
       -> option (Or_bottom.t (env_extension * state))) : Prop :=
  ∀ (s : state) (extensions : list (Index.t * env_extension))
    (result : Or_bottom.t (env_extension * state)),
    state_valid s ->
    joined_envs_well_formed s ->
    join_args_distinct extensions ->
    join_args_in_scope env_extension_in_scope s extensions ->
    n_way_join_env_extension s extensions = Some result ->
    (result = Or_bottom.Bottom -> extensions = [])
    ∧ ∀ (joined : env_extension) (s' : state),
        result = Or_bottom.Ok (joined, s') ->
        state_valid s'
        ∧ state_grows s s'
        ∧ env_extension_in_target s' joined
        ∧ ∀ (index : Index.t) (extension : env_extension)
            (use : Typing_env.t) (statics : static_env)
            (valuation valuation' : env),
            In (index, extension) extensions ->
            joined_env s' index = Some use ->
            typing_env_satisfied_strictly statics valuation use ->
            extends_input s' index valuation valuation' ->
            env_extension_satisfied statics valuation extension ->
            env_extension_satisfied statics valuation' joined.

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
   a state of the machine that satisfies the use and the source
   satisfies the target; and the valuation that shows it gives each
   variable with a definition at that use, by a [Simple] that may occur
   in terms there, the value that the machine has for that [Simple].
   The last part is what entitles Simplify to add a parameter for such
   a variable and to pass that [Simple] for it at the use
   (join_points.ml, [add_extra_params_from_join_analysis]). *)
Definition join_admits_use_in_machine_statement : Prop :=
  ∀ (source use target : Typing_env.t)
    (definitions definitions_at_normal_mode
       : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) (statics : static_env) (vars : env),
    join_admits_use source use target definitions definitions_at_normal_mode
      index ->
    (∀ x : variable, in_scope_in_terms target x -> in_scope_in_terms use x) ->
    use_and_source_satisfied source use statics vars ->
    ∃ valuation' : env,
      typing_env_satisfied_strictly statics valuation' target
      ∧ agrees_in_terms target valuation' vars
      ∧ bound_in_terms target vars
      ∧ ∀ (x : variable) (simples : Simples_in_joined_envs.t)
          (kind : flambda_kind) (simple : simple),
          lookup x definitions_at_normal_mode = Some (simples, kind) ->
          Simples_in_joined_envs.find index simples = Some simple ->
          Typing_env.mem_simple (Some Name_mode.normal) use simple = true ->
          lookup x valuation' = eval_simple vars simple.

Definition join_admits_use_env_satisfies_statement : Prop :=
  ∀ (source use target : Typing_env.t)
    (definitions definitions_at_normal_mode
       : finite_map (Simples_in_joined_envs.t * flambda_kind))
    (index : Index.t) (statics : static_env) (vars : env),
    join_admits_use source use target definitions definitions_at_normal_mode
      index ->
    (∀ x : variable, in_scope_in_terms target x -> in_scope_in_terms use x) ->
    use_and_source_satisfied source use statics vars ->
    env_satisfies_strictly target statics vars.

(* The same of a join that meets the contract: if a variable that may
   occur in terms in the source may occur in terms at each use, a state
   of the machine that satisfies a use and the source satisfies the
   target. *)
Definition join_guarantees_in_machine_statement : Prop :=
  ∀ (typing_env_well_formed : Typing_env.t -> Prop) (A : Type)
    (avoid : list variable) (inputs : join_inputs A) (target : Typing_env.t)
    (analysis : Analysis.t A) (index : Index.t) (use : Typing_env.t)
    (statics : static_env) (vars : env),
    join_guarantees typing_env_well_formed avoid inputs target analysis ->
    terms_in_scope_at_uses inputs ->
    use_at inputs index use ->
    use_and_source_satisfied (source inputs) use statics vars ->
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

(* What the two lists that Simplify folds over hold
   ([Analysis.values_at_uses], [Analysis.definitions_at_uses]): each
   element is the identifier of an index and what the vector has at
   that index, so what is said above of a definition at an index is
   true of each element. *)
Definition values_at_uses_found_statement : Prop :=
  ∀ (A : Type) (external_ids : Keyed.finite_map Index.t A)
    (simples : Simples_in_joined_envs.t)
    (values : list (A * Or_unknown.t const)) (id : A)
    (value : Or_unknown.t const),
    Analysis.values_at_uses external_ids simples = Some values ->
    In (id, value) values ->
    ∃ (index : Index.t) (simple : simple),
      Keyed.lookup Index.equal index external_ids = Some id
      ∧ Simples_in_joined_envs.find index simples = Some simple
      ∧ value = Analysis.value_at_use simple.

Definition definitions_at_uses_found_statement : Prop :=
  ∀ (A : Type) (external_ids : Keyed.finite_map Index.t A)
    (simples : Simples_in_joined_envs.t) (definitions : list (A * simple))
    (id : A) (simple : simple),
    Analysis.definitions_at_uses external_ids simples = Some definitions ->
    In (id, simple) definitions ->
    ∃ index : Index.t,
      Keyed.lookup Index.equal index external_ids = Some id
      ∧ Simples_in_joined_envs.find index simples = Some simple.

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
