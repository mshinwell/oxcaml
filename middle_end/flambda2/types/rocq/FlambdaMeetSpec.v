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



(* What the meet of two Flambda types guarantees: the contract.

   This file is to be reviewed: what is asked of the inputs of a meet
   ([meet_inputs_well_formed]), the contracts [meet_sound],
   [add_equation_sound], [meet_expanded_head_sound] and
   [join_scoped_envs_sound], and the statements at the end. It is
   written before the functions. A contract here is a proposition about
   a function of the type that the compiler's function has; that the
   transcribed functions have their contracts is to be stated, with
   them, in the form of [transcription_sound]. The statements that are
   closed are proved in FlambdaMeetProofs.v.

   The compiler. middle_end/flambda2/types/meet_and_n_way_join.ml (the
   33 functions from [meet] to [meet_function_type], and the helpers
   before them), types/meet.ml, types/env/meet_env.ml,
   types/expand_head.ml, and flambda2_types.ml for
   [Typing_env.add_equation]. The compiler has a second file with a
   meet, types/meet_and_join.ml, the one it runs by default. The two
   have the same 33 functions but for the join that four of them call,
   and two helpers that differ, [meet_disjunction] and [meet_row_like],
   which join the environments of the alternatives of a disjunction.
   So there is one contract, here; the traversal is to be transcribed
   once, with that join as a parameter ([join_scoped_envs]); and it is
   instantiated first with the n-way join, which is another
   workstream's (T5). The other file is not the reference.

   The contract, in short ([meet_sound]). [meet tenv t1 t2] answers
   bottom, or a type [t] and an environment [tenv'], which is [tenv]
   with equations added and variables defined. If a valuation
   satisfies [tenv] and gives a value [v] both the types [t1] and
   [t2], then:
   - the answer is not bottom. So bottom is answered only if no value
     has both types under any valuation that satisfies the environment
     ([meet_bottom_sound]);
   - some valuation satisfies [tenv'], gives [v] the type [t], and
     agrees with the first on every variable that [tenv] knows. The
     variables that [tenv'] knows and [tenv] does not are those that
     the meet defined; the valuation may give each a value, and one
     valuation accounts for all the equations that the meet added.
   What is known is kept and what is new is true. Nothing is said of
   how much the meet knows: see "Precision" below.

   What satisfies an environment. The contracts are about
   [typing_env_satisfied_strictly]: every name that has a value in the
   valuation has the type that the environment gives it, and aliases
   have the same value. It differs in two ways from
   [typing_env_satisfied] of FlambdaTypingEnvSpec.v as it is on this
   branch, which asks nothing of the type of a name whose value is
   poison (decision D26) and gives every name a value. Both were agreed
   with T2 and T5; the notion is T2's, and is being added to
   FlambdaTypingEnvSpec.v under this name. The definition here stands
   in for it and goes when T2's is on this branch.
   - Poison is a value like another. A meet reads the types of names:
     of the name that a type is an alias to, of the name of which a
     number is the result of a relation, of the names of an environment
     extension. If such a name holds poison and its type is not true of
     poison, the meet deduces from a type that does not hold. Example:
     [x] holds poison and the environment has [x : null]. The value
     poison has the types [= x] and [any_non_null_value], and their
     meet is bottom. With [x] and [y] holding poison,
     [x : Variant (is_int = z)], [y : Variant (is_int = z')], [z]
     holding 1 and [z'] holding 0, the meet of [= x] and [= y], both
     of which poison has, makes [z] and [z'] aliases. And the name
     need not be the one that an equation is added to: it may be
     reached through a field. So the
     premise "the value of the name is not poison" on the name of
     [add_equation] is not enough, and the contracts ask that every
     name has its type. A name may hold poison if its type is true of
     poison (the unknown type is). There is a CR at
     [typing_env_satisfied_strictly] and one at [add_equation_sound].
   - A name may have no value. The n-way join defines, in the
     environment that it answers, variables that come from one of the
     environments joined, with the types they have there. Under a
     valuation of another of the environments joined no value need
     have such a type. Such a variable has no value then, and nothing
     is asked of it. A type that mentions it in a place that counts
     (an alias to it, a relation to it) has no value either
     (FlambdaTypeMeaningSpec.v), so a meet never reads the type of a
     name with no value on behalf of a value that it has in hand. The
     variable is mentioned only in what is dead under that valuation:
     the case of another tag, the other side of a variant.
   An environment that is satisfied as FlambdaTypingEnvSpec.v says, by
   a valuation that gives poison to none of its names, is satisfied
   strictly ([satisfied_no_poison_statement]). The environment of a
   handler whose parameters unboxing gives poison to on some paths is
   not, on those paths: the contracts say nothing there.

   What is asked of the inputs ([meet_inputs_well_formed]).
   - The two types have one kind. A meet of types of two kinds is a
     fatal error of the compiler ([Meet_env.meet]: "Kind mismatch upon
     meet"), never bottom; a fatal error is [None] here
     ([meet_kinds]). An environment that is bottom is tested for first,
     and then the answer is bottom whatever the kinds
     ([meet_bottom_env]).
   - The types, and the types of the environment, are well formed:
     [type_well_formed], which is T1's to define
     (FlambdaTypeWellFormedSpec.v, not there yet) and is a parameter of
     the contracts until it is. What meet needs of it, as agreed with
     T1: (a) the product of a case of blocks is no wider than the size
     of its index; (b) the function types, the closure types and the
     value slot types of a case of closures are of slots among those of
     its index, and an exact index has the slot of the case among its
     closures; (c) a shape is written in one way; (d) the kinds: the
     immediates of a variant are of kind naked immediate, the contents
     of a boxed number of the kind boxed, the closure types of kind
     value, the fields of a block of the kinds of its shape; (e) a set
     of numbers that is a head is not empty ([set_meet] answers one of
     its inputs where one set is included in the other, so an empty
     set would come back as an answer that is not bottom); (f) no type
     is an alias to a poison constant ([Relation.of_const] reads
     [Is_int] of one as 1, and the relation says nothing of poison).
     The compiler's creation functions give (a) to (e) under
     preconditions that not all of them check, and its raw constructors
     check nothing (discrepancy T1-5). The n-way join does not keep
     (b): it keeps a function type under an index that does not say
     that the set has the function (T1-4). On such a type the meet
     answers bottom for two function types of one slot with different
     code, and a closure of a set without that slot has both types
     (discrepancy T4-3).
   - The variables that the types mention are known to the environment
     ([type_fits]). (Symbols too; [free_variables] has the variables
     only, and T1 is adding the names.)
   - The environment is well formed: [typing_env_well_formed], which
     is T2's to define (its second request) and is a parameter until it
     is: binding times, levels and scopes, the aliases.
   The answer is well formed in the same sense and of the kind of the
   inputs, and the environment answered knows what the first knew
   ([meet_keeps_well_formed]), so that a meet can follow a meet.

   The join that meet is given ([join_scoped_envs_sound]). It is
   [Join_env.cut_and_n_way_join] with its [n_way_join_type], called
   by [meet_disjunction] (the two sides of a variant, and a value that
   may be null) and by [meet_row_like] (the cases of a row-like
   structure): each alternative is met in an environment of its own,
   one scope further than the environment of the meet, and the join
   makes of these one environment. It is given the meet of expanded
   types as an argument, and its contract supposes that this argument
   has its own ([meet_expanded_head_sound]). What is asked, as agreed
   with T5 (its contract is FlambdaJoinSpec.v):
   - a valuation that satisfies one of the environments joined extends
     to one that satisfies the result, and agrees with it on every
     variable that the environment joined knows; one valuation for all
     that the join defines. The variables that the result takes from
     the other environments joined may have no value in it;
   - the result is the first environment with equations and
     definitions added: its scope, its earlier levels and what it knew
     are unchanged ([meet_env_extends]);
   - a variable that the result knows and that none of the environments
     given knows is new: it is not among the names to avoid
     ([Meet_env.names_to_avoid]). Nothing else is said of the variables
     made: not which, nor in what order. Meet itself makes no variable;
     it defines again, in the result, the variables that the
     alternatives defined (see "Known differences");
   - the result is well formed.
   Meet gives the join environments that it made from the first by
   adding definitions and equations ([scoped_env_of]).

   Code ids. A function type names its code exactly
   (FlambdaTypeMeaningSpec.v); the code age relation is not in the
   model's environment. So the model's [meet_code_id] is to answer
   bottom for two different code ids, which is right for that meaning
   where the set has the function (condition (b) above). The compiler
   answers the newer of the two if one is a later version of the other
   ([Code_age_relation.meet]), and either input if it cannot tell. The
   contract claims nothing of that: the model and the compiler part
   ways on two code ids that the relation relates, and the differential
   tests are to leave those inputs out or expect the difference
   (discrepancy T4-4). A claim that the code named by a meet is the
   code of the closure at run time needs code age (workstream S4).

   Allocation modes and uniqueness mean nothing in the meaning of
   types, so the contract says nothing of [meet_alloc_mode] or of
   [is_unique]. They are to be transcribed as they are.

   Physical equality. The compiler's meet answers [Left_input],
   [Right_input] or [Both_inputs] so as to give back an input unchanged
   and keep sharing; [meet_inverse_relations] tests [==] as a shortcut.
   Neither changes which type is answered. The model has no physical
   equality (decision D30): the transcription is to follow the slow
   path, and the contract is about the type answered, by
   [extract_value].

   Precision. The contract says that a meet loses no value. It does
   not say that the type answered has no more values than each input
   has, and that is not true of the compiler's meet: an equation on a
   name is dropped while another equation on that name is being added
   ([adding_equations_for_names]); a case that is impossible falls back
   to the case of the other tags ([meet_knowns], with a CR in the
   compiler); the extensions of the cases are joined. What precision
   is promised, and for which inputs, is to be stated apart, when the
   functions are here.

   Termination. The functions of meet call each other through the
   environment: a meet with an alias reads the type that the
   environment has for the name and meets that. It is not a recursion
   on the two types. In the compiler it stops because an equation on a
   name is dropped while one is being added on that name
   ([Meet_env.add_or_delay_concrete_equation_on_canonical_name]) and,
   between two such additions, the types get smaller; nothing states
   it. The transcription is to be one fixpoint on a number, the fuel,
   with [None] where it runs out, and to give itself, with the fuel
   that is left, to the join. The contracts are about answers that are
   not [None], so they need no fuel; that some fuel is enough for
   every well formed input is a statement of its own, to come, and is
   not needed for soundness.

   The step that is not sound. [reduce_inverse_relations], in its case
   [Get_tag]: when the numbers of a naked immediate that is [Get_tag]
   of a name become known, it adds to the name the equation
   [blocks_with_these_tags tags], a type with no immediate. The
   relation holds of a name that is an immediate, with any number:
   unboxing records it of a parameter that may be one, and passes the
   tag 0 where it is (FlambdaTypeMeaningSpec.v). So the equation added
   is not true ([get_tag_reduction_unsound_statement]), and no meet
   that makes this step has [meet_sound]. The input on which it fails:
   the environment [p : Variant (get_tag = tag)],
   [tag : (numbers unknown, Get_tag p)], as
   [Typing_env.add_get_tag_relation] makes it; the valuation in which
   [p] is the tagged immediate 7 and [tag] is 0, which satisfies it
   strictly; the meet of [= tag] and of the type of the
   naked immediate 0, both of which the value 0 has. The environment
   answered has [p : blocks_with_these_tags [0]], which no valuation
   that keeps the value of [p] satisfies. What would make it sound: to
   add the type of the immediates and of the blocks with one of the
   tags ([immediate_or_blocks_with_these_tags]), which is what the
   relation gives ([get_tag_reduction_repaired_statement]); in the
   compiler, [~immediates:Unknown] in place of the bottom type of
   naked immediates in the type that this case builds. Nothing is lost
   where the name is already known to be a block. The contract is not
   weakened for this: the transcription is to take the type added in
   this case as a parameter, so that the function as the compiler has
   it can be run and compared, and the function with the type that is
   true can be proved. (Discrepancies T1-1, R3-2; in both files.)

   Known differences between what the compiler does and what is said
   here, each recorded: T4-1 (after the join, meet defines again the
   variables that the join imported: a meet that does so does not keep
   an environment well formed, and [meet_keeps_well_formed] is to be
   proved of one that defines only what the result does not know),
   T4-2 (a meet through a name that holds poison), T4-3 (function
   types of slots that the index does not have), T4-4 (code age). *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaExpandHead FlambdaMeetEnv.
Import ListNotations.

(* ======================================================================== *)
(* What satisfies an environment                                            *)
(* ======================================================================== *)

(* A valuation satisfies a typing environment strictly: the environment
   is not bottom; every name that has a value has the type that the
   environment gives it, poison or not; and names that are aliases have
   the same value, or none. A name may have no value, and then nothing
   is asked of it. This stands in for the definition of this name that
   is to be in FlambdaTypingEnvSpec.v (see the header). *)
(* CR mshinwell: the statements about meet are made of environments in
   which a name that holds poison has a type that is true of poison.
   The compiler does not state that and nothing checks it. Unboxing
   gives the parameters that stand for the fields of an inactive case
   of a variant their types on every path, and passes poison for them:
   on such a path the environment of the handler is not satisfied
   strictly, and the statements below say nothing. There the compiler
   relies on no meet reading the type of a name that holds poison; if
   one does, it may answer bottom, or add an equation that is not true,
   at a point that is reached. The premise "the value of the name is
   not poison" on the name that an equation is added to is not enough
   (the header has the example). Decision D26. *)
Definition typing_env_satisfied_strictly (statics : static_env)
    (valuation : env) (tenv : Typing_env.t) : Prop :=
  Typing_env.is_bottom tenv = false
  ∧ (∀ (n : name) (ty : flambda_type)
       (binding_time_and_mode : Binding_time.With_name_mode.t) (v : value),
      Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
      = Some (ty, binding_time_and_mode) ->
      value_of_name valuation n = Some v ->
      type_satisfied statics valuation v ty)
  ∧ aliases_respected (Typing_env.aliases tenv) valuation.

(* What a meet or a join may change of a valuation: nothing, on the
   variables that the environment [tenv] knows. A variable that had no
   value has none. The variables that are new may have any value, or
   none. *)
Definition extended_from (tenv : Typing_env.t) (valuation valuation' : env)
    : Prop :=
  ∀ x : variable,
    Typing_env.mem None tenv (Name_var x) = true ->
    lookup x valuation' = lookup x valuation.

(* No name that the environment has a type for holds poison. *)
Definition no_name_holds_poison (valuation : env) (tenv : Typing_env.t)
    : Prop :=
  ∀ (n : name) (ty : flambda_type)
    (binding_time_and_mode : Binding_time.With_name_mode.t) (v : value),
    Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
    = Some (ty, binding_time_and_mode) ->
    value_of_name valuation n = Some v ->
    ~ is_poison v.

(* ======================================================================== *)
(* The functions                                                            *)
(* ======================================================================== *)

(* The type of [Meet.meet] (meet.ml, and [Meet_and_n_way_join.meet] as
   it is exposed): bottom, or a type and the environment extended.
   [None] is a fatal error of the compiler, or a meet that was not
   given enough fuel. *)
Definition meet_function : Type :=
  Typing_env.t -> flambda_type -> flambda_type ->
  option (Or_bottom.t (flambda_type * Typing_env.t)).

(* The type of [Typing_env.add_equation] of flambda2_types.ml: the
   environment in which the name has the type given as well as the type
   it had. Where the two have no value in common the environment
   answered is bottom ([Typing_env.make_bottom]). *)
Definition add_equation_function : Type :=
  Typing_env.t -> name -> flambda_type -> option Typing_env.t.

(* The type of the join that meet is given:
   [Join_env.cut_and_n_way_join ~n_way_join_type ~meet_expanded_head
   ~cut_after initial_env initial_tenv scoped_envs]. *)
Definition join_scoped_envs : Type :=
  meet_expanded_head -> Scope.t -> Meet_env.t -> Typing_env.t ->
  list Typing_env.t -> option Meet_env.t.

Section Contracts.

(* [type_well_formed] is to be T1's and [typing_env_well_formed] T2's
   (see the header): the conditions on a type and on an environment
   that the compiler's functions establish and meet relies on. Until
   they are defined the contracts take them as parameters. *)
Variable type_well_formed : flambda_type -> bool.
Variable typing_env_well_formed : Typing_env.t -> bool.

(* ======================================================================== *)
(* What is asked of the inputs                                              *)
(* ======================================================================== *)

(* A type that may be met in an environment: it is well formed and the
   environment knows its variables. *)
Definition type_fits (tenv : Typing_env.t) (t : flambda_type) : Prop :=
  type_well_formed t = true
  ∧ ∀ x : variable,
      x ∈ free_variables t -> Typing_env.mem None tenv (Name_var x) = true.

(* An environment in which a meet may be made: it is well formed, and
   so is each of its types. *)
Definition typing_env_fits (tenv : Typing_env.t) : Prop :=
  typing_env_well_formed tenv = true
  ∧ ∀ (n : name) (ty : flambda_type)
      (binding_time_and_mode : Binding_time.With_name_mode.t),
      Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
      = Some (ty, binding_time_and_mode) ->
      type_fits tenv ty.

Definition meet_inputs_well_formed (tenv : Typing_env.t)
    (t1 t2 : flambda_type) : Prop :=
  typing_env_fits tenv
  ∧ type_fits tenv t1
  ∧ type_fits tenv t2
  ∧ kind t1 = kind t2.

(* ======================================================================== *)
(* The contract of meet                                                     *)
(* ======================================================================== *)

(* A meet loses no value and what it adds is true. If a valuation
   satisfies the environment and gives [v] both types, the meet does
   not answer bottom, and a valuation that agrees with the first on
   what the environment knew satisfies the environment answered and
   gives [v] the type answered. *)
Definition meet_sound (meet : meet_function) : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t)
    (t1 t2 : flambda_type) (v : value)
    (result : Or_bottom.t (flambda_type * Typing_env.t)),
    meet_inputs_well_formed tenv t1 t2 ->
    typing_env_satisfied_strictly statics valuation tenv ->
    type_satisfied statics valuation v t1 ->
    type_satisfied statics valuation v t2 ->
    meet tenv t1 t2 = Some result ->
    ∃ (t : flambda_type) (tenv' : Typing_env.t) (valuation' : env),
      result = Or_bottom.Ok (t, tenv')
      ∧ extended_from tenv valuation valuation'
      ∧ typing_env_satisfied_strictly statics valuation' tenv'
      ∧ type_satisfied statics valuation' v t.

(* The same, read from the answer: where a meet answers bottom, no
   value has both types under a valuation that satisfies the
   environment. It follows from [meet_sound]
   ([meet_answers_bottom_statement]). *)
Definition meet_bottom_sound (meet : meet_function) : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t)
    (t1 t2 : flambda_type) (v : value),
    meet_inputs_well_formed tenv t1 t2 ->
    typing_env_satisfied_strictly statics valuation tenv ->
    meet tenv t1 t2 = Some Or_bottom.Bottom ->
    ~ (type_satisfied statics valuation v t1
       ∧ type_satisfied statics valuation v t2).

(* What is answered may be met again: the type is of the kind of the
   inputs, it and the environment are well formed, and the environment
   knows every name that the first knew. *)
Definition meet_keeps_well_formed (meet : meet_function) : Prop :=
  ∀ (tenv tenv' : Typing_env.t) (t1 t2 t : flambda_type),
    meet_inputs_well_formed tenv t1 t2 ->
    meet tenv t1 t2 = Some (Or_bottom.Ok (t, tenv')) ->
    typing_env_fits tenv'
    ∧ type_fits tenv' t
    ∧ kind t = kind t1
    ∧ ∀ n : name,
        Typing_env.mem None tenv n = true ->
        Typing_env.mem None tenv' n = true.

(* Kinds. In an environment that is not bottom, a meet of types of two
   kinds is a fatal error: it is never bottom, nor a type. *)
Definition meet_kinds (meet : meet_function) : Prop :=
  ∀ (tenv : Typing_env.t) (t1 t2 : flambda_type),
    Typing_env.is_bottom tenv = false ->
    kind t1 <> kind t2 ->
    meet tenv t1 t2 = None.

(* In an environment that is bottom every meet is bottom, and the kinds
   are not looked at. *)
Definition meet_bottom_env (meet : meet_function) : Prop :=
  ∀ (tenv : Typing_env.t) (t1 t2 : flambda_type),
    Typing_env.is_bottom tenv = true ->
    meet tenv t1 t2 = Some Or_bottom.Bottom.

Definition meet_contract (meet : meet_function) : Prop :=
  meet_sound meet
  ∧ meet_keeps_well_formed meet
  ∧ meet_kinds meet
  ∧ meet_bottom_env meet.

(* ======================================================================== *)
(* Adding an equation                                                       *)
(* ======================================================================== *)

(* [Typing_env.add_equation]. If a valuation satisfies the environment,
   and the name has a value, of the type given, then a valuation that
   agrees with the first on what the environment knew satisfies the
   environment answered. In particular that environment is not
   bottom. *)
(* CR mshinwell: the premise is that the environment is satisfied
   strictly: the name, if it holds poison, has a type that is true of
   poison, and so has every name whose type the meet reads. That is an
   assumption of the compiler that nothing checks. Unboxing gives types
   to parameters that hold poison on some paths; an equation added on
   such a parameter where it holds poison, whose meet with its type is
   bottom, would make the environment of a point that is reached
   bottom. Decision D26. *)
Definition add_equation_sound (add_equation : add_equation_function)
    : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv tenv' : Typing_env.t)
    (n : name) (ty : flambda_type) (v : value),
    typing_env_fits tenv ->
    type_fits tenv ty ->
    typing_env_satisfied_strictly statics valuation tenv ->
    value_of_name valuation n = Some v ->
    type_satisfied statics valuation v ty ->
    add_equation tenv n ty = Some tenv' ->
    ∃ valuation' : env,
      extended_from tenv valuation valuation'
      ∧ typing_env_satisfied_strictly statics valuation' tenv'.

(* The same from the premises of FlambdaTypingEnvSpec.v, where no name
   of the environment holds poison. It follows from
   [add_equation_sound] ([add_equation_no_poison_statement]). *)
Definition add_equation_sound_no_poison
    (add_equation : add_equation_function) : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv tenv' : Typing_env.t)
    (n : name) (ty : flambda_type) (v : value),
    typing_env_fits tenv ->
    type_fits tenv ty ->
    typing_env_satisfied statics valuation tenv ->
    no_name_holds_poison valuation tenv ->
    value_of_name valuation n = Some v ->
    type_satisfied statics valuation v ty ->
    add_equation tenv n ty = Some tenv' ->
    ∃ valuation' : env,
      extended_from tenv valuation valuation'
      ∧ typing_env_satisfied_strictly statics valuation' tenv'.

(* ======================================================================== *)
(* The meet of expanded types, and the join that meet is given              *)
(* ======================================================================== *)

(* An environment of a meet after some of the meet: its typing
   environment has the same scope and the same earlier levels, the
   names it knew are known with their binding times and name modes and
   with types of the same kinds, the names that equations are being
   added to are the same, and no name to avoid is forgotten. *)
Definition meet_env_extends (menv menv' : Meet_env.t) : Prop :=
  let tenv := Meet_env.typing_env menv in
  let tenv' := Meet_env.typing_env menv' in
  Typing_env.current_scope tenv' = Typing_env.current_scope tenv
  ∧ Typing_env.prev_levels tenv' = Typing_env.prev_levels tenv
  ∧ Typing_env.min_binding_time tenv' = Typing_env.min_binding_time tenv
  ∧ Meet_env.adding_equations_for_names menv'
    = Meet_env.adding_equations_for_names menv
  ∧ (∀ x : variable,
      among x (Meet_env.names_to_avoid menv) = true ->
      among x (Meet_env.names_to_avoid menv') = true)
  ∧ ∀ (n : name) (ty : flambda_type)
      (binding_time_and_mode : Binding_time.With_name_mode.t),
      Keyed.lookup name_eqb n (Typing_env.names_to_types tenv)
      = Some (ty, binding_time_and_mode) ->
      ∃ ty' : flambda_type,
        Keyed.lookup name_eqb n (Typing_env.names_to_types tenv')
        = Some (ty', binding_time_and_mode)
        ∧ kind ty' = kind ty.

(* [Meet_env.meet_expanded_head], the meet of two types that are not
   aliases: [meet_sound] for it, in the environment of a meet. It is
   what the join is given, and what the join's contract supposes. *)
Definition meet_expanded_head_sound (meet_head : meet_expanded_head) : Prop :=
  ∀ (statics : static_env) (valuation : env) (menv : Meet_env.t)
    (expanded1 expanded2 : Expanded_type.t) (v : value)
    (result : Meet_result.t Expanded_type.t),
    let tenv := Meet_env.typing_env menv in
    meet_inputs_well_formed tenv (Expanded_type.to_type expanded1)
      (Expanded_type.to_type expanded2) ->
    typing_env_satisfied_strictly statics valuation tenv ->
    type_satisfied statics valuation v (Expanded_type.to_type expanded1) ->
    type_satisfied statics valuation v (Expanded_type.to_type expanded2) ->
    meet_head menv expanded1 expanded2 = Some result ->
    ∃ (r : meet_return_value Expanded_type.t) (menv' : Meet_env.t)
      (valuation' : env),
      result = Meet_result.Ok r menv'
      ∧ extended_from tenv valuation valuation'
      ∧ typing_env_satisfied_strictly statics valuation'
          (Meet_env.typing_env menv')
      ∧ type_satisfied statics valuation' v
          (Expanded_type.to_type (extract_value r expanded1 expanded2))
      ∧ meet_env_extends menv menv'
      ∧ typing_env_fits (Meet_env.typing_env menv')
      ∧ type_fits (Meet_env.typing_env menv')
          (Expanded_type.to_type (extract_value r expanded1 expanded2)).

(* What meet gives the join: an environment made from [initial_tenv] by
   adding definitions and equations. It fits, it knows what
   [initial_tenv] knows, and what satisfies it satisfies
   [initial_tenv]. *)
Definition scoped_env_of (initial_tenv scoped_env : Typing_env.t) : Prop :=
  typing_env_fits scoped_env
  ∧ (∀ n : name,
      Typing_env.mem None initial_tenv n = true ->
      Typing_env.mem None scoped_env n = true)
  ∧ ∀ (statics : static_env) (valuation : env),
      typing_env_satisfied_strictly statics valuation scoped_env ->
      typing_env_satisfied_strictly statics valuation initial_tenv.

(* The contract of the join that meet is given. Meet calls it with the
   typing environment of [initial_env] for [initial_tenv] and its scope
   for [cut_after]. *)
Definition join_scoped_envs_sound (join : join_scoped_envs) : Prop :=
  ∀ (meet_head : meet_expanded_head) (initial_env result : Meet_env.t)
    (scoped_envs : list Typing_env.t),
    let initial_tenv := Meet_env.typing_env initial_env in
    meet_expanded_head_sound meet_head ->
    typing_env_fits initial_tenv ->
    (∀ scoped_env : Typing_env.t,
      scoped_env ∈ scoped_envs -> scoped_env_of initial_tenv scoped_env) ->
    join meet_head (Typing_env.current_scope initial_tenv) initial_env
      initial_tenv scoped_envs
    = Some result ->
    (* What satisfies one of the environments joined extends to
       something that satisfies the result. *)
    (∀ (scoped_env : Typing_env.t) (statics : static_env) (valuation : env),
      scoped_env ∈ scoped_envs ->
      typing_env_satisfied_strictly statics valuation scoped_env ->
      ∃ valuation' : env,
        extended_from scoped_env valuation valuation'
        ∧ typing_env_satisfied_strictly statics valuation'
            (Meet_env.typing_env result))
    (* The result is the first environment, extended. *)
    ∧ meet_env_extends initial_env result
    ∧ typing_env_fits (Meet_env.typing_env result)
    (* A variable of the result that no environment given knows is new,
       and is to be avoided from now on. *)
    ∧ ∀ x : variable,
        Typing_env.mem None (Meet_env.typing_env result) (Name_var x)
        = true ->
        Typing_env.mem None initial_tenv (Name_var x) = false ->
        (∀ scoped_env : Typing_env.t,
          scoped_env ∈ scoped_envs ->
          Typing_env.mem None scoped_env (Name_var x) = false) ->
        among x (Meet_env.names_to_avoid initial_env) = false
        ∧ among x (Meet_env.names_to_avoid result) = true.

(* The form of the statement to come for the transcribed meet, which
   takes the join and the fuel: with a join that has its contract, it
   has its own, whatever the fuel. *)
Definition transcription_sound
    (meet_of : join_scoped_envs -> nat -> meet_function) : Prop :=
  ∀ (join : join_scoped_envs) (fuel : nat),
    join_scoped_envs_sound join -> meet_contract (meet_of join fuel).

End Contracts.

(* ======================================================================== *)
(* The step of the compiler's meet that is not sound                        *)
(* ======================================================================== *)

(* The type that [reduce_inverse_relations] adds, in its case [Get_tag],
   to a name of which a number among [tags] is [Get_tag] is
   [blocks_with_these_tags tags] (FlambdaTypeGrammar.v). The type that
   is true of such a name: an immediate, or a block with one of the
   tags. It is [blocks_with_these_tags] with [~immediates:Unknown]. *)
Definition immediate_or_blocks_with_these_tags (tags : list Z)
    (alloc_mode : Alloc_mode.t) : flambda_type :=
  create_variant false Or_unknown.Unknown
    (Or_unknown.Known
       (Row_like_for_blocks
          (map (fun tag => (tag, Or_unknown.Unknown)) tags)
          Or_bottom.Bottom alloc_mode))
    No_extensions.

(* The compiler's step is not sound: there are a value that is not
   poison and a number that [Get_tag] relates, and the value has not
   the type that the step adds. The value is an immediate. *)
Definition get_tag_reduction_unsound_statement : Prop :=
  ∃ (statics : static_env) (vars : env) (w : value) (n : Z),
    relation_holds statics Relation.Get_tag w n
    ∧ ~ is_poison w
    ∧ ~ type_satisfied statics vars w
          (blocks_with_these_tags [n] Alloc_mode.Heap_or_local).

(* With the other type it is. *)
Definition get_tag_reduction_repaired_statement : Prop :=
  ∀ (statics : static_env) (vars : env) (w : value) (n : Z) (tags : list Z)
    (alloc_mode : Alloc_mode.t),
    relation_holds statics Relation.Get_tag w n ->
    n ∈ tags ->
    ~ is_poison w ->
    type_satisfied statics vars w
      (immediate_or_blocks_with_these_tags tags alloc_mode).

(* ======================================================================== *)
(* What the definitions give                                                *)
(* ======================================================================== *)

(* A valuation that satisfies an environment as FlambdaTypingEnvSpec.v
   says, and gives poison to none of its names, satisfies it
   strictly. *)
Definition satisfied_no_poison_statement : Prop :=
  ∀ (statics : static_env) (valuation : env) (tenv : Typing_env.t),
    typing_env_satisfied statics valuation tenv ->
    no_name_holds_poison valuation tenv ->
    typing_env_satisfied_strictly statics valuation tenv.

(* A meet that has its contract answers bottom only where no value has
   both types. *)
Definition meet_answers_bottom_statement : Prop :=
  ∀ (type_well_formed : flambda_type -> bool)
    (typing_env_well_formed : Typing_env.t -> bool) (meet : meet_function),
    meet_sound type_well_formed typing_env_well_formed meet ->
    meet_bottom_sound type_well_formed typing_env_well_formed meet.

(* [add_equation_sound] gives the statement from the premises of
   FlambdaTypingEnvSpec.v. *)
Definition add_equation_no_poison_statement : Prop :=
  ∀ (type_well_formed : flambda_type -> bool)
    (typing_env_well_formed : Typing_env.t -> bool)
    (add_equation : add_equation_function),
    add_equation_sound type_well_formed typing_env_well_formed add_equation ->
    add_equation_sound_no_poison type_well_formed typing_env_well_formed
      add_equation.
