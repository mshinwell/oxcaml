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


(* The environment side of the n-way join: what is stated of the
   functions of FlambdaJoinEnv.v.

   To be reviewed: every definition and statement of this file. The
   contract of a join is FlambdaJoinSpec.v; this file is about the
   transcription of the compiler's join.

   What is here so far:
   - [compiler_join]: the transcription of the join that Simplify
     calls, as a join of environments in the sense of the contract.
   - An instance, [Witness], that shows that the transcription has not
     the strict contract ([sound_join_of_environments]): two uses in
     which a variable [x] that exists only in types has a type that
     says that [r] holds whether [x] is null (at the first use [x] may
     be null or not, at the second it is null); a run through the
     first use in which [x] has no value and [r] holds 0. The join puts the
     relation back on [r] ("[r] is the result of [Is_null] on [x]"),
     and no valuation that gives [x] no value satisfies that. The run
     meets neither [scrutinees_have_values] nor
     [joined_variables_have_values], two of the conditions that the
     contract of the compiler's join has
     ([sound_join_where_values_are_read]): [x] is a variable of the
     source that both uses have refined. An instance in which only the
     first fails needs the scrutinee to be a variable that the join
     makes, standing at one use for a variable with no value (the
     shape of the program that the compiler compiles wrongly); it is
     owed, with the model's join of types.

   What the instance is made with, and why it shows something of the
   compiler's function and not of its stand-ins. The join is given
   the functions of the environment of the meet, the meet, and the
   join of types. Those of the model are not under this file yet, so
   the instance has stand-ins, each of which does, on the inputs that
   this instance gives it, what the compiler's function does:
   - The join of types is given, for [x], the two types of the uses.
     The stand-in answers the first, which is their upper bound, if
     every type given is one of the two, and unknown otherwise. It is
     an upper bound ([witness_join_of_types_upper_bound_statement]),
     and what it answers mentions only [r], which the source has. (The
     compiler's function, on these two types, joins the two [is_null]
     variables, which are both [r], into [r], and the two parts that
     are not null, unknown and bottom, into unknown: the same type.)
   - The environment of the meet is the typing environment; an
     equation is added by replacing the type of a name whose type is
     unknown, and the stand-in answers [None] for any other equation.
     The compiler's function meets the two types; the meet of unknown
     with a type that is not an alias and has more than one value is
     that type, and it then replaces the type of the name
     ([Meet_env.replace_concrete_equation]).
   - The equality of types that stands for physical equality is one
     that is right of the two types of [x], which are all that it is
     asked about: they differ, so they are joined and not kept as they
     stand. (The equality of the meaning of types is not under this
     file yet.)
   The type of [x] in the uses is what a join
   brings into an environment for a variable of one of its uses whose
   type was made by reading the same field of an older block that
   another variable was read from (discrepancy T5-10 has the stages).
   That such environments, and such a run, come from a program is not
   shown: the instance is about the contract, and is the reason why
   the contract of the compiler's join has its conditions. *)

From Stdlib Require Import ZArith List Bool PeanoNat.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvInvariantSpec FlambdaJoinEnv FlambdaJoinSpec.
Import ListNotations.

(* ======================================================================== *)
(* The compiler's join, as a join of environments                           *)
(* ======================================================================== *)

(* [Join_env.cut_and_n_way_join_with_analysis], given what the model's
   function needs besides the compiler's arguments. *)
Definition compiler_join {A meet_env meet_expanded_head : Type}
    (ops : Join_env.meet_env_functions meet_env meet_expanded_head)
    (p : Join_env.parameters) (fuel : nat)
    (n_way_join_type : Join_env.n_way_join_type)
    (meet_expanded_head_fn : meet_expanded_head) : join_of_environments A :=
  fun (avoid : list variable) (inputs : join_inputs A) =>
    cut_and_n_way_join_with_analysis ops p fuel n_way_join_type
      meet_expanded_head_fn avoid (cut_after inputs) (source inputs)
      (uses inputs).

(* ======================================================================== *)
(* The transcription has not the strict contract                            *)
(* ======================================================================== *)

Module Witness.

  (* [r] may occur in terms; [x] exists only in types. *)
  Definition r : variable := 1%positive.
  Definition x : variable := 2%positive.

  (* A value that may be null, of which [r] holds whether it is. *)
  Definition type_of_x : flambda_type :=
    Type_value
      (Ok (No_alias (Head_of_kind_value Unknown (Maybe_null (Some r))))).

  Definition source_env : Typing_env.t :=
    Typing_env.add_variable_definition
      (Typing_env.add_variable_definition Typing_env.create r
         (Naked_number Kind_naked_immediate) Name_mode.normal)
      x Value Name_mode.in_types.

  (* The same of a value that is null. *)
  Definition type_of_x_null : flambda_type :=
    Type_value
      (Ok (No_alias (Head_of_kind_value Bottom (Maybe_null (Some r))))).

  (* A use: the source, one scope further, where [x] has its type. *)
  Definition use_env : Typing_env.t :=
    Typing_env.replace_equation (Typing_env.increment_scope source_env)
      (Name_var x) type_of_x.

  (* The other use, where [x] is null. *)
  Definition use_env_null : Typing_env.t :=
    Typing_env.replace_equation (Typing_env.increment_scope source_env)
      (Name_var x) type_of_x_null.

  Definition inputs : join_inputs unit :=
    {| source := source_env;
       cut_after := Typing_env.current_scope source_env;
       uses := [(tt, use_env); (tt, use_env_null)] |}.

  (* The stand-in for the join of types. *)
  Definition is_type_of_x (t : flambda_type) : bool :=
    match t with
    | Type_value
        (Ok (No_alias (Head_of_kind_value Unknown (Maybe_null (Some r'))))) =>
      Pos.eqb r' r
    | _ => false
    end.

  Definition is_type_of_x_null (t : flambda_type) : bool :=
    match t with
    | Type_value
        (Ok (No_alias (Head_of_kind_value Bottom (Maybe_null (Some r'))))) =>
      Pos.eqb r' r
    | _ => false
    end.

  Definition join_of_types : Join_env.n_way_join_type :=
    fun (s : Join_env.t) (ts : list (Index.t * flambda_type)) =>
      match ts with
      | [] => None
      | _ :: _ =>
        if forallb
             (fun binding =>
                is_type_of_x (snd binding) || is_type_of_x_null (snd binding))
             ts
        then Some (Or_unknown.Known type_of_x, s)
        else Some (Or_unknown.Unknown, s)
      end.

  (* The stand-in for the equality of types: right of the two types of
     [x]. *)
  Definition type_eqb (t t' : flambda_type) : bool :=
    (is_type_of_x t && is_type_of_x t')
    || (is_type_of_x_null t && is_type_of_x_null t').

  (* The stand-in for the environment of the meet. *)
  Definition replace_unknown (tenv : option Typing_env.t)
      (equation : name * flambda_type) : option Typing_env.t :=
    let* tenv := tenv in
    let* ty := Typing_env.find tenv (fst equation) None in
    match ty with
    | Type_value Unknown | Type_naked_immediate Unknown =>
      Some (Typing_env.replace_equation tenv (fst equation) (snd equation))
    | _ => None
    end.

  Definition ops : Join_env.meet_env_functions Typing_env.t unit :=
    {| Join_env.create_meet_env := fun tenv => tenv;
       Join_env.current_typing_env := fun tenv => tenv;
       Join_env.add_variable_definition :=
         Typing_env.add_variable_definition;
       Join_env.add_env_extension :=
         fun tenv extension _ =>
           match extension with
           | Env_extension equations =>
             List.fold_left replace_unknown equations (Some tenv)
           end;
       Join_env.make_bottom := Typing_env.make_bottom;
       Join_env.final_typing_env := fun tenv => tenv;
       Join_env.names_to_avoid := fun _ => [];
       Join_env.with_names_to_avoid := fun tenv _ => tenv |}.

  (* No variable is made and no constant is expanded in this instance:
     the first and the fourth are never called. *)
  Definition parameters : Join_env.parameters :=
    {| Join_env.fresh := fun _ => 3%positive;
       Join_env.type_eqb := type_eqb;
       Join_env.env_extension_eqb := fun _ _ => false;
       Join_env.expand_const := fun _ => type_of_x;
       Join_env.join_depth := 1 |}.

  Definition join : join_of_environments unit :=
    compiler_join ops parameters 10 join_of_types tt.

  (* The run: [r] holds 0 and [x] has no value. *)
  Definition valuation : env := [(r, Value_const (Naked_immediate 0))].

End Witness.

(* The stand-in for the join of types answers an upper bound, and
   leaves the state as it is: a value that has one of the types given,
   under a valuation, has the type answered under any valuation that
   gives [r] the same. *)
Definition witness_join_of_types_upper_bound_statement : Prop :=
  ∀ (s s' : Join_env.t) (ts : list (Index.t * flambda_type))
    (ty : flambda_type) (index : Index.t) (t_index : flambda_type)
    (statics : static_env) (valuation valuation' : env) (v : value),
    Witness.join_of_types s ts = Some (Or_unknown.Known ty, s') ->
    In (index, t_index) ts ->
    lookup Witness.r valuation' = lookup Witness.r valuation ->
    type_satisfied statics valuation v t_index ->
    s' = s ∧ type_satisfied statics valuation' v ty.

(* The inputs are what the contract asks: well formed, with the
   invariant of typing environments, and kinded. *)
Definition witness_inputs_well_formed_statement : Prop :=
  join_inputs_well_formed typing_env_invariant [Witness.r; Witness.x]
    Witness.inputs
  ∧ uses_kinded Witness.inputs.

(* The run satisfies the first use and the source, strictly. *)
Definition witness_run_satisfies_statement : Prop :=
  ∀ statics : static_env,
    typing_env_satisfied_strictly statics Witness.valuation Witness.use_env
    ∧ typing_env_satisfied_strictly statics Witness.valuation
        Witness.source_env.

(* The join answers, and its target does not admit the first use: no
   valuation satisfies the target and gives [r] and [x] what the run
   gives them. The run has not the values that the join reads: [r] has
   a value and [x], on which the target has a relation with [r] for
   result, has none; and [x] is a variable of the source that every
   use has an equation on. *)
Definition witness_use_not_admitted_statement : Prop :=
  ∃ (target : Typing_env.t) (analysis : Analysis.t unit),
    Witness.join [Witness.r; Witness.x] Witness.inputs
    = Some (target, analysis)
    ∧ ~ join_admits_use Witness.source_env Witness.use_env target
          (Analysis.definitions_in_joined_envs analysis)
          (Analysis.canonical_definitions_at_normal_mode analysis) 0
    ∧ ~ scrutinees_have_values target
          (Analysis.definitions_in_joined_envs analysis) 0 Witness.valuation
    ∧ ~ joined_variables_have_values Witness.inputs Witness.valuation.

(* So the transcription of the compiler's join, with these stand-ins,
   has not the strict contract. *)
Definition transcribed_join_not_strict_statement : Prop :=
  ~ sound_join_of_environments typing_env_invariant Witness.join.
