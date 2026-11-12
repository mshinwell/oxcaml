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


(* Examples of the n-way join of typing environments: what the join
   that Simplify calls answers on small inputs, with the meet, the
   join of types and the join of environments of the model put
   together ([model_join], FlambdaJoinMeet.v).

   To be reviewed: how the inputs are made, and each statement,
   against what the compiler's [Join_levels.cut_and_n_way_join]
   answers at a continuation whose parameter is given the types of
   the example at its uses.

   Why they are here. What is proved of the join says that what it
   adds to the target is true. A join that added nothing would have
   that too. The examples say what the model computes, with nothing
   stood in for: the same functions as in the statements, and
   environments made with the model's own [Typing_env.add_equation].
   An answer [None] on one of these inputs would be a fatal error of
   the compiler, too little fuel, or the state at which the model's
   meet stops and the compiler does not (FlambdaJoinMeet.v says
   which): there is none.

   What they are not. No answer here was read off a run of the
   compiler: each is what the model computes, and was compared with
   the compiler's code by reading. They are written so that the
   workstream of the differential tests can run them, as it ran the
   examples of the join of types (FlambdaJoinTypesExamplesSpec.v).

   The inputs. The source environment knows three variables of kind
   value that may occur in terms: [y], [z] and the parameter [p]. A
   use is the source one scope further, in which some variables may
   have been defined and given types, and in which [p] has been given
   a type, all by [Typing_env.add_equation]. The uses are joined
   after the scope of the source. What a statement shows of the
   answer: the type that the target has for [p]; whether the target
   is bottom; the two maps of definitions of the analysis; and the
   type that the target has for [a], a variable that some uses define
   and the source does not.

   The choices are the compiler's, the depth of the join is the
   compiler's default, 5, and the fuel is more than these inputs
   need. A new variable is one greater than the names to avoid, which
   are [y], [z], [p] and [a]: so the first variable that a join makes
   here is 5. The sets of numbers of the model are lists, and the
   order of the numbers in an answer is the one that the model makes;
   it has no meaning.

   The proofs are by computation, in FlambdaJoinMeetExamplesProofs.v,
   which needs no review. *)

From Stdlib Require Import ZArith List Bool PeanoNat.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaTypingEnv FlambdaJoinEnv FlambdaJoinSpec FlambdaJoinEnvSpec
  FlambdaJoinTypesExamplesSpec FlambdaMeetGrammar FlambdaMeetEnv FlambdaMeet
  FlambdaMeetSpec FlambdaJoinMeet.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The inputs                                                               *)
(* ======================================================================== *)

Definition example_y : variable := 1%positive.
Definition example_z : variable := 2%positive.
Definition example_p : variable := 3%positive.
Definition example_a : variable := 4%positive.

Definition example_fuel : fuels :=
  {| fuel_of_env := 20; fuel_of_types := 20; fuel_of_meet := 20 |}.

Definition example_source_env : Typing_env.t :=
  Typing_env.add_variable_definition
    (Typing_env.add_variable_definition
       (Typing_env.add_variable_definition Typing_env.create example_y Value
          Name_mode.normal)
       example_z Value Name_mode.normal)
    example_p Value Name_mode.normal.

Definition example_add_equation : add_equation_function :=
  model_add_equation Join_env.compiler_choices compiler_choices 5
    example_fuel.

(* An environment in which variables have been defined, each at a name
   mode and with a type. *)
Fixpoint example_with_variables (tenv : Typing_env.t)
    (variables : list (variable * Name_mode.t * flambda_type))
    : option Typing_env.t :=
  match variables with
  | [] => Some tenv
  | (x, name_mode, ty) :: variables =>
    let* tenv :=
      example_add_equation
        (Typing_env.add_variable_definition tenv x (kind ty) name_mode)
        (Name_var x) ty
    in
    example_with_variables tenv variables
  end.

(* A use: the source one scope further, with the variables given, and
   the type given for [p]. *)
Definition example_use
    (variables : list (variable * Name_mode.t * flambda_type))
    (ty : flambda_type) : option Typing_env.t :=
  let* tenv :=
    example_with_variables (Typing_env.increment_scope example_source_env)
      variables
  in
  example_add_equation tenv (Name_var example_p) ty.

(* A use that is bottom. *)
Definition example_bottom_use : option Typing_env.t :=
  Some (Typing_env.make_bottom (Typing_env.increment_scope example_source_env)).

Fixpoint example_all (uses : list (option Typing_env.t))
    : option (list Typing_env.t) :=
  match uses with
  | [] => Some []
  | use :: uses =>
    let* use := use in
    let* uses := example_all uses in
    Some (use :: uses)
  end.

(* What is shown of an answer. *)
Record example_answer : Type := Example_answer {
  type_of_p : option flambda_type;
  target_is_bottom : bool;
  definitions : finite_map (Simples_in_joined_envs.t * flambda_kind);
  definitions_at_normal_mode
    : finite_map (Simples_in_joined_envs.t * flambda_kind);
  type_of_a : option flambda_type
}.

(* The join of uses. *)
Definition example_join_uses (uses : list (option Typing_env.t))
    : option example_answer :=
  let* uses := example_all uses in
  let* '(target, analysis) :=
    model_join Join_env.compiler_choices compiler_choices 5 example_fuel
      [example_y; example_z; example_p; example_a]
      {| source := example_source_env;
         cut_after := Typing_env.current_scope example_source_env;
         uses := map (fun use => (tt, use)) uses |}
  in
  Some
    {| type_of_p := Typing_env.find target (Name_var example_p) None;
       target_is_bottom := Typing_env.is_bottom target;
       definitions := Analysis.definitions_in_joined_envs analysis;
       definitions_at_normal_mode :=
         Analysis.canonical_definitions_at_normal_mode analysis;
       type_of_a :=
         if Typing_env.mem None target (Name_var example_a)
         then Typing_env.find target (Name_var example_a) None
         else None |}.

(* The join of two uses that define no variable. *)
Definition example_join_types (ty1 ty2 : flambda_type)
    : option example_answer :=
  example_join_uses [example_use [] ty1; example_use [] ty2].

(* An answer in which [p] has a type, the target is not bottom, the two
   maps of definitions are the same, and the target does not know
   [a]. *)
Definition example_answer_of (ty : flambda_type)
    (definitions : finite_map (Simples_in_joined_envs.t * flambda_kind))
    : option example_answer :=
  Some
    {| type_of_p := Some ty;
       target_is_bottom := false;
       definitions := definitions;
       definitions_at_normal_mode := definitions;
       type_of_a := None |}.

(* The definition of a variable at two uses. *)
Definition example_definition (x : variable) (indices : nat * nat)
    (simples : simple * simple) (kind : flambda_kind)
    : finite_map (Simples_in_joined_envs.t * flambda_kind) :=
  [(x,
    ([(fst indices, fst simples); (snd indices, snd simples)], kind))].

(* ======================================================================== *)
(* Constants                                                                *)
(* ======================================================================== *)

(* [p] is 1 at a use and 2 at the other. The join of types makes a
   variable for the two constants, of which [p] is an alias in the
   target; so the variable is replaced by [p], which has its type, the
   set of the two, and its definition: [p] is the constant 1 at the
   first use and 2 at the second. *)
Definition example_join_env_two_constants_statement : Prop :=
  example_join_types (this_tagged_immediate 1) (this_tagged_immediate 2)
  = example_answer_of (these_tagged_immediates [1; 2])
      (example_definition example_p (0%nat, 1%nat)
         (Const (Tagged_immediate 1), Const (Tagged_immediate 2)) Value).

(* The same constant at both uses: [p] is that constant, and nothing
   is defined. *)
Definition example_join_env_one_constant_statement : Prop :=
  example_join_types (this_tagged_immediate 1) (this_tagged_immediate 1)
  = example_answer_of (this_tagged_immediate 1) [].

(* A set of numbers at a use and a constant at the other: the union,
   and nothing is defined. *)
Definition example_join_env_set_and_constant_statement : Prop :=
  example_join_types (these_tagged_immediates [1; 2])
    (this_tagged_immediate 3)
  = example_answer_of (these_tagged_immediates [3; 1; 2]) [].

(* ======================================================================== *)
(* Aliases                                                                  *)
(* ======================================================================== *)

(* [p] is [y] at both uses: it is [y] in the target. *)
Definition example_join_env_one_alias_statement : Prop :=
  example_join_types (alias_type_of Value (Var example_y))
    (alias_type_of Value (Var example_y))
  = example_answer_of (alias_type_of Value (Var example_y)) [].

(* [p] is [y] at a use and [z] at the other: nothing is known of it
   in the target (nothing is known of [y] nor of [z]), and the
   analysis says what it is at each use. *)
Definition example_join_env_two_aliases_statement : Prop :=
  example_join_types (alias_type_of Value (Var example_y))
    (alias_type_of Value (Var example_z))
  = example_answer_of (unknown Value)
      (example_definition example_p (0%nat, 1%nat)
         (Var example_y, Var example_z) Value).

(* ======================================================================== *)
(* Blocks                                                                   *)
(* ======================================================================== *)

(* Two pairs of constants: a pair of sets. The two variables that the
   join of types makes for the fields are mentioned once each, and are
   replaced by their types. *)
Definition example_join_env_pairs_statement : Prop :=
  example_join_types
    (example_join_block 0 [this_tagged_immediate 1; this_tagged_immediate 2])
    (example_join_block 0 [this_tagged_immediate 3; this_tagged_immediate 4])
  = example_answer_of
      (example_join_block 0
         [these_tagged_immediates [1; 3]; these_tagged_immediates [2; 4]])
      [].

(* An immediate at a use and a block at the other, as for a value of
   an option type: a variant with both, and a variable made for the
   result of [Is_int], which is 1 at the first use and 0 at the
   second. *)
Definition example_join_env_immediate_and_block_statement : Prop :=
  example_join_types (this_tagged_immediate 0)
    (example_join_block 0 [alias_type_of Value (Var example_y)])
  = example_answer_of
      (example_join_variant (Some 5%positive) (this_naked_immediate 0) None
         [(0, [alias_type_of Value (Var example_y)])])
      (example_definition 5%positive (1%nat, 0%nat)
         (Const (Naked_immediate 0), Const (Naked_immediate 1))
         (Naked_number Kind_naked_immediate)).

(* Blocks of two tags: a variant with the two cases, and a variable
   made for the result of [Get_tag], which is 0 at the first use and 1
   at the second. *)
Definition example_join_env_two_tags_statement : Prop :=
  example_join_types (example_join_block 0 [this_tagged_immediate 1])
    (example_join_block 1 [this_tagged_immediate 2])
  = example_answer_of
      (example_join_variant None (bottom (Naked_number Kind_naked_immediate))
         (Some 5%positive)
         [(0, [this_tagged_immediate 1]); (1, [this_tagged_immediate 2])])
      (example_definition 5%positive (1%nat, 0%nat)
         (Const (Naked_immediate 1), Const (Naked_immediate 0))
         (Naked_number Kind_naked_immediate)).

(* ======================================================================== *)
(* Variables of the uses                                                    *)
(* ======================================================================== *)

(* The field of the block is a variable that the first use defines,
   one of two numbers, and a constant at the second use: the field is
   one of the three in the target, which does not know the variable. *)
Definition example_join_env_variable_of_one_use_statement : Prop :=
  example_join_uses
    [example_use
       [(example_a, Name_mode.normal, these_tagged_immediates [1; 2])]
       (example_join_block 0 [alias_type_of Value (Var example_a)]);
     example_use [] (example_join_block 0 [this_tagged_immediate 7])]
  = example_answer_of
      (example_join_block 0 [these_tagged_immediates [7; 1; 2]]) [].

(* The field is a variable that both uses define, which exists only in
   types: the target has the variable, with the type that it has at
   the uses, and the field is that variable. *)
Definition example_join_env_variable_of_both_uses_statement : Prop :=
  example_join_uses
    [example_use
       [(example_a, Name_mode.in_types, these_tagged_immediates [1; 2])]
       (example_join_block 0 [alias_type_of Value (Var example_a)]);
     example_use
       [(example_a, Name_mode.in_types, these_tagged_immediates [1; 2])]
       (example_join_block 0 [alias_type_of Value (Var example_a)])]
  = Some
      {| type_of_p :=
           Some (example_join_block 0 [alias_type_of Value (Var example_a)]);
         target_is_bottom := false;
         definitions := [];
         definitions_at_normal_mode := [];
         type_of_a := Some (these_tagged_immediates [1; 2]) |}.

(* ======================================================================== *)
(* Uses that are bottom                                                     *)
(* ======================================================================== *)

(* A use that is bottom is left out: the definitions are at the first
   and the third. *)
Definition example_join_env_bottom_use_statement : Prop :=
  example_join_uses
    [example_use [] (this_tagged_immediate 1); example_bottom_use;
     example_use [] (this_tagged_immediate 2)]
  = example_answer_of (these_tagged_immediates [1; 2])
      (example_definition example_p (0%nat, 2%nat)
         (Const (Tagged_immediate 1), Const (Tagged_immediate 2)) Value).

(* No use that is not bottom: the target is bottom. *)
Definition example_join_env_no_use_statement : Prop :=
  example_join_uses [example_bottom_use]
  = Some
      {| type_of_p := Some (bottom Value);
         target_is_bottom := true;
         definitions := [];
         definitions_at_normal_mode := [];
         type_of_a := None |}.
