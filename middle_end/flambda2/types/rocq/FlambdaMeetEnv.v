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



(* The environment that a meet works in, and what a meet answers, as the
   model sees them.

   This file is to be reviewed, line by line against
   middle_end/flambda2/types/env/meet_env.ml (with meet_env.mli). It
   holds definitions only and it extracts. For now it has the types
   alone: they are what the join that meet is given is written against
   (FlambdaMeetSpec.v says what is asked of it). The functions of
   meet_env.ml ([add_equation], [add_env_extension], [add_alias],
   [enter_scope], [meet], ...) are to come here with the functions of
   meet, under the compiler's names.

   What the model has of [Meet_env]:
   - [meet_return_value] and [meet_result]: in full. The constructors of
     [meet_result] are in a module, [Meet_result.Bottom] and
     [Meet_result.Ok], as those of [Or_bottom.t] are in
     FlambdaTypeGrammar.v.
   - [meet_expanded_head]: the type of the function that meets two
     expanded types, which [Meet_env] and the join are given as an
     argument. Here it answers an [option]: [None] is a fatal error of
     the compiler, or a meet that was not given enough fuel
     (FlambdaMeetSpec.v, "Termination").
   - [t]: [typing_env] and [adding_equations_for_names] in full, the
     latter as a list of names.

   The differences:
   - [delayed_equations] is left out, with [delay_equation_on_simple]
     and the loop of [final_typing_env]. The compiler has three
     strategies for a meet ([meet_strategy]: [Dfs], [Bfs], [Hybrid]),
     chosen by an option for debugging; the default, [Dfs], never
     delays an equation, and it is the one modelled. With it
     [final_typing_env] is [current_typing_env].
   - [names_to_avoid] is not in the compiler. A variable that the
     compiler makes ([Variable.create], in types/env/join_env.ml; meet
     itself makes none) is different from every variable made before.
     The model has no such supply: the join is to make variables that
     are not in this list and that no environment it is given knows,
     and to add them to it, and meet hands the list on from one branch
     of a disjunction to the next, so that two branches do not make the
     same variable. Nothing reads the list but to avoid its names; no
     statement depends on which names are made. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaTypingEnv FlambdaExpandHead.
Import ListNotations.

(* [Meet_env.meet_return_value]: the result of a meet is one of its
   inputs, either of them, or something else. *)
Inductive meet_return_value (A : Type) : Type :=
  | Left_input
  | Right_input
  | Both_inputs
  | New_result (a : A).

Arguments Left_input {A}.
Arguments Right_input {A}.
Arguments Both_inputs {A}.
Arguments New_result {A} a.

(* [Meet_and_n_way_join.extract_value]. *)
Definition extract_value {A : Type} (res : meet_return_value A)
    (left right : A) : A :=
  match res with
  | Left_input => left
  | Right_input => right
  | Both_inputs => left
  | New_result value => value
  end.

(* [Meet_env.t]. *)
Module Meet_env.

  Record t : Type := {
    typing_env : Typing_env.t;
    adding_equations_for_names : list name;
    names_to_avoid : list variable
  }.

  (* [Meet_env.create]. *)
  Definition create (typing_env : Typing_env.t) : t :=
    {| typing_env := typing_env;
       adding_equations_for_names := [];
       names_to_avoid := [] |}.

  (* [Meet_env.current_typing_env]. *)
  Definition current_typing_env (env : t) : Typing_env.t := typing_env env.

End Meet_env.

(* [Meet_env.meet_result]. *)
Module Meet_result.
  Inductive t (A : Type) : Type :=
    | Bottom (r : meet_return_value unit)
    | Ok (r : meet_return_value A) (env : Meet_env.t).
  Arguments Bottom {A} r.
  Arguments Ok {A} r env.
End Meet_result.

(* [Meet_env.meet_expanded_head]. *)
Definition meet_expanded_head : Type :=
  Meet_env.t -> Expanded_type.t -> Expanded_type.t ->
  option (Meet_result.t Expanded_type.t).
