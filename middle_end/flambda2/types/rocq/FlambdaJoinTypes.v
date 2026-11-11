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


(* The n-way join of types: the functions of
   middle_end/flambda2/types/meet_and_n_way_join.ml that join.

   This file is to be reviewed line by line against that file. It holds
   definitions only. What the join guarantees is FlambdaJoinSpec.v.

   It is the first part of the transcription: the one function of the
   thirty that is known not to give an upper bound, so that
   FlambdaJoinSpec.v can state the failure of a function of the model
   and not of a type written by hand. The others are to come, and the
   header will then say function by function what the model has.

   What is here:
   - [n_way_join_function_type]: the compiler's function of that name.
     A function type of the model has no [rec_info]
     (FlambdaTypeGrammar.v), so the join of the [rec_info]s is not
     there, nor the join environment, which only that join threads.
     A consequence for the differential tests: where every function
     type is known and all name one code, the model answers that code;
     the compiler answers unknown instead if the join of the
     [rec_info]s is unknown (their heads differ). So the compiler's
     answer may be unknown where the model's is known, never the
     reverse, and never a different code.
     With invariant checks the compiler stops on an empty list; without
     them it answers unknown, as here.
   - [n_way_join_function_types]: of [n_way_join_closures_entry], the
     part that joins the function types of the entries. For each
     function slot that some entry has a function type for, it joins
     the function types of the entries that have one. An entry that has
     none for the slot is left out of that join: it is not taken to
     say that the code is unknown.
   - [n_way_join_function_types_proposed]: not in the compiler. The
     same with the one change that makes it an upper bound: a function
     slot is kept only if every entry has a function type for it, as
     [n_way_join_generic_product] does for the closures and the value
     slots, and as the binary join does ([join_closures_entry] in
     meet_and_join.ml).

   The lists of contributors are in the reverse of the order of the
   entries, as in the compiler; [n_way_join_function_type] does not
   depend on the order. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaJoinEnv.
Import ListNotations.

(* The function types of a list, if none is unknown. *)
Fixpoint known_function_types
    (func_types : list (Index.t * Or_unknown.t function_type))
    : option (list function_type) :=
  match func_types with
  | [] => Some []
  | (_, Or_unknown.Unknown) :: _ => None
  | (_, Or_unknown.Known func_type) :: func_types =>
    match known_function_types func_types with
    | None => None
    | Some known => Some (func_type :: known)
    end
  end.

(* [n_way_join_function_type]: the code is known if every function type
   is known and all name the same code. *)
Definition n_way_join_function_type
    (func_types : list (Index.t * Or_unknown.t function_type))
    : Or_unknown.t function_type :=
  match known_function_types func_types with
  | None | Some [] => Or_unknown.Unknown
  | Some (func_type :: func_types) =>
    if forallb
         (fun func_type' =>
            Pos.eqb (function_type_code_id func_type)
              (function_type_code_id func_type'))
         func_types
    then Or_unknown.Known func_type
    else Or_unknown.Unknown
  end.

(* The function types of the entries, slot by slot, as
   [n_way_join_closures_entry] gathers them: the entries that have none
   for a slot are not among its contributors. *)
Definition gather_function_types
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    : finite_map (list (Index.t * Or_unknown.t function_type)) :=
  match entries with
  | [] => []
  | (id1, function_types1) :: entries =>
    fold_left
      (fun function_types entry =>
         merge
           (fun vals_opt val2_opt =>
              match vals_opt, val2_opt with
              | None, None => None
              | None, Some val2 => Some [(fst entry, val2)]
              | Some vals, None => Some vals
              | Some vals, Some val2 => Some ((fst entry, val2) :: vals)
              end)
           function_types (snd entry))
      entries
      (map_values (fun func_type => [(id1, func_type)]) function_types1)
  end.

Definition n_way_join_function_types
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    : finite_map (Or_unknown.t function_type) :=
  map_values n_way_join_function_type (gather_function_types entries).

(* The same, keeping a slot only if every entry has a function type for
   it. *)
Definition gather_function_types_proposed
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    : finite_map (list (Index.t * Or_unknown.t function_type)) :=
  match entries with
  | [] => []
  | (id1, function_types1) :: entries =>
    fold_left
      (fun function_types entry =>
         merge
           (fun vals_opt val2_opt =>
              match vals_opt, val2_opt with
              | None, _ | _, None => None
              | Some vals, Some val2 => Some ((fst entry, val2) :: vals)
              end)
           function_types (snd entry))
      entries
      (map_values (fun func_type => [(id1, func_type)]) function_types1)
  end.

Definition n_way_join_function_types_proposed
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    : finite_map (Or_unknown.t function_type) :=
  map_values n_way_join_function_type (gather_function_types_proposed entries).
