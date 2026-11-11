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



(* What meet uses of the grammar of types and of its neighbours, and
   that FlambdaTypeGrammar.v and FlambdaTypingEnv.v do not have yet.

   This file is to be reviewed, each definition against the function of
   the compiler that it names. It holds definitions only and it
   extracts. Every definition here belongs in another file, which is
   not this stream's to edit: it is to move there, under the same name,
   when its owner takes it, and this file is to go. They are:
   - of middle_end/flambda2/types/grammar/type_grammar.ml, for
     FlambdaTypeGrammar.v (T1): [const_of_naked_number],
     [must_be_singleton], [head_of_kind_value_null],
     [head_of_kind_value_tagged_immediate],
     [set_of_closures_contents_equal], [_subset] and [_union];
   - of types/env/typing_env.ml, for FlambdaTypingEnv.v (T2):
     [kind_of_simple];
   - [sort_numbers], a sort of integers, which the module of maps
     has not and is not to have.

   The differences from the compiler:
   - [must_be_singleton]: the outer [None] is the fatal error of the
     compiler ("Immediates case returned wrong kind of constant"). A
     set of numbers is a list here, and has one number if all its
     numbers are the same one ([Keyed.get_singleton]).
   - [kind_of_simple] is [Simple.kind]. A variable of the compiler
     carries its kind; a variable of the model does not, and its kind
     is that of the type that the environment has for it
     (FlambdaTypingEnv.v). [None] where the environment has none.
   - A set of slots is a list, compared as a set. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningBoolSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaTypingEnv.
Import ListNotations.

(* ======================================================================== *)
(* Of the grammar of types                                                  *)
(* ======================================================================== *)

(* [Reg_width_const.naked_immediate], [naked_float32], ...: the constant
   that a number of a kind is. *)
Definition const_of_naked_number (k : naked_number_kind) (i : Z) : const :=
  match k with
  | Kind_naked_immediate => Naked_immediate i
  | Kind_naked_float32 => Naked_float32 i
  | Kind_naked_float => Naked_float i
  | Kind_naked_int8 => Naked_int8 i
  | Kind_naked_int16 => Naked_int16 i
  | Kind_naked_int32 => Naked_int32 i
  | Kind_naked_int64 => Naked_int64 i
  | Kind_naked_nativeint => Naked_nativeint i
  | Kind_naked_vec128 => Naked_vec128 i
  | Kind_naked_vec256 => Naked_vec256 i
  | Kind_naked_vec512 => Naked_vec512 i
  | Kind_naked_mask => Naked_mask i
  end.

(* [Simple.must_be_const]. *)
Definition simple_must_be_const (s : simple) : option const :=
  match s with
  | Const c => Some c
  | Var _ | Symbol _ => None
  end.

(* [Type_grammar.must_be_singleton]: the constant that a type has for
   only value, if the type shows it. The outer [None] is a fatal error
   of the compiler. *)
Fixpoint must_be_singleton (t : flambda_type) : option (option const) :=
  match t with
  | Type_value ty =>
    match ty with
    | Unknown | Bottom => Some None
    | Ok (Equals simple) => Some (simple_must_be_const simple)
    | Ok
        (No_alias
           (Head_of_kind_value (Ok (Variant _ immediates _ blocks _ _))
              Not_null)) =>
      match blocks with
      | Or_unknown.Unknown => Some None
      | Or_unknown.Known blocks =>
        if negb (row_like_for_blocks_is_bottom blocks)
        then Some None
        else
          match immediates with
          | Or_unknown.Unknown => Some None
          | Or_unknown.Known immediates =>
            match must_be_singleton immediates with
            | None => None
            | Some None => Some None
            | Some (Some (Naked_immediate i)) =>
              Some (Some (Tagged_immediate i))
            | Some (Some (Poison (Naked_number Kind_naked_immediate))) =>
              Some (Some (Poison Value))
            | Some (Some _) => None
            end
          end
      end
    | Ok (No_alias _) => Some None
    end
  | Type_naked_immediate ty =>
    match ty with
    | Unknown | Bottom => Some None
    | Ok (Equals simple) => Some (simple_must_be_const simple)
    | Ok (No_alias head) =>
      match naked_immediates head with
      | Or_unknown.Unknown => Some None
      | Or_unknown.Known numbers =>
        Some (option_map Naked_immediate (Keyed.get_singleton Z.eqb numbers))
      end
    end
  | Type_naked_number k ty =>
    match ty with
    | Unknown | Bottom => Some None
    | Ok (Equals simple) => Some (simple_must_be_const simple)
    | Ok (No_alias numbers) =>
      Some
        (option_map (const_of_naked_number k)
           (Keyed.get_singleton Z.eqb numbers))
    end
  | Type_rec_info _ | Type_region _ => Some None
  end.

(* [Type_grammar.Head_of_kind_value.null]. *)
Definition head_of_kind_value_null : head_of_kind_value :=
  Head_of_kind_value Bottom (Maybe_null None).

(* [Type_grammar.Head_of_kind_value.create_tagged_immediate]. *)
Definition head_of_kind_value_tagged_immediate (imm : Z)
    : head_of_kind_value :=
  Head_of_kind_value
    (Ok
       (Variant None (Or_unknown.Known (this_naked_immediate imm)) None
          (Or_unknown.Known row_like_for_blocks_bottom) No_extensions false))
    Not_null.

(* [Set_of_closures_contents.equal], [subset] and [union]. *)
Definition set_of_closures_contents_equal
    (contents contents' : set_of_closures_contents) : bool :=
  Keyed.same_keys_b Pos.eqb (contents_closures contents)
    (contents_closures contents')
  && Keyed.same_keys_b Pos.eqb (contents_value_slots contents)
       (contents_value_slots contents').

Definition set_of_closures_contents_subset
    (contents contents' : set_of_closures_contents) : bool :=
  all_among (contents_closures contents) (contents_closures contents')
  && all_among (contents_value_slots contents)
       (contents_value_slots contents').

Definition set_of_closures_contents_union
    (contents contents' : set_of_closures_contents)
    : set_of_closures_contents :=
  Set_of_closures_contents
    (dedup (contents_closures contents ++ contents_closures contents'))
    (dedup (contents_value_slots contents ++ contents_value_slots contents')).

(* ======================================================================== *)
(* Of the module of maps                                                    *)
(* ======================================================================== *)

(* Integers in increasing order. *)
Fixpoint insert_number (i : Z) (sorted : list Z) : list Z :=
  match sorted with
  | [] => [i]
  | j :: rest => if Z.leb i j then i :: sorted else j :: insert_number i rest
  end.

Definition sort_numbers (numbers : list Z) : list Z :=
  fold_right insert_number [] numbers.

(* ======================================================================== *)
(* Of the typing environment                                                *)
(* ======================================================================== *)

(* [Simple.kind], read from the environment for a variable. *)
Definition kind_of_simple (tenv : Typing_env.t) (simple : simple)
    : option flambda_kind :=
  match simple with
  | Const c => Some (kind_of_const c)
  | Symbol _ => Some Value
  | Var x => option_map kind (Typing_env.find tenv (Name_var x) None)
  end.
