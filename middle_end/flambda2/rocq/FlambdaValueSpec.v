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

(* The values of the machine of FlambdaSemanticsSpec.v, what symbols are
   bound to, and how a value is read.

   This file is to be reviewed: [value], [kind_of_value],
   [statically_allocated_value], the observations [closure_of],
   [block_of], [boxed_number_of] and [string_of], and the statement that
   they are exclusive, which FlambdaValueProofs.v proves. The rest is
   definitions. FlambdaSemanticsSpec.v exports this file, so a file that
   imports the semantics has what is here.

   A value is a constant (a tagged immediate, a naked number of any kind,
   null or poison), a pointer to what a symbol is bound to, or something
   allocated that is immutable: a closure, a block of values, a boxed
   number. An allocated value is its contents: two of them are the same
   value when they have the same contents, and nothing tells one
   allocation from another. There is no mutable memory.

   A symbol is a value by itself, whether or not it is bound, and what it
   points to is in the static environment. So a block made by a primitive
   and a symbol bound to a block of the same tag and fields are different
   values, although no primitive tells them apart: every reading of an
   allocated value goes through an observation, which takes the static
   environment and answers the same for both. The observations are
   pairwise exclusive: a value is at most one of a closure, a block, a
   boxed number and a string ([observations_disjoint_statement]).

   A boxed number is recognised by the kind of its contents, which is
   one of the naked number kinds that have a boxed form. So the contents
   may be poison of such a kind, and a symbol bound to a boxed poison is
   a boxed number, and allocated. What a primitive does with it is the
   primitive's to say (FlambdaPrimitiveSpec.v). One that asks what a
   value is sees the box: [Is_null] answers no of it, and so does
   [Is_int] without [variant_only], and the identity returns it. Boxing
   a poison and unboxing a boxed poison have no value.

   The kind of a value is that of its constant, and [Value] for
   everything else. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
Import ListNotations.

(* ======================================================================== *)
(* Values                                                                   *)
(* ======================================================================== *)

(* The values of variables: constants, closures made by a [Let], pointers
   to what symbols are bound to, and the immutable blocks and the boxed
   numbers that primitives make. A closure is the code of its function and
   the values of its value slots. The contents of a boxed number are a
   constant, whose constructor says which number it is. (The warning
   silenced is about induction schemes through the lists, which nothing
   uses yet.) *)
#[local] Set Warnings "-register-all".
Inductive value : Type :=
  | Value_const (c : const)
  | Value_closure (code : code_id) (value_slots : list (value_slot * value))
  | Value_symbol (s : symbol)
  | Value_block (tag : Z) (fields : list value)
  | Value_boxed_number (contents : const).

(* The kind of a value. *)
Definition kind_of_value (v : value) : flambda_kind :=
  match v with
  | Value_const c => kind_of_const c
  | _ => Value
  end.

(* What a symbol points to. *)
Inductive statically_allocated_value : Type :=
  | Static_closure (code : code_id) (value_slots : list (value_slot * value))
  | Static_block (tag : Z) (fields : list value)
  | Static_boxed_number (contents : value)
  | Static_string (bytes : list Z).

(* The static environment: the code and the statically allocated values
   bound so far. *)
Record static_env : Type := Static_env {
  static_code : list (code_id * code);
  static_values : list (symbol * statically_allocated_value)
}.

Definition empty_static_env : static_env := Static_env [] [].

(* ======================================================================== *)
(* Reading an allocated value                                               *)
(* ======================================================================== *)

(* A value as a closure: one made by a [Let], or a symbol bound to one. *)
Definition closure_of (statics : static_env) (v : value)
    : option (code_id * list (value_slot * value)) :=
  match v with
  | Value_closure code value_slots => Some (code, value_slots)
  | Value_symbol s =>
    match lookup s (static_values statics) with
    | Some (Static_closure code value_slots) => Some (code, value_slots)
    | _ => None
    end
  | _ => None
  end.

(* A value as an immutable block of values, with its tag: one made by a
   primitive, or a symbol bound to one. *)
Definition block_of (statics : static_env) (v : value)
    : option (Z * list value) :=
  match v with
  | Value_block tag fields => Some (tag, fields)
  | Value_symbol s =>
    match lookup s (static_values statics) with
    | Some (Static_block tag fields) => Some (tag, fields)
    | _ => None
    end
  | _ => None
  end.

(* The kind of number a constant is, if its kind is a naked number kind
   that has a boxed form. It goes by the kind of the constant and not by
   its constructor, so a poison of such a kind is one. *)
Definition boxable_number_of_const (c : const) : option boxable_number :=
  boxable_number_of_kind (kind_of_const c).

(* The contents, if they are of a kind that has a boxed form. *)
Definition boxable_contents (c : const) : option const :=
  match boxable_number_of_const c with
  | Some _ => Some c
  | None => None
  end.

(* A value as a boxed number, by the naked number inside: one made by a
   primitive, or a symbol bound to one. The kind of the constant says
   which boxed number it is. *)
Definition boxed_number_of (statics : static_env) (v : value)
    : option const :=
  match v with
  | Value_boxed_number c => boxable_contents c
  | Value_symbol s =>
    match lookup s (static_values statics) with
    | Some (Static_boxed_number (Value_const c)) => boxable_contents c
    | _ => None
    end
  | _ => None
  end.

(* A value as an immutable string, by its bytes: a symbol bound to one. *)
Definition string_of (statics : static_env) (v : value) : option (list Z) :=
  match v with
  | Value_symbol s =>
    match lookup s (static_values statics) with
    | Some (Static_string bytes) => Some bytes
    | _ => None
    end
  | _ => None
  end.

(* Whether a value is allocated: a closure, a block, a boxed number or a
   string. A symbol bound to nothing is not. *)
Definition is_allocated (statics : static_env) (v : value) : bool :=
  is_some (closure_of statics v)
  || is_some (block_of statics v)
  || is_some (boxed_number_of statics v)
  || is_some (string_of statics v).

(* ======================================================================== *)
(* The observations are exclusive                                           *)
(* ======================================================================== *)

(* The four ways in which a value is allocated are exclusive. *)
Definition observations_disjoint_statement : Prop :=
  ∀ (statics : static_env) (v : value),
    (block_of statics v <> None
     -> closure_of statics v = None
        ∧ boxed_number_of statics v = None
        ∧ string_of statics v = None)
    ∧ (closure_of statics v <> None
       -> boxed_number_of statics v = None ∧ string_of statics v = None)
    ∧ (boxed_number_of statics v <> None -> string_of statics v = None).
