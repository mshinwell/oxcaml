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
   bound to, and how a closure is read.

   This file is to be reviewed: [value], [statically_allocated_value]
   and [closure_of]. It holds definitions only. FlambdaSemanticsSpec.v
   exports it, so a file that imports the semantics has what is here.

   A value is a constant (a tagged immediate, a naked number of any kind,
   null or poison), a closure, or a pointer to what a symbol is bound to.
   A symbol is a value by itself, whether or not it is bound, and what it
   points to is in the static environment. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
Import ListNotations.

(* ======================================================================== *)
(* Values                                                                   *)
(* ======================================================================== *)

(* The values of variables: constants, closures made by a [Let], and
   pointers to what symbols are bound to. A closure is the code of its
   function and the values of its value slots. (The warning silenced is
   about induction schemes through the pairs of lists, which nothing uses
   yet.) *)
#[local] Set Warnings "-register-all".
Inductive value : Type :=
  | Value_const (c : const)
  | Value_closure (code : code_id) (value_slots : list (value_slot * value))
  | Value_symbol (s : symbol).

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
  | Value_const _ => None
  end.
