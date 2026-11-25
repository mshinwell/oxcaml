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

(* What Rocq itself refuses, by the types of the kit: each [Fail] below must
   fail. This file follows no file of the compiler; [make real] compiles it
   with the real implementation of the monad. *)

From SimplifyPort Require Import Port_monad.
Local Open Scope string_scope.

Parameter tick : unit -> M unit.

(* A partial application that is in truth a whole one would store a
   computation: [papp1] wants a function that still expects an argument. *)
Fail Definition stored_by_papp : M unit :=
  let* action := papp1 (fun _ : unit => tick tt) tt in
  ret tt.

(* A computation is not a function of the fuel and of the state for the
   ported files. *)
Fail Definition run_by_hand (n : nat) (s : ocaml_state) : result unit :=
  tick tt n s.

(* A function is not a computation. *)
Fail Definition function_as_computation : M unit :=
  let* x := (fun (n : nat) (s : ocaml_state) => Returned tt s) in
  ret x.

(* An exception can be DECLARED for any type. It can be raised, made a value
   of, or handled only if its type is one that an exception can carry: one
   that has an instance of [Carried] in the kit ([unit], [string]). *)
Parameter Carries_a_pair : exception (nat * nat).
Fail Definition raises_a_pair : M unit := raise_ Carries_a_pair (0, 0).
Fail Definition value_of_a_pair : exn := exn_make Carries_a_pair (0, 0).
Fail Definition handles_a_pair : M unit :=
  try_with (fun _ => ret tt) Carries_a_pair (fun _ => ret tt).
Fail Definition matches_a_pair : M unit :=
  match_exn (fun _ => ret tt) Carries_a_pair (fun _ => ret tt)
    (fun _ => ret tt).
