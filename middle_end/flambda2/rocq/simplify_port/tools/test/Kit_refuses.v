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
   fail. This file follows no file of the compiler; [make tooltest] compiles
   it. *)

From SimplifyPort Require Import Port_monad.
Local Open Scope string_scope.

Parameter tick : unit -> M unit.

(* A partial application that is in truth a whole one would store a
   computation: [papp1] wants a function that still expects an argument. *)
Fail Definition stored_by_papp : M unit :=
  let* action := papp1 (fun _ : unit => tick tt) tt in
  ret tt.

(* A computation is not a function of the world for the ported files. *)
Fail Definition run_by_hand (w : world) : result unit := tick tt w.

(* A function is not a computation. *)
Fail Definition function_as_computation : M unit :=
  let* x := (fun w : world => Returned tt w) in
  ret x.
