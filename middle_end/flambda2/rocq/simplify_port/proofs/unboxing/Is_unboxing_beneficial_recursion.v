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

(* A FIRST LEMMA ABOUT A RECURSIVE FUNCTION:
   [filter_non_beneficial_decisions] of unboxing/Is_unboxing_beneficial.v,
   which takes a fuel. Read proofs/README.md first. The lemma is about the
   one case of the function that makes no call. It shows the form of a
   statement about a function with a fuel: it is for every fuel, and where
   the fuel is out there is nothing to prove. It is not a specification of
   the file. A file of the real build only: nothing of it is extracted. It
   has no axiom and no parameter. It follows no file of the compiler.

   WHAT IS ASSUMED: nothing. *)

From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort.decl Require Unboxing_types.
From SimplifyPort.unboxing Require Is_unboxing_beneficial.

Module U := SimplifyPort.decl.Unboxing_types.
Module B := SimplifyPort.unboxing.Is_unboxing_beneficial.

(* A decision not to unbox is returned as it is, in the state as it was,
   and nothing is raised: for every fuel of the function and every fuel of
   the run. (With the fuel [Out] the run is out of fuel, and the statement
   says nothing of it.) *)
Theorem do_not_unbox_stays (fuel : fuel) (reason : U.do_not_unbox_reason)
    (n : nat) (s : ocaml_state) :
  wp (B.filter_non_beneficial_decisions fuel (U.Do_not_unbox reason))
    (fun decision s' => decision = U.Do_not_unbox reason /\ s' = s)
    no_exn n s.
Proof.
  destruct fuel as [ | fuel]; [apply wp_out_of_fuel | ].
  simpl. apply wp_ret. split; reflexivity.
Qed.

(* With a fuel that is not out, as an equation of the run. *)
Corollary do_not_unbox_runs (fuel : fuel) (reason : U.do_not_unbox_reason)
    (n : nat) (s : ocaml_state) :
  run (B.filter_non_beneficial_decisions (More fuel) (U.Do_not_unbox reason))
    n s
  = Returned (U.Do_not_unbox reason) s.
Proof. reflexivity. Qed.
