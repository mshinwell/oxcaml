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

(* THE CONTRACTS OF THE PARAMETERS OF decl/Unboxing_epa.v. Read
   contracts/README.md first. A file of the real build only: nothing of it
   is extracted. It has no axiom and no parameter. It follows no file of the
   compiler.

   Today: the name of its exception. *)

From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort.decl Require Unboxing_epa.
Local Open Scope string_scope.

(* THE CONTRACT: the name of [Unboxing_epa.Invalid_apply_cont], by the rule
   of names. The ported file of that module declares the same exception of
   OCaml, and its contract (contracts/ported/unboxing/Unboxing_epa.v) gives
   it the same name. *)
Definition Invalid_apply_cont_named : Prop :=
  named decl.Unboxing_epa.Invalid_apply_cont
    "Unboxing_epa.Invalid_apply_cont".

(* A model: the exception of that name. *)
Example Invalid_apply_cont_named_has_a_model :
  named ({| exception_name := "Unboxing_epa.Invalid_apply_cont" |}
          : exception unit)
    "Unboxing_epa.Invalid_apply_cont".
Proof. reflexivity. Qed.
