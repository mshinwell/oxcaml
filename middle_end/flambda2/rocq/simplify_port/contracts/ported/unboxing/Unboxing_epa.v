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

(* THE CONTRACTS OF THE PARAMETERS THAT THE PORTED FILE
   unboxing/Unboxing_epa.v DECLARES ITSELF. Read contracts/README.md first.
   A file of the real build only: nothing of it is extracted. It has no
   axiom and no parameter. It follows no file of the compiler.

   Today: the names of the file's two exceptions. *)

From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort.unboxing Require Unboxing_epa.
Local Open Scope string_scope.

(* THE CONTRACT: the name of [Invalid_apply_cont], by the rule of names. It
   is the name that decl/Unboxing_epa.v's declaration of the same exception
   of OCaml has (contracts/Unboxing_epa.v). *)
Definition Invalid_apply_cont_named : Prop :=
  named SimplifyPort.unboxing.Unboxing_epa.Invalid_apply_cont
    "Unboxing_epa.Invalid_apply_cont".

(* THE CONTRACT: the name of [Prevent_current_unboxing]. *)
Definition Prevent_current_unboxing_named : Prop :=
  named SimplifyPort.unboxing.Unboxing_epa.Prevent_current_unboxing
    "Unboxing_epa.Prevent_current_unboxing".

(* A model: the two exceptions of those names. They are two exceptions. *)
Example the_names_have_a_model :
  named ({| exception_name := "Unboxing_epa.Invalid_apply_cont" |}
          : exception unit)
    "Unboxing_epa.Invalid_apply_cont"
  /\ named ({| exception_name := "Unboxing_epa.Prevent_current_unboxing" |}
             : exception unit)
       "Unboxing_epa.Prevent_current_unboxing".
Proof. split; reflexivity. Qed.
