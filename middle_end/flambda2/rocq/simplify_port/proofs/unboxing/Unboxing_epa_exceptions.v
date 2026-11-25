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

(* TWO DECLARATIONS OF ONE EXCEPTION OF OCAML. Read proofs/README.md first.
   [Unboxing_epa.Invalid_apply_cont] is declared twice: in
   decl/Unboxing_epa.v, and unboxing/Unbox_continuation_params.v handles
   that one; and in the ported file unboxing/Unboxing_epa.v, which raises
   its own. Each declaration is a parameter. These lemmas say that, with the
   contracts of the two names, the two are one exception. A file of the real
   build only: nothing of it is extracted. It has no axiom and no parameter.
   It follows no file of the compiler.

   WHAT IS ASSUMED: the names of the exceptions
   (contracts/Unboxing_epa.v, contracts/ported/unboxing/Unboxing_epa.v). *)

From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort.decl Require Unboxing_epa.
From SimplifyPort.unboxing Require Unboxing_epa.
From SimplifyPort.contracts Require Unboxing_epa.
From SimplifyPort.contracts.ported.unboxing Require Unboxing_epa.
Local Open Scope string_scope.

Module Declared := SimplifyPort.decl.Unboxing_epa.
Module Ported := SimplifyPort.unboxing.Unboxing_epa.
Module Declared_contract := SimplifyPort.contracts.Unboxing_epa.
Module Ported_contract := SimplifyPort.contracts.ported.unboxing.Unboxing_epa.

Section Two_declarations.

  (* THE TWO CONTRACTS: each declaration has the name that the rule of names
     gives it, and the rule gives the two the same name. *)
  Hypothesis declared_named : Declared_contract.Invalid_apply_cont_named.
  Hypothesis ported_named : Ported_contract.Invalid_apply_cont_named.

  (* A handler for the declared one takes what the ported file raises. *)
  Theorem declared_takes_ported :
    exn_match Declared.Invalid_apply_cont
      (exn_make Ported.Invalid_apply_cont tt) = Some tt.
  Proof. exact (named_same _ _ _ tt declared_named ported_named). Qed.

  (* And the other way. *)
  Theorem ported_takes_declared :
    exn_match Ported.Invalid_apply_cont
      (exn_make Declared.Invalid_apply_cont tt) = Some tt.
  Proof. exact (named_same _ _ _ tt ported_named declared_named). Qed.

  (* The two are one exception. *)
  Theorem the_two_are_one :
    Declared.Invalid_apply_cont = Ported.Invalid_apply_cont.
  Proof.
    pose proof (proj1 (named_is _ _) declared_named) as Hd.
    pose proof (proj1 (named_is _ _) ported_named) as Hp.
    rewrite Hd, Hp. reflexivity.
  Qed.

  (* As a run: a body that raises the ported one, under a handler for the
     declared one. That is the form of the handler of
     unboxing/Unbox_continuation_params.v. *)
  Theorem handler_runs (A : Type) (handler : unit -> M A) (n : nat)
      (s : ocaml_state) :
    run (try_with (fun _ => raise_ Ported.Invalid_apply_cont tt)
           Declared.Invalid_apply_cont handler) n s
    = run (handler tt) n s.
  Proof.
    rewrite run_try_with, run_raise, declared_takes_ported. reflexivity.
  Qed.

End Two_declarations.

(* The other exception of the ported file is another exception: a handler
   for [Invalid_apply_cont] lets it pass. From the two names. *)
Theorem another_passes :
  Declared_contract.Invalid_apply_cont_named ->
  Ported_contract.Prevent_current_unboxing_named ->
  exn_match Declared.Invalid_apply_cont
    (exn_make Ported.Prevent_current_unboxing tt) = None.
Proof.
  unfold Declared_contract.Invalid_apply_cont_named,
    Ported_contract.Prevent_current_unboxing_named.
  intros. exn_other.
Qed.

(* A fatal error passes a handler for [Invalid_apply_cont] too. *)
Theorem fatal_error_passes :
  Declared_contract.Invalid_apply_cont_named ->
  exn_match Declared.Invalid_apply_cont fatal_exn = None.
Proof. intro H. exact (fatal_passes H eq_refl). Qed.
