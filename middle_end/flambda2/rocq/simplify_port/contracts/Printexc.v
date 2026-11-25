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

(* THE CONTRACTS OF THE PARAMETERS OF decl/Printexc.v. Read
   contracts/README.md first. A file of the real build only: nothing of it
   is extracted. It has no axiom and no parameter. It follows no file of the
   compiler.

   Today: [Printexc.raise_with_backtrace] and [Printexc.get_raw_backtrace]:
   what the handlers that print a context and raise the fatal error again
   call. *)

From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort.decl Require Printexc.

(* Of any function of the type of [Printexc.raise_with_backtrace]: it does
   not return; if it raises, it raises the value that it is given.
   NOTHING IS SAID OF THE STATE AFTER IT: OCaml writes its record of the last
   backtrace there, which is not in [ocaml_state] and of which no statement
   speaks (monad/real/Port_monad.v). Nothing is said of a run that is out of
   fuel. *)
Definition raises_what_it_is_given
    (raise : forall A : Type, exn -> decl.Printexc.raw_backtrace -> M A)
    : Prop :=
  forall (A : Type) (e : exn) (bt : decl.Printexc.raw_backtrace) (n : nat)
    (s : ocaml_state),
    wp (raise A e bt) (fun _ _ => False) (fun x _ => x = e) n s.

(* THE CONTRACT of [Printexc.raise_with_backtrace]. *)
Definition raise_with_backtrace_raises : Prop :=
  raises_what_it_is_given (@decl.Printexc.raise_with_backtrace).

(* A model: the kit's [raise] of a value. *)
Example raise_with_backtrace_has_a_model :
  raises_what_it_is_given (fun A e _ => raise_exn e).
Proof. intros A e bt n s. reflexivity. Qed.

(* With the contract, it never returns. *)
Theorem raise_with_backtrace_never_returns :
  raise_with_backtrace_raises ->
  forall (A : Type) (e : exn) (bt : decl.Printexc.raw_backtrace) (n : nat)
    (s : ocaml_state) (a : A) (s' : ocaml_state),
    run (decl.Printexc.raise_with_backtrace e bt : M A) n s <> Returned a s'.
Proof.
  intros Hraise A e bt n s a s' Hrun.
  pose proof (Hraise A e bt n s) as H. unfold wp in H.
  rewrite Hrun in H. exact H.
Qed.

(* With the contract, a fatal error that is raised again ends in a fatal
   error (or the run is out of fuel): whatever [Q] says of a value. *)
Theorem reraise_fatal_only :
  raise_with_backtrace_raises ->
  forall (A : Type) (bt : decl.Printexc.raw_backtrace)
    (Q : A -> ocaml_state -> Prop) (n : nat) (s : ocaml_state),
    wp (decl.Printexc.raise_with_backtrace (exn_make Fatal_error tt) bt)
      Q fatal_only n s.
Proof.
  intros Hraise A bt Q n s.
  eapply wp_weaken; [apply Hraise | intros a s' [] | ].
  intros x s' ->. reflexivity.
Qed.

(* Of any function of the type of [Printexc.get_raw_backtrace]: it returns,
   or ends in a fatal error. Nothing is said of what it returns: the model
   has no backtrace. *)
Definition gets_or_fatal
    (get : unit -> M decl.Printexc.raw_backtrace) : Prop :=
  returns_or_fatal (get tt).

(* THE CONTRACT of [Printexc.get_raw_backtrace]. *)
Definition get_raw_backtrace_returns : Prop :=
  gets_or_fatal decl.Printexc.get_raw_backtrace.

(* A model. The type of backtraces is a parameter, and nothing says that it
   has a value: so the model is one that ends in a fatal error. *)
Example get_raw_backtrace_has_a_model :
  gets_or_fatal (fun _ => raise_ Fatal_error tt).
Proof. unfold gets_or_fatal. apply returns_or_fatal_raise_fatal. Qed.
