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

(* THE CONTRACTS OF THE KIT'S OWN PARAMETERS (monad/real/Port_monad.v). Read
   contracts/README.md first. A file of the real build only: nothing of it
   is extracted. It has no axiom and no parameter. It follows no file of the
   compiler.

   Today: the printing of a fatal error. *)

From SimplifyPort Require Import Port_monad Kit_laws.
Local Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* The printing of a fatal error                                      *)
(* ------------------------------------------------------------------ *)

(* [Misc.fatal_error] and [Misc.fatal_errorf] print before they raise, and
   the printing runs the printers that the message is given for [%a]. A
   printer may raise an exception of its own: the fatal error then ends in
   THAT exception, and a handler for it would take it. So "this fatal error
   ends in a fatal error" is a statement about one message and its
   arguments. It is not stated of every message: the kit does not know which
   of the arguments are printers, and of some printers it would be false. *)

(* Of any function of the type of [print_fatal_message]: with this format
   and these arguments it returns, or ends in a fatal error. Nothing is
   said of the state after it, nor of a run that is out of fuel. *)
Definition prints_or_fatal_of (print : string -> fmt_args -> M unit)
    (format : string) (args : fmt_args) : Prop :=
  returns_or_fatal (print format args).

(* THE CONTRACT of one fatal error: of its format and its arguments. *)
Definition prints_or_fatal (format : string) (args : fmt_args) : Prop :=
  prints_or_fatal_of print_fatal_message format args.

(* THE CONTRACT of every [Misc.fatal_error msg]: the message is a string,
   and no printer of the port is run. *)
Definition fatal_error_prints : Prop :=
  forall message : string, prints_or_fatal "%s" (Fmt_cons message Fmt_nil).

(* A model: a printing that returns. *)
Example prints_or_fatal_has_a_model (format : string) (args : fmt_args) :
  prints_or_fatal_of (fun _ _ => ret tt) format args.
Proof. apply returns_or_fatal_ret. Qed.

(* WITH THE CONTRACT, THE FATAL ERROR ENDS IN A FATAL ERROR, or the run is
   out of fuel: whatever [Q] says of a value, since none is returned.
   Without the contract it never returns (Kit_laws.v), and no more.
   [fatal_errorfN] is [fatal_errorf_args] of its arguments: unfold it. *)
Theorem fatal_errorf_args_fatal_only {A : Type} (format : string)
    (args : fmt_args) (Q : A -> ocaml_state -> Prop) (n : nat)
    (s : ocaml_state) :
  prints_or_fatal format args ->
  wp (fatal_errorf_args format args) Q fatal_only n s.
Proof.
  intro Hprint. unfold fatal_errorf_args. apply wp_bind.
  apply wp_returns_or_fatal;
    [exact Hprint | intros u s' | intros s']; reflexivity.
Qed.

Theorem fatal_error_fatal_only {A : Type} (message : string)
    (Q : A -> ocaml_state -> Prop) (n : nat) (s : ocaml_state) :
  fatal_error_prints -> wp (fatal_error message) Q fatal_only n s.
Proof.
  intro Hprint. unfold fatal_error. apply wp_bind.
  apply wp_returns_or_fatal;
    [apply Hprint | intros u s' | intros s']; reflexivity.
Qed.
