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

(* FIRST LEMMAS ABOUT THE HANDLER OF [add_use] OF env/Continuation_uses.v.
   Read proofs/README.md first. [add_use] has a handler for a fatal error
   that prints a context and raises the fatal error again with
   [Printexc.raise_with_backtrace]; four functions of the port have such a
   handler. The lemmas say what follows from the contract of that function
   alone, and what more a proof needs to say that the whole ends in a fatal
   error. They are not a specification of the file. A file of the real
   build only: nothing of it is extracted. It has no axiom and no parameter.
   It follows no file of the compiler.

   WHAT IS ASSUMED. By [add_use_returns]: the contract of
   [Printexc.raise_with_backtrace] (contracts/Printexc.v). By
   [add_use_fatal_only]: that contract, the contract of
   [Printexc.get_raw_backtrace], and six premises about the calls of
   [add_use] itself, which the second section states. Two of them name a
   call by its format string, which is the one of env/Continuation_uses.v
   (the compiler's). *)

From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort.decl Require Continuation Downwards_env Flambda2_types
  Flambda_arity Flambda_colours Format One_continuation_use Printexc.
From SimplifyPort.env Require Continuation_uses.
From SimplifyPort.contracts Require Port_monad Printexc.
Local Open Scope string_scope.

Module CU := SimplifyPort.env.Continuation_uses.
Module DE := Downwards_env.
Module T := Flambda2_types.
Module U := One_continuation_use.
Module Kit_contract := SimplifyPort.contracts.Port_monad.
Module Printexc_contract := SimplifyPort.contracts.Printexc.

(* ------------------------------------------------------------------ *)
(* With the contract of [Printexc.raise_with_backtrace] alone         *)
(* ------------------------------------------------------------------ *)

Section Returns.

  Hypothesis raises : Printexc_contract.raise_with_backtrace_raises.

  (* If [add_use] returns, it returns [t] with [use] before its uses. The
     handler never returns: that is all that the contract gives, and all
     that this needs. NOTHING IS SAID OF AN EXCEPTION: the handler calls
     four declared functions before it raises again, and one of them could
     raise an exception that is not a fatal error. The proof names neither
     the body nor the handler: the rules take them from the goal. *)
  Theorem add_use_returns (t : CU.t) (use : U.t) :
    spec (fun _ => True) (CU.add_use t use)
      (fun v _ => v = CU.update_uses t (use :: CU.uses t)) any_exn.
  Proof.
    intros n s _. unfold CU.add_use. apply wp_try_with.
    (* The handler never returns. *)
    match goal with
    | |- wp _ _ (handled _ ?h _) _ _ => assert (Hh : forall p s', h p s')
    end.
    { intros [] s0. cbv beta. apply wp_bind.
      apply wp_any; [intros bt s1 | intros; exact I].
      apply wp_seq. apply wp_any; [intros done s2 | intros; exact I].
      eapply wp_weaken; [apply raises | intros a s3 [] | intros; exact I]. }
    match goal with
    | |- wp _ _ ?E _ _ => assert (HE : forall x s', E x s')
    end.
    { intros x s0. unfold handled.
      destruct (exn_match Fatal_error x) as [p | ];
        [exact (Hh p s0) | exact I]. }
    (* The body: two declared functions, a test, a fatal error or the
       value. *)
    apply wp_bind. apply wp_any; [intros arity s1 | exact HE].
    apply wp_seq. apply wp_bind. apply wp_any; [intros b s2 | exact HE].
    destruct (negb b).
    - apply wp_never_returns; [ | exact HE].
      intros a s3. apply fatal_errorf_args_never_returns.
    - apply wp_ret. apply wp_ret. reflexivity.
  Qed.

End Returns.

(* ------------------------------------------------------------------ *)
(* What "returns, or ends in a fatal error" needs                     *)
(* ------------------------------------------------------------------ *)

Section Fatal_only.

  Variables (t : CU.t) (use : U.t).

  (* THE TWO CONTRACTS of contracts/Printexc.v. *)
  Hypothesis raises : Printexc_contract.raise_with_backtrace_raises.
  Hypothesis gets : Printexc_contract.get_raw_backtrace_returns.

  (* SIX PREMISES ABOUT THE CALLS OF [add_use]. Each says of one call that
     it returns or ends in a fatal error ([returns_or_fatal]), and no more.
     They are not in contracts/: each is about this function's own call,
     with these arguments. A premise of this form is no contradiction
     ([returns_or_fatal_ret], [returns_or_fatal_raise_fatal]). *)

  (* Three calls of the body. The handler calls [U.arg_types use] too. *)
  Hypothesis arg_types_ok : returns_or_fatal (U.arg_types use).
  Hypothesis arity_of_list_ok :
    forall types : list T.t, returns_or_fatal (T.arity_of_list types).
  Hypothesis equal_ok :
    forall arity : Flambda_arity.t_Unarized,
      returns_or_fatal
        (Flambda_arity.equal_ignoring_subkinds arity (CU.arity t)).

  (* The message of the body's fatal error, with its two printers: the
     contract of the kit for one message (contracts/Port_monad.v). *)
  Hypothesis message_ok :
    forall arity : Flambda_arity.t_Unarized,
      Kit_contract.prints_or_fatal
        "Arity of use (%a) doesn't match continuation's arity (%a)"
        (Fmt_cons Flambda_arity.print
           (Fmt_cons arity
              (Fmt_cons Flambda_arity.print
                 (Fmt_cons (CU.arity t) Fmt_nil)))).

  (* Two calls of the handler: the environment of the use, and the printing
     of the context with its six printers, of which one is this file's own
     [print]. *)
  Hypothesis env_at_use_ok : returns_or_fatal (U.env_at_use use).
  Hypothesis context_ok :
    forall (env : DE.t) (types : list T.t),
      returns_or_fatal
        (Format.eprintf10
           "
%tContext is:%t adding use of %a with arg types@ (%a);@ existing uses:@ %a; environment:@ %a"
           Flambda_colours.error Flambda_colours.pop Continuation.print
           (CU.continuation t)
           (Format.pp_print_list (Some Format.pp_print_space) T.print)
           types CU.print t DE.print env).

  (* [add_use] returns [t] with [use] before its uses, or ends in a fatal
     error (or the run is out of fuel). *)
  Theorem add_use_fatal_only :
    spec (fun _ => True) (CU.add_use t use)
      (fun v _ => v = CU.update_uses t (use :: CU.uses t)) fatal_only.
  Proof.
    intros n s _. unfold CU.add_use. apply wp_try_with.
    (* The handler ends in a fatal error. *)
    match goal with
    | |- wp _ _ (handled _ ?h _) _ _ => assert (Hh : forall p s', h p s')
    end.
    { intros [] s0. cbv beta. apply wp_bind.
      apply wp_returns_or_fatal;
        [exact gets | intros bt s1 | intros s1; reflexivity].
      apply wp_seq. apply wp_bind.
      apply wp_returns_or_fatal;
        [exact env_at_use_ok | intros env s2 | intros s2; reflexivity].
      apply wp_bind.
      apply wp_returns_or_fatal;
        [exact arg_types_ok | intros types s3 | intros s3; reflexivity].
      unfold papp2. apply wp_bind, wp_ret.
      apply wp_returns_or_fatal;
        [apply context_ok | intros done s4 | intros s4; reflexivity].
      apply (Printexc_contract.reraise_fatal_only raises). }
    (* So the fatal error of the body is taken, and the whole ends in a
       fatal error. *)
    match goal with
    | |- wp _ _ ?E _ _ => assert (HE : forall s', E fatal_exn s')
    end.
    { intros s0. unfold handled, fatal_exn. rewrite exn_match_make.
      exact (Hh tt s0). }
    (* The body. *)
    apply wp_bind. apply wp_bind.
    apply wp_returns_or_fatal;
      [exact arg_types_ok | intros types s1 | exact HE].
    apply wp_returns_or_fatal;
      [apply arity_of_list_ok | intros arity s2 | exact HE].
    apply wp_seq. apply wp_bind.
    apply wp_returns_or_fatal; [apply equal_ok | intros b s3 | exact HE].
    destruct (negb b).
    - unfold fatal_errorf4.
      eapply wp_weaken;
        [apply Kit_contract.fatal_errorf_args_fatal_only, message_ok
        | intros a s4 H; exact H | intros x s4 ->; apply HE].
    - apply wp_ret. apply wp_ret. reflexivity.
  Qed.

End Fatal_only.
