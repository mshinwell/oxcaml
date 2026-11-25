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

(* FIRST LEMMAS ABOUT THE HANDLERS OF Simplify_simple.v. Read
   proofs/README.md first. They are not a specification of the file: each
   says what one handler does with one end of its body. A file of the real
   build only: nothing of it is extracted. It has no axiom and no parameter.
   It follows no file of the compiler.

   WHAT IS ASSUMED: the name of the exception that the file declares
   (contracts/ported/Simplify_simple.v), by the two lemmas that say so. The
   other lemmas assume nothing. *)

From SimplifyPort Require Import Port_monad Kit_laws.
From SimplifyPort.decl Require Downwards_acc Flambda2_types Name_mode Simple.
From SimplifyPort Require Simplify_simple.
From SimplifyPort.contracts.ported Require Simplify_simple.
Local Open Scope string_scope.

Module DA := Downwards_acc.
Module T := Flambda2_types.
Module TE := T.Typing_env.
Module S := SimplifyPort.Simplify_simple.
Module Contract := SimplifyPort.contracts.ported.Simplify_simple.

Section Handlers.

  (* THE CONTRACT that two lemmas below use. It is a hypothesis of the
     section: a lemma that uses it has it as a premise, and the others do
     not. *)
  Hypothesis Simple_not_in_scope_named : Contract.Simple_not_in_scope_named.

  Variables (dacc : DA.t) (simple : Simple.t) (mode : Name_mode.t).
  Variables (n : nat) (s : ocaml_state).

  (* ---- [simplify_simple0]: a handler for [Not_found] around a declared
     function, [TE.type_simple_in_term_exn]. ---- *)

  (* If the body raises [Not_found], the handler's branch runs: the whole
     raises [Simple_not_in_scope]. Nothing is assumed. *)
  Lemma simple0_not_found (typing_env : TE.t) (s1 s2 : ocaml_state) :
    run (DA.typing_env dacc) n s = Returned typing_env s1 ->
    run (TE.type_simple_in_term_exn typing_env (Some mode) simple) n s1
      = Raised (exn_make Not_found tt) s2 ->
    run (S.simplify_simple0 dacc simple mode) n s
      = Raised (exn_make S.Simple_not_in_scope tt) s2.
  Proof.
    intros Henv Hbody. unfold S.simplify_simple0.
    rewrite run_bind, Henv, run_match_exn, Hbody, exn_match_make.
    reflexivity.
  Qed.

  (* If the body ends in a fatal error, the whole ends in a fatal error.
     Nothing is assumed: both exceptions are the kit's, and Rocq computes
     that their names differ. *)
  Lemma simple0_fatal (typing_env : TE.t) (s1 s2 : ocaml_state) :
    run (DA.typing_env dacc) n s = Returned typing_env s1 ->
    run (TE.type_simple_in_term_exn typing_env (Some mode) simple) n s1
      = Raised fatal_exn s2 ->
    run (S.simplify_simple0 dacc simple mode) n s = Raised fatal_exn s2.
  Proof.
    intros Henv Hbody. unfold S.simplify_simple0.
    rewrite run_bind, Henv, run_match_exn, Hbody. reflexivity.
  Qed.

  (* A failed assertion in the body passes the handler too. *)
  Lemma simple0_assert (typing_env : TE.t) (s1 s2 : ocaml_state) :
    run (DA.typing_env dacc) n s = Returned typing_env s1 ->
    run (TE.type_simple_in_term_exn typing_env (Some mode) simple) n s1
      = Raised assert_failure s2 ->
    run (S.simplify_simple0 dacc simple mode) n s = Raised assert_failure s2.
  Proof.
    intros Henv Hbody. unfold S.simplify_simple0.
    rewrite run_bind, Henv, run_match_exn, Hbody. reflexivity.
  Qed.

  (* ---- [simplify_simple_if_in_scope]: a handler for the file's own
     exception around [simplify_simple0]. ---- *)

  (* If the body raises [Simple_not_in_scope], the handler's branch runs.
     Nothing is assumed: [exn_match_make] holds of every exception. *)
  Lemma if_in_scope_not_in_scope (s' : ocaml_state) :
    run (S.simplify_simple0 dacc simple mode) n s
      = Raised (exn_make S.Simple_not_in_scope tt) s' ->
    run (S.simplify_simple_if_in_scope dacc simple mode) n s
      = Returned None s'.
  Proof.
    intro Hbody. unfold S.simplify_simple_if_in_scope.
    rewrite run_match_exn, Hbody, exn_match_make. reflexivity.
  Qed.

  (* If the body ends in a fatal error, the whole ends in a fatal error.
     THIS uses the name of the declared exception. *)
  Lemma if_in_scope_fatal (s' : ocaml_state) :
    run (S.simplify_simple0 dacc simple mode) n s = Raised fatal_exn s' ->
    run (S.simplify_simple_if_in_scope dacc simple mode) n s
      = Raised fatal_exn s'.
  Proof.
    intro Hbody. unfold S.simplify_simple_if_in_scope.
    rewrite run_match_exn, Hbody.
    rewrite (fatal_passes Simple_not_in_scope_named) by reflexivity.
    reflexivity.
  Qed.

  (* If the body returns, the value is returned. Nothing is assumed. *)
  Lemma if_in_scope_returns (ty : T.t) (simple' : Simple.t)
      (s' : ocaml_state) :
    run (S.simplify_simple0 dacc simple mode) n s
      = Returned (ty, simple') s' ->
    run (S.simplify_simple_if_in_scope dacc simple mode) n s
      = Returned (Some ty) s'.
  Proof.
    intro Hbody. unfold S.simplify_simple_if_in_scope.
    rewrite run_match_exn, Hbody. reflexivity.
  Qed.

  (* The three together, as ONE statement in the form of the kit: if
     [simplify_simple0] raises nothing but [Simple_not_in_scope] and a fatal
     error, then [simplify_simple_if_in_scope] raises nothing but a fatal
     error. THIS uses the name of the declared exception. *)
  Lemma if_in_scope_spec (Q : T.t -> ocaml_state -> Prop) :
    wp (S.simplify_simple0 dacc simple mode)
      (fun res s' => Q (fst res) s')
      (fun x s' => x = exn_make S.Simple_not_in_scope tt \/ x = fatal_exn)
      n s ->
    wp (S.simplify_simple_if_in_scope dacc simple mode)
      (fun res s' => match res with None => True | Some ty => Q ty s' end)
      fatal_only n s.
  Proof.
    intro Hbody. unfold S.simplify_simple_if_in_scope.
    apply wp_match_exn. eapply wp_weaken; [exact Hbody | | ].
    - intros [ty simple'] s' HQ. exact HQ.
    - intros x s' [-> | ->]; unfold handled.
      + rewrite exn_match_make. exact I.
      + rewrite (fatal_passes Simple_not_in_scope_named) by reflexivity.
        reflexivity.
  Qed.

  (* ---- [simplify_simple]: the handler ends in a fatal error. ---- *)

  (* If the whole returns, the body returned that value: the handler's
     branch is a fatal error, which never returns. Nothing is assumed. *)
  Lemma simplify_simple_returns (res : T.t * Simple.t) (s' : ocaml_state) :
    run (S.simplify_simple dacc simple mode) n s = Returned res s' ->
    run (S.simplify_simple0 dacc simple mode) n s = Returned res s'.
  Proof.
    unfold S.simplify_simple. rewrite run_match_exn.
    destruct (run (S.simplify_simple0 dacc simple mode) n s)
      as [res0 s0 | x s0 | ]; [intro H; exact H | | discriminate].
    destruct (exn_match S.Simple_not_in_scope x); [ | discriminate].
    intro H. exfalso. revert H. unfold fatal_errorf6.
    apply fatal_errorf_args_never_returns.
  Qed.

End Handlers.
