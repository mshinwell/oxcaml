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

(* Proofs of the statements of FlambdaControlFlowSpec.v. Each equivalence is
   proved by running both sides until they come to the same thing
   (FlambdaSemanticsProofs.equivalent_of_run). Nothing here needs review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaControlFlowSpec.
Import ListNotations.

(* ======================================================================== *)
(* Continuations                                                            *)
(* ======================================================================== *)

(* Two steps of the left-hand side reach the right-hand side. *)
Theorem let_cont_apply_cont : let_cont_apply_cont_statement.
Proof.
  intros k params handler args vars handler_vars conts statics vs Hargs
    Hbind.
  apply (equivalent_of_run 2 0). simpl.
  rewrite Hargs. unfold apply_continuation, resolve. simpl.
  rewrite Pos.eqb_refl. simpl. rewrite Hbind. reflexivity.
Qed.

(* Both sides evaluate the argument first; if it has a value, both reach the
   handler with the parameter bound, and if not, both are undefined. *)
Theorem let_cont_apply_cont_one_param :
  let_cont_apply_cont_one_param_statement.
Proof.
  intros k x handler arg vars conts statics.
  apply (equivalent_of_run 2 1). simpl.
  destruct (eval_simple vars arg) as [v | ]; simpl; [ | reflexivity ].
  unfold apply_continuation, resolve. simpl. rewrite Pos.eqb_refl.
  reflexivity.
Qed.

Theorem let_cont_recursive_apply_cont :
  let_cont_recursive_apply_cont_statement.
Proof.
  intros k params handler handlers args vars handler_vars conts statics vs
    Hlookup Hargs Hbind.
  apply (equivalent_of_run 2 0). simpl.
  rewrite Hargs. unfold apply_continuation, resolve, rec_closures.
  rewrite (lookup_rec_closures _ _ _ _ _ _ _ Hlookup). simpl.
  rewrite Hbind.
  reflexivity.
Qed.

(* After its first step the loop is in a state that steps to itself. *)
Theorem loop_forever_diverges : loop_forever_diverges_statement.
Proof.
  intros k vars conts statics.
  apply (step_behaves _ Diverges). simpl.
  set (looping := State _ _ _ statics).
  assert (Hstep : step looping = Step looping).
  { subst looping. simpl. unfold apply_continuation, resolve. simpl.
    rewrite Pos.eqb_refl. reflexivity. }
  clearbody looping. intros n. exists looping.
  induction n as [ | n IH]; simpl; [ reflexivity | ].
  rewrite Hstep. exact IH.
Qed.

(* ======================================================================== *)
(* Switches                                                                 *)
(* ======================================================================== *)

Theorem switch_const : switch_const_statement.
Proof.
  intros i arms ac Hfind vars conts statics.
  apply step_equivalent. simpl. rewrite Hfind. reflexivity.
Qed.

(* Either the [Switch] steps to one of its arms, which is [ac], or it is
   undefined. *)
Theorem switch_same_arms : switch_same_arms_statement.
Proof.
  intros scrutinee arms ac Hsame vars conts statics.
  destruct (step (State (Switch scrutinee arms) vars conts statics)) eqn:Hstep.
  - apply equivalent_refines, step_equivalent.
    assert (Harm : s = State (Apply_cont ac) vars conts statics);
      [ | rewrite <- Harm; exact Hstep ].
    simpl in Hstep.
    destruct (eval_simple vars scrutinee) as [v | ]; [ | discriminate ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | discriminate ].
    destruct (find_arm i arms) as [arm | ] eqn:Hfind; [ | discriminate ].
    apply find_arm_in, Hsame in Hfind. congruence.
  - simpl in Hstep.
    destruct (eval_simple vars scrutinee) as [v | ]; [ | discriminate ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | discriminate ].
    destruct (find_arm i arms); discriminate.
  - apply goes_wrong_refines. exists 1. unfold run. rewrite Hstep.
    reflexivity.
Qed.
