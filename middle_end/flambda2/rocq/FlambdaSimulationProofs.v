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

(* Simulations in which one step of the first state is answered by one or
   more steps of the second. Nothing here needs review: it is a way of
   proving [refines], beside FlambdaSemanticsProofs.simulation_refines,
   which asks that the two states step together.

   It serves where a rewrite makes one step into several: a [Let] made
   a [Let_static] followed by a [Let] (FlambdaLiftProofs.v), a call that
   then binds a variable. The second run never takes fewer steps than the
   first, which is what lets a run of the second that has ended bound the
   first ([stuttering_ends]); so no measure is needed, and divergence
   never has to be considered. What is asked of the values at an exit is
   a parameter ([Q]): equality gives [refines] ([stuttering_refines]),
   and a weaker relation gives the exit of the first run in the second
   up to it ([stuttering_exit]). *)

From Stdlib Require Import ZArith List Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs.
Import ListNotations.

(* ======================================================================== *)
(* Simulations in which one step is answered by one or more                 *)
(* ======================================================================== *)

Section Stuttering.

Variable R : state -> state -> Prop.

(* What is asked of the values at an exit, given the state that the
   second run exits from. *)
Variable Q : state -> list value -> list value -> Prop.

(* What a step of the first state comes to is answered by the second
   state: nothing is asked if it is undefined; an exit is answered by an
   exit through the same continuation; a step, by one or more steps to a
   related state. *)
Definition answered (result : step_result) (s' : state) : Prop :=
  match result with
  | Undefined => True
  | Exit k vs => ∃ vs' : list value, step s' = Exit k vs' ∧ Q s' vs vs'
  | Step t => ∃ (n : nat) (t' : state), run (S n) s' = Step t' ∧ R t t'
  end.

Hypothesis R_step : ∀ s s' : state, R s s' -> answered (step s) s'.

(* An exit of the first run is one of the second. *)
Lemma stuttering_exit (n : nat) :
  ∀ (s s' : state) (k : continuation) (vs : list value),
    R s s' ->
    run n s = Exit k vs ->
    ∃ (m : nat) (last : state) (vs' : list value),
      run m s' = Step last ∧ step last = Exit k vs' ∧ Q last vs vs'.
Proof.
  induction n as [ | n IH]; intros s s' k vs Hrel; simpl; [ discriminate | ].
  pose proof (R_step s s' Hrel) as Hanswer.
  destruct (step s) as [t | k' vs0 | ]; unfold answered in Hanswer.
  - destruct Hanswer as (j & t' & Hrun & Hrel'). intros Hexit.
    destruct (IH t t' k vs Hrel' Hexit) as (m & last & vs' & Hm & Hlast & HQ).
    exists (S j + m), last, vs'. rewrite run_add, Hrun. auto.
  - intros [= <- <-]. destruct Hanswer as (vs' & Hstep & HQ).
    exists 0, s', vs'. auto.
  - discriminate.
Qed.

(* If the second run has ended, so has the first: each of its steps
   uses up at least one of the second's. *)
Lemma stuttering_ends (m : nat) :
  ∀ (s s' : state) (b : behaviour),
    R s s' ->
    ended (run m s') b ->
    ∃ n : nat,
      run n s = Undefined
      ∨ ∃ (k : continuation) (vs : list value), run n s = Exit k vs.
Proof.
  induction m as [m IH] using (well_founded_induction lt_wf).
  intros s s' b Hrel Hended.
  pose proof (R_step s s' Hrel) as Hanswer.
  destruct (step s) as [t | k vs | ] eqn:Hstep; unfold answered in Hanswer.
  - destruct Hanswer as (j & t' & Hrun & Hrel').
    destruct (Nat.lt_ge_cases m (S j)) as [Hshort | Hlong].
    + exfalso. replace (S j) with (m + (S j - m)) in Hrun by lia.
      rewrite (ended_stable m _ s' b Hended) in Hrun.
      rewrite Hrun in Hended. destruct b; contradiction.
    + replace m with (S j + (m - S j)) in Hended by lia.
      rewrite run_add, Hrun in Hended.
      assert (Hless : m - S j < m) by lia.
      destruct (IH (m - S j) Hless t t' b Hrel' Hended) as [n Hn].
      exists (S n). simpl. rewrite Hstep. exact Hn.
  - exists 1. right. exists k, vs. simpl. rewrite Hstep. reflexivity.
  - exists 1. left. simpl. rewrite Hstep. reflexivity.
Qed.

(* Where the values at an exit are the same, the second state refines the
   first. *)
Lemma stuttering_refines (s s' : state) :
  (∀ (last : state) (vs vs' : list value), Q last vs vs' -> vs' = vs) ->
  R s s' ->
  refines s s'.
Proof.
  intros Hsame Hrel.
  assert (Hexits :
    ∀ (k : continuation) (vs : list value),
      behaves s (Exits k vs) -> behaves s' (Exits k vs)).
  { intros k vs [n Hn].
    destruct (stuttering_exit n s s' k vs Hrel Hn)
      as (m & last & vs' & Hm & Hlast & HQ).
    rewrite (Hsame last vs vs' HQ) in Hlast.
    exists (m + 1). rewrite run_add, Hm. simpl. rewrite Hlast. reflexivity. }
  split; [ exact Hexits | ].
  intros b Hterm Hb. destruct (behaves_ended s' b Hterm Hb) as [m Hended].
  destruct (stuttering_ends m s s' b Hrel Hended)
    as [n [Hwrong | (k & vs & Hexit)]].
  - right. exists n. exact Hwrong.
  - left. assert (Hs : behaves s (Exits k vs)) by (exists n; exact Hexit).
    rewrite (behaviour_unique s' b (Exits k vs) Hb (Hexits k vs Hs)).
    exact Hs.
Qed.

End Stuttering.
