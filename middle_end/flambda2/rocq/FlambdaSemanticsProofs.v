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

(* Lemmas about the execution of FlambdaSemanticsSpec.v: bounded runs, the
   uniqueness of behaviours, and the ways of showing two states equivalent
   or one a refinement of the other. Nothing here needs review. *)

From Stdlib Require Import ZArith List Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec.
Import ListNotations.

(* ======================================================================== *)
(* Bounded runs                                                             *)
(* ======================================================================== *)

(* A run of [n + m] steps is a run of [n] steps and, if that has not ended,
   one of [m] steps from the state reached. *)
Lemma run_add (n m : nat) (s : state) :
  run (n + m) s
  = match run n s with
    | Step s' => run m s'
    | result => result
    end.
Proof.
  revert s. induction n as [ | n IH]; intros s; simpl; [ reflexivity | ].
  destruct (step s); [ apply IH | reflexivity | reflexivity ].
Qed.

(* ======================================================================== *)
(* Behaviours                                                               *)
(* ======================================================================== *)

(* What a run that has ended came to, as a behaviour. *)
Definition ended (result : step_result) (b : behaviour) : Prop :=
  match result, b with
  | Exit k vs, Exits k' vs' => k = k' ∧ vs = vs'
  | Undefined, Goes_wrong => True
  | _, _ => False
  end.

(* A terminating behaviour is a run that has ended with it. *)
Lemma behaves_ended (s : state) (b : behaviour) :
  b <> Diverges -> behaves s b -> ∃ n : nat, ended (run n s) b.
Proof.
  destruct b as [k vs | | ]; simpl; intros Hb; [ | | congruence ];
    intros [n Hrun]; exists n; rewrite Hrun; simpl; auto.
Qed.

(* More fuel does not change how a run ended. *)
Lemma ended_stable (n m : nat) (s : state) (b : behaviour) :
  ended (run n s) b -> run (n + m) s = run n s.
Proof.
  intros Hended. rewrite run_add.
  destruct (run n s); [ destruct b; contradiction | | ]; reflexivity.
Qed.

(* A run that has ended did so in one way. *)
Lemma ended_unique (result : step_result) (b b' : behaviour) :
  ended result b -> ended result b' -> b = b'.
Proof.
  destruct result, b, b'; simpl; try contradiction; try reflexivity.
  intros [<- <-] [<- <-]. reflexivity.
Qed.

(* A state that diverges has no run that ends. *)
Lemma diverges_not_ended (n : nat) (s : state) (b : behaviour) :
  behaves s Diverges -> ended (run n s) b -> False.
Proof.
  intros Hdiv Hended. destruct (Hdiv n) as [s' Hrun].
  rewrite Hrun in Hended. destruct b; contradiction.
Qed.

(* Two runs of one state that have both ended have ended alike: give both
   the fuel of the two together. *)
Theorem behaviour_unique : behaviour_unique_statement.
Proof.
  intros s b b' Hb Hb'.
  assert (Hdec : ∀ c : behaviour, c = Diverges ∨ c <> Diverges)
    by (intros [ | | ]; [ right | right | left ]; congruence).
  destruct (Hdec b) as [-> | Hterm], (Hdec b') as [-> | Hterm'].
  - reflexivity.
  - destruct (behaves_ended s b' Hterm' Hb') as [n Hended].
    destruct (diverges_not_ended n s b' Hb Hended).
  - destruct (behaves_ended s b Hterm Hb) as [n Hended].
    destruct (diverges_not_ended n s b Hb' Hended).
  - destruct (behaves_ended s b Hterm Hb) as [n Hended].
    destruct (behaves_ended s b' Hterm' Hb') as [m Hended'].
    rewrite <- (ended_stable n m s b Hended) in Hended.
    rewrite <- (ended_stable m n s b' Hended'), Nat.add_comm in Hended'.
    exact (ended_unique _ _ _ Hended Hended').
Qed.

(* The behaviours of what a step or a run comes to. *)
Definition result_behaves (result : step_result) (b : behaviour) : Prop :=
  match result with
  | Step s => behaves s b
  | Exit k vs => b = Exits k vs
  | Undefined => b = Goes_wrong
  end.

(* The behaviours of a state are those of what its first step comes to. *)
Lemma step_behaves (s : state) (b : behaviour) :
  behaves s b <-> result_behaves (step s) b.
Proof.
  destruct b as [k vs | | ]; simpl; split.
  - intros [[ | n] Hrun]; [ discriminate | ]. simpl in Hrun.
    destruct (step s); simpl; [ eauto | congruence | discriminate ].
  - destruct (step s) eqn:Hstep; simpl.
    + intros [n Hrun]. exists (S n). simpl. rewrite Hstep. exact Hrun.
    + intros [= <- <-]. exists 1. simpl. rewrite Hstep. reflexivity.
    + discriminate.
  - intros [[ | n] Hrun]; [ discriminate | ]. simpl in Hrun.
    destruct (step s); simpl; [ eauto | discriminate | reflexivity ].
  - destruct (step s) eqn:Hstep; simpl.
    + intros [n Hrun]. exists (S n). simpl. rewrite Hstep. exact Hrun.
    + discriminate.
    + intros _. exists 1. simpl. rewrite Hstep. reflexivity.
  - intros Hdiv. destruct (step s) eqn:Hstep; simpl.
    + intros n. specialize (Hdiv (S n)). simpl in Hdiv.
      rewrite Hstep in Hdiv. exact Hdiv.
    + destruct (Hdiv 1) as [s' Hrun]. simpl in Hrun.
      rewrite Hstep in Hrun. discriminate.
    + destruct (Hdiv 1) as [s' Hrun]. simpl in Hrun.
      rewrite Hstep in Hrun. discriminate.
  - destruct (step s) eqn:Hstep; simpl; [ | discriminate | discriminate ].
    intros Hdiv [ | n]; simpl; [ eauto | ]. rewrite Hstep. apply Hdiv.
Qed.

(* The same for a run of any length. *)
Lemma run_behaves (n : nat) (s : state) (b : behaviour) :
  behaves s b <-> result_behaves (run n s) b.
Proof.
  revert s. induction n as [ | n IH]; intros s; [ reflexivity | ].
  rewrite step_behaves. simpl.
  destruct (step s); simpl; [ apply IH | reflexivity | reflexivity ].
Qed.

(* ======================================================================== *)
(* Equivalence and refinement                                               *)
(* ======================================================================== *)

Lemma equivalent_refl (s : state) : equivalent s s.
Proof. intros b. reflexivity. Qed.

Lemma equivalent_sym (s s' : state) : equivalent s s' -> equivalent s' s.
Proof. intros Hequiv b. symmetry. apply Hequiv. Qed.

Lemma equivalent_trans (s s' s'' : state) :
  equivalent s s' -> equivalent s' s'' -> equivalent s s''.
Proof. intros H H' b. rewrite (H b). apply H'. Qed.

(* Two states whose runs, of whatever lengths, come to the same thing are
   equivalent. This is how the rewrites of FlambdaControlFlowProofs.v are
   proved: run both sides until they meet. *)
Lemma equivalent_of_run (n m : nat) (s s' : state) :
  run n s = run m s' -> equivalent s s'.
Proof.
  intros Hrun b. rewrite (run_behaves n s), (run_behaves m s'), Hrun.
  reflexivity.
Qed.

Theorem step_equivalent : step_equivalent_statement.
Proof.
  intros s s' Hstep. apply (equivalent_of_run 1 0). simpl.
  rewrite Hstep. reflexivity.
Qed.

Lemma equivalent_refines (s s' : state) : equivalent s s' -> refines s s'.
Proof. intros Hequiv b Hb. left. apply Hequiv. exact Hb. Qed.

Lemma refines_refl (s : state) : refines s s.
Proof. apply equivalent_refines, equivalent_refl. Qed.

Lemma refines_trans (s s' s'' : state) :
  refines s s' -> refines s' s'' -> refines s s''.
Proof.
  intros H H' b Hb.
  destruct (H' b Hb) as [Hb' | Hwrong]; [ exact (H b Hb') | ].
  destruct (H Goes_wrong Hwrong) as [Hwrong' | Hwrong']; right; exact Hwrong'.
Qed.

(* Anything refines a state that goes wrong. *)
Lemma goes_wrong_refines (s s' : state) : behaves s Goes_wrong -> refines s s'.
Proof. intros Hwrong b _. right. exact Hwrong. Qed.

Lemma expr_equivalent_refines (e e' : expr) :
  expr_equivalent e e' -> expr_refines e e'.
Proof. intros Hequiv vars conts. apply equivalent_refines, Hequiv. Qed.

(* ======================================================================== *)
(* Environments                                                             *)
(* ======================================================================== *)

(* An arm found is one of the arms. *)
Lemma find_arm_in (i : Z) (arms : list (Z * apply_cont)) (ac : apply_cont) :
  find_arm i arms = Some ac -> (i, ac) ∈ arms.
Proof.
  induction arms as [ | [discriminant ac'] arms IH]; simpl; [ discriminate | ].
  destruct (Z.eqb_spec i discriminant) as [-> | _].
  - intros [= ->]. left. reflexivity.
  - intros Hfind. right. apply IH, Hfind.
Qed.

(* Looking up a handler of a recursive [Let_cont] among the closures made of
   its handlers finds the closure of that handler. [all] is the whole list
   of handlers, kept apart from the ones still to be looked through. *)
Lemma lookup_rec_closures (k : continuation) (h : continuation_handler)
    (handlers all : list (continuation * continuation_handler)) (vars : env)
    (conts rest : cont_env) :
  lookup k handlers = Some h ->
  lookup k (map (fun '(k, h) => (k, Closure h vars conts all)) handlers ++ rest)
  = Some (Closure h vars conts all).
Proof.
  induction handlers as [ | [k' h'] handlers IH]; simpl; [ discriminate | ].
  destruct (Pos.eqb k k'); [ | exact IH ].
  intros [= ->]. reflexivity.
Qed.
