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

(* A run that has ended with a behaviour gives that behaviour. *)
Lemma ended_behaves (n : nat) (s : state) (b : behaviour) :
  ended (run n s) b -> behaves s b.
Proof.
  destruct b as [k vs | | ], (run n s) as [s' | k' vs' | ] eqn:Hrun; simpl;
    try contradiction.
  - intros [-> ->]. exists n. exact Hrun.
  - intros _. exists n. exact Hrun.
Qed.

Lemma ended_undefined (b : behaviour) : ended Undefined b -> b = Goes_wrong.
Proof. destruct b; simpl; try contradiction. reflexivity. Qed.

Lemma ended_exit (k : continuation) (vs : list value) (b : behaviour) :
  ended (Exit k vs) b -> b = Exits k vs.
Proof.
  destruct b; simpl; try contradiction. intros [-> ->]. reflexivity.
Qed.

Lemma diverges_dec (b : behaviour) : b = Diverges ∨ b <> Diverges.
Proof. destruct b; [ right | right | left ]; congruence. Qed.

(* If [s] has every behaviour of [s'] that ends, and [s] diverges, then
   [s'] diverges: a run of [s'] that had ended would be one of [s]. *)
Lemma diverges_of_terminating (s s' : state) :
  (∀ b : behaviour, b <> Diverges -> behaves s' b -> behaves s b) ->
  behaves s Diverges -> behaves s' Diverges.
Proof.
  intros Hterm Hdiv. simpl. intros n.
  destruct (run n s') as [u | k vs | ] eqn:Hrun; [ exists u; reflexivity | | ];
    exfalso.
  - assert (Hexit : behaves s' (Exits k vs)) by (exists n; exact Hrun).
    apply Hterm in Hexit; [ | discriminate ].
    pose proof (behaviour_unique _ _ _ Hdiv Hexit). discriminate.
  - assert (Hwrong : behaves s' Goes_wrong) by (exists n; exact Hrun).
    apply Hterm in Hwrong; [ | discriminate ].
    pose proof (behaviour_unique _ _ _ Hdiv Hwrong). discriminate.
Qed.

(* Two states with the same behaviours that end are equivalent: divergence
   need not be considered. *)
Lemma equivalent_of_terminating (s s' : state) :
  (∀ b : behaviour, b <> Diverges -> behaves s b <-> behaves s' b) ->
  equivalent s s'.
Proof.
  intros Hterm b.
  destruct (diverges_dec b) as [-> | Hb]; [ | exact (Hterm b Hb) ].
  split; apply diverges_of_terminating; intros b Hb Hbehaves;
    apply (Hterm b Hb); exact Hbehaves.
Qed.

Lemma equivalent_refines (s s' : state) : equivalent s s' -> refines s s'.
Proof.
  intros Hequiv. split.
  - intros k vs Hb. apply Hequiv, Hb.
  - intros b _ Hb. left. apply Hequiv, Hb.
Qed.

Lemma refines_refl (s : state) : refines s s.
Proof. apply equivalent_refines, equivalent_refl. Qed.

Lemma refines_trans (s s' s'' : state) :
  refines s s' -> refines s' s'' -> refines s s''.
Proof.
  intros [Hexits Hends] [Hexits' Hends']. split.
  - intros k vs Hb. apply Hexits', Hexits, Hb.
  - intros b Hterm Hb.
    destruct (Hends' b Hterm Hb) as [Hb' | Hwrong];
      [ exact (Hends b Hterm Hb') | ].
    destruct (Hends Goes_wrong ltac:(discriminate) Hwrong); right; assumption.
Qed.

(* Anything refines a state that goes wrong. *)
Lemma goes_wrong_refines (s s' : state) : behaves s Goes_wrong -> refines s s'.
Proof.
  intros Hwrong. split.
  - intros k vs Hb. pose proof (behaviour_unique _ _ _ Hwrong Hb).
    discriminate.
  - intros b _ _. right. exact Hwrong.
Qed.

Theorem refines_defined : refines_defined_statement.
Proof.
  intros s s' [Hexits Hends] Hdefined. apply equivalent_of_terminating.
  intros b Hterm. split; intros Hb.
  - destruct b; [ apply Hexits, Hb | contradiction | congruence ].
  - destruct (Hends b Hterm Hb); [ assumption | contradiction ].
Qed.

Theorem refines_antisymmetric : refines_antisymmetric_statement.
Proof.
  intros s s' [Hexits Hends] [Hexits' Hends']. apply equivalent_of_terminating.
  intros b Hterm. split; intros Hb.
  - destruct b; [ apply Hexits, Hb | | congruence ].
    destruct (Hends' Goes_wrong Hterm Hb); assumption.
  - destruct b; [ apply Hexits', Hb | | congruence ].
    destruct (Hends Goes_wrong Hterm Hb); assumption.
Qed.

(* Refinement is preserved backwards along steps. *)
Lemma refines_step (s s' t t' : state) :
  step s = Step s' -> step t = Step t' -> refines s' t' -> refines s t.
Proof.
  intros Hs Ht Hrefines.
  apply (refines_trans s s');
    [ apply equivalent_refines, step_equivalent, Hs | ].
  apply (refines_trans s' t'); [ exact Hrefines | ].
  apply equivalent_refines, equivalent_sym, step_equivalent, Ht.
Qed.

Lemma expr_equivalent_refines (e e' : expr) :
  expr_equivalent e e' -> expr_refines e e'.
Proof. intros Hequiv vars conts statics. apply equivalent_refines, Hequiv. Qed.

(* ======================================================================== *)
(* Bisimulations                                                            *)
(* ======================================================================== *)

(* What two steps, or two runs of one length, come to, alike up to [R]:
   states related by [R], the same exit, or both undefined. *)
Definition result_related (R : state -> state -> Prop)
    (result result' : step_result) : Prop :=
  match result, result' with
  | Step s, Step s' => R s s'
  | Exit k vs, Exit k' vs' => k = k' ∧ vs = vs'
  | Undefined, Undefined => True
  | _, _ => False
  end.

Lemma result_related_refl (R : state -> state -> Prop)
    (result : step_result) :
  (∀ s : state, R s s) -> result_related R result result.
Proof. intros Hrefl. destruct result; simpl; auto. Qed.

Section Bisimulation.

Variable R : state -> state -> Prop.

Hypothesis R_step :
  ∀ s s' : state, R s s' -> result_related R (step s) (step s').

Lemma bisimulation_run (n : nat) :
  ∀ s s' : state, R s s' -> result_related R (run n s) (run n s').
Proof.
  induction n as [ | n IH]; intros s s' Hrel; simpl; [ exact Hrel | ].
  specialize (R_step s s' Hrel).
  destruct (step s), (step s'); simpl in R_step; try contradiction;
    [ apply IH; exact R_step | exact R_step | exact I ].
Qed.

(* States related by a relation that steps preserve, in step with each
   other, are equivalent. *)
Lemma bisimulation_equivalent (s s' : state) : R s s' -> equivalent s s'.
Proof.
  intros Hrel b.
  pose proof (fun n => bisimulation_run n s s' Hrel) as Hrun.
  destruct b as [k vs | | ]; simpl; split.
  - intros [n Hn]. exists n. specialize (Hrun n). rewrite Hn in Hrun.
    destruct (run n s'); simpl in Hrun; try contradiction.
    destruct Hrun as [-> ->]. reflexivity.
  - intros [n Hn]. exists n. specialize (Hrun n). rewrite Hn in Hrun.
    destruct (run n s); simpl in Hrun; try contradiction.
    destruct Hrun as [-> ->]. reflexivity.
  - intros [n Hn]. exists n. specialize (Hrun n). rewrite Hn in Hrun.
    destruct (run n s'); simpl in Hrun; try contradiction. reflexivity.
  - intros [n Hn]. exists n. specialize (Hrun n). rewrite Hn in Hrun.
    destruct (run n s); simpl in Hrun; try contradiction. reflexivity.
  - intros Hdiv n. destruct (Hdiv n) as [t Ht]. specialize (Hrun n).
    rewrite Ht in Hrun.
    destruct (run n s') as [t' | | ]; simpl in Hrun; try contradiction.
    exists t'. reflexivity.
  - intros Hdiv n. destruct (Hdiv n) as [t Ht]. specialize (Hrun n).
    rewrite Ht in Hrun.
    destruct (run n s) as [t' | | ]; simpl in Hrun; try contradiction.
    exists t'. reflexivity.
Qed.

End Bisimulation.

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

(* Looking up any continuation among the closures of a recursive
   [Let_cont], with other bindings after them. *)
Lemma lookup_rec_closures_aux (k : continuation)
    (handlers all : list (continuation * continuation_handler)) (vars : env)
    (conts rest : cont_env) :
  lookup k (map (fun '(k, h) => (k, Closure h vars conts all)) handlers ++ rest)
  = match lookup k handlers with
    | Some h => Some (Closure h vars conts all)
    | None => lookup k rest
    end.
Proof.
  induction handlers as [ | [k' h'] handlers IH]; simpl; [ reflexivity | ].
  destruct (Pos.eqb k k'); [ reflexivity | exact IH ].
Qed.

Lemma lookup_rec_closures_app (k : continuation)
    (handlers : list (continuation * continuation_handler)) (vars : env)
    (conts rest : cont_env) :
  lookup k (rec_closures handlers vars conts ++ rest)
  = match lookup k handlers with
    | Some h => Some (Closure h vars conts handlers)
    | None => lookup k rest
    end.
Proof. apply lookup_rec_closures_aux. Qed.

(* A call is undefined, or runs a body under variables that depend on the
   callee, the arguments and the static environment only, with the code's
   two continuations bound to what the caller gave. *)
Lemma call_function_cases (callee : value) (kind : call_kind)
    (vs : list value) (statics : static_env) :
  (∀ return_to exn_to : cont_value,
    call_function callee kind vs return_to exn_to statics = Undefined)
  ∨ (∃ (body : expr) (callee_vars : env) (ret exn : continuation),
      ∀ return_to exn_to : cont_value,
        call_function callee kind vs return_to exn_to statics
        = Step
            (State body callee_vars [(ret, return_to); (exn, exn_to)]
               statics)).
Proof.
  unfold call_function.
  destruct (closure_of statics callee) as [[called slots] | ];
    [ | left; reflexivity ].
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | left; reflexivity ].
  destruct (lookup called (static_code statics)) as [c | ];
    [ | left; reflexivity ].
  destruct (bind_params (code_params c) vs [(code_my_closure c, callee)])
    as [callee_vars | ]; [ | left; reflexivity ].
  right. eauto.
Qed.

(* Every parameter bound, and every variable bound before, is bound. *)
Lemma bind_params_bound (params : list variable) :
  ∀ (vs : list value) (vars handler_vars : env) (x : variable),
    bind_params params vs vars = Some handler_vars ->
    x ∈ params ∨ (∃ v : value, lookup x vars = Some v) ->
    ∃ v : value, lookup x handler_vars = Some v.
Proof.
  induction params as [ | param params IH];
    intros [ | v vs] vars handler_vars x; simpl; try discriminate.
  - intros [= <-] [[] | Hbound]. exact Hbound.
  - intros Hbind Hx. apply (IH vs _ _ x Hbind). simpl.
    destruct (Pos.eqb_spec x param) as [-> | Hne]; [ right; eauto | ].
    destruct Hx as [[Heq | Hin] | Hbound];
      [ congruence | left; exact Hin | right; exact Hbound ].
Qed.

(* Binding parameters under more variables binds them the same way. *)
Lemma bind_params_app (params : list variable) :
  ∀ (vs : list value) (vars bound rest : env),
    bind_params params vs vars = Some bound ->
    bind_params params vs (vars ++ rest) = Some (bound ++ rest).
Proof.
  induction params as [ | param params IH]; intros [ | v vs] vars bound rest;
    simpl; try discriminate.
  - intros [= <-]. reflexivity.
  - intros Hbind. exact (IH vs ((param, v) :: vars) bound rest Hbind).
Qed.
