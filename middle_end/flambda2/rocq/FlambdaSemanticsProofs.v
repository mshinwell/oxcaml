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

(* Lemmas about the execution of FlambdaSemanticsSpec.v: what a state of
   each construct steps to (the step lemmas, through which every other
   proof reasons about [step]), bounded runs, the uniqueness of
   behaviours, and the ways of showing two states equivalent or one a
   refinement of the other. Nothing here needs review. *)

From Stdlib Require Import ZArith List Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
Import ListNotations.

(* ======================================================================== *)
(* States                                                                   *)
(* ======================================================================== *)

(* A state is its components. A proof about any state [s] rewrites with
   this and goes by cases on [state_expr s]; it does not destruct [s],
   which would name the components by their position. *)
Lemma state_eta (s : state) :
  s = State (state_expr s) (state_vars s) (state_conts s) (state_statics s).
Proof. destruct s. reflexivity. Qed.

(* Reduces the projections of states that are given by their components,
   and nothing else. *)
Ltac simpl_state :=
  cbn [state_expr state_vars state_conts state_statics] in *.

(* ======================================================================== *)
(* Steps                                                                    *)
(* ======================================================================== *)

(* What a state steps to, for each construct: one lemma for each case of
   [step], saying what the state comes to and under which conditions.

   These are how every proof reasons about a step. [step] is made opaque
   below, so [simpl] and [unfold] leave it alone: a proof rewrites with
   the lemma of the construct at hand and goes by cases on the conditions
   it names. A change to [step] is then a change to these lemmas, and to
   the proofs that use the lemma of the case that changed. *)

Lemma step_let (x : variable) (defining_expr : named) (body : expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  step (State (Let x defining_expr body) vars conts statics)
  = match eval_named statics vars defining_expr with
    | Some v => Step (State body ((x, v) :: vars) conts statics)
    | None => Undefined
    end.
Proof. reflexivity. Qed.

Lemma step_let_static (bindings : list static_binding) (body : expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  step (State (Let_static bindings body) vars conts statics)
  = match eval_static_bindings vars bindings statics with
    | Some statics' => Step (State body vars conts statics')
    | None => Undefined
    end.
Proof. reflexivity. Qed.

Lemma step_let_cont_non_recursive (k : continuation)
    (h : continuation_handler) (body : expr) (vars : env) (conts : cont_env)
    (statics : static_env) :
  step (State (Let_cont_non_recursive k h body) vars conts statics)
  = Step (State body vars ((k, Closure h vars conts []) :: conts) statics).
Proof. reflexivity. Qed.

Lemma step_let_cont_recursive
    (handlers : list (continuation * continuation_handler)) (body : expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  step (State (Let_cont_recursive handlers body) vars conts statics)
  = if handlers_bind_statics handlers then Undefined
    else
      Step
        (State body vars (rec_closures handlers vars conts ++ conts) statics).
Proof. reflexivity. Qed.

Lemma step_apply (ap : apply_expr) (vars : env) (conts : cont_env)
    (statics : static_env) :
  step (State (Apply ap) vars conts statics)
  = match eval_simple vars (ap_callee ap), eval_simples vars (ap_args ap) with
    | Some callee, Some vs =>
      call_function callee (ap_call_kind ap) vs
        (resolve (ap_continuation ap) conts)
        (resolve (ap_exn_continuation ap) conts) statics
    | _, _ => Undefined
    end.
Proof. reflexivity. Qed.

Lemma step_apply_cont (ac : apply_cont) (vars : env) (conts : cont_env)
    (statics : static_env) :
  step (State (Apply_cont ac) vars conts statics)
  = match eval_simples vars (ac_args ac) with
    | Some vs => apply_continuation (ac_continuation ac) vs conts statics
    | None => Undefined
    end.
Proof. reflexivity. Qed.

Lemma step_switch (scrutinee : simple) (arms : list (Z * apply_cont))
    (vars : env) (conts : cont_env) (statics : static_env) :
  step (State (Switch scrutinee arms) vars conts statics)
  = match eval_simple vars scrutinee with
    | Some v =>
      match naked_immediate_of_value v with
      | Some i =>
        match find_arm i arms with
        | Some ac => Step (State (Apply_cont ac) vars conts statics)
        | None => Undefined
        end
      | None => Undefined
      end
    | None => Undefined
    end.
Proof. reflexivity. Qed.

Lemma step_invalid (vars : env) (conts : cont_env) (statics : static_env) :
  step (State Invalid vars conts statics) = Undefined.
Proof. reflexivity. Qed.

(* The two ways in which an [Apply_cont] does not go wrong: its
   continuation stands for a handler, which runs under the environments of
   its closure with its parameters bound; or for a way out of the term. *)
Lemma step_apply_cont_handler (ac : apply_cont) (vars : env)
    (conts : cont_env) (statics : static_env) (vs : list value)
    (params : list variable) (handler : expr) (def_vars : env)
    (def_conts : cont_env)
    (recursive : list (continuation * continuation_handler))
    (handler_vars : env) :
  eval_simples vars (ac_args ac) = Some vs ->
  resolve (ac_continuation ac) conts
  = Closure (Handler params handler) def_vars def_conts recursive ->
  bind_params params vs def_vars = Some handler_vars ->
  step (State (Apply_cont ac) vars conts statics)
  = Step
      (State handler handler_vars
         (rec_closures recursive def_vars def_conts ++ def_conts) statics).
Proof.
  intros Hargs Hresolve Hbind. rewrite step_apply_cont, Hargs.
  unfold apply_continuation. rewrite Hresolve. simpl. rewrite Hbind.
  reflexivity.
Qed.

Lemma step_apply_cont_exit (ac : apply_cont) (vars : env) (conts : cont_env)
    (statics : static_env) (vs : list value) (k : continuation) :
  eval_simples vars (ac_args ac) = Some vs ->
  resolve (ac_continuation ac) conts = Outer k ->
  step (State (Apply_cont ac) vars conts statics) = Exit k vs.
Proof.
  intros Hargs Hresolve. rewrite step_apply_cont, Hargs.
  unfold apply_continuation. rewrite Hresolve. reflexivity.
Qed.

(* A [Switch] is undefined, or steps to the arm of its scrutinee. *)
Lemma step_switch_cases (scrutinee : simple) (arms : list (Z * apply_cont))
    (vars : env) (conts : cont_env) (statics : static_env) :
  step (State (Switch scrutinee arms) vars conts statics) = Undefined
  ∨ ∃ (v : value) (i : Z) (ac : apply_cont),
      eval_simple vars scrutinee = Some v
      ∧ naked_immediate_of_value v = Some i
      ∧ find_arm i arms = Some ac
      ∧ step (State (Switch scrutinee arms) vars conts statics)
        = Step (State (Apply_cont ac) vars conts statics).
Proof.
  rewrite step_switch.
  destruct (eval_simple vars scrutinee) as [v | ]; [ | left; reflexivity ].
  destruct (naked_immediate_of_value v) as [i | ] eqn:Hi;
    [ | left; reflexivity ].
  destruct (find_arm i arms) as [ac | ] eqn:Hfind; [ | left; reflexivity ].
  right. exists v, i, ac. auto.
Qed.

#[global] Opaque step.

(* For a proof by cases on the construct of a state:
   [autorewrite with step] rewrites the step of each case. *)
Create Rewrite HintDb step.
#[global] Hint Rewrite step_let step_let_static step_let_cont_non_recursive
  step_let_cont_recursive step_apply step_apply_cont step_switch
  step_invalid : step.

(* ======================================================================== *)
(* Bounded runs                                                             *)
(* ======================================================================== *)

(* A run of one step more is the first step and, if that has not ended,
   the rest of the run. *)
Lemma run_succ (n : nat) (s : state) :
  run (S n) s
  = match step s with
    | Step s' => run n s'
    | result => result
    end.
Proof. reflexivity. Qed.

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
   equivalent. *)
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

(* Both sides take a step, to states that are equivalent. *)
Lemma equivalent_step (s s' t t' : state) :
  step s = Step s' -> step t = Step t' -> equivalent s' t' -> equivalent s t.
Proof.
  intros Hs Ht Hequiv.
  apply (equivalent_trans s s'); [ apply step_equivalent, Hs | ].
  apply (equivalent_trans s' t'); [ exact Hequiv | ].
  apply equivalent_sym, step_equivalent, Ht.
Qed.

(* Two states whose first steps come to the same thing are equivalent. *)
Lemma step_eq_equivalent (s s' : state) : step s = step s' -> equivalent s s'.
Proof.
  intros Hstep b. rewrite (step_behaves s), (step_behaves s'), Hstep.
  reflexivity.
Qed.

(* A state whose step is undefined goes wrong, so anything refines it. *)
Lemma step_undefined_wrong (s : state) :
  step s = Undefined -> behaves s Goes_wrong.
Proof.
  intros Hstep. apply (step_behaves s Goes_wrong). rewrite Hstep.
  reflexivity.
Qed.

Lemma step_undefined_refines (s s' : state) :
  step s = Undefined -> refines s s'.
Proof. intros Hstep. apply goes_wrong_refines, step_undefined_wrong, Hstep. Qed.

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

(* What a continuation stands for where it has just been bound, and where
   the closures of a recursive [Let_cont] have. *)
Lemma resolve_head (k : continuation) (c : cont_value) (conts : cont_env) :
  resolve k ((k, c) :: conts) = c.
Proof. unfold resolve. simpl. rewrite Pos.eqb_refl. reflexivity. Qed.

Lemma resolve_other (k k' : continuation) (c : cont_value)
    (conts : cont_env) :
  k <> k' -> resolve k ((k', c) :: conts) = resolve k conts.
Proof.
  intros Hne. unfold resolve. simpl.
  destruct (Pos.eqb_spec k k'); [ contradiction | reflexivity ].
Qed.

Lemma resolve_rec_closures (k : continuation)
    (handlers : list (continuation * continuation_handler)) (vars : env)
    (conts rest : cont_env) :
  resolve k (rec_closures handlers vars conts ++ rest)
  = match lookup k handlers with
    | Some h => Closure h vars conts handlers
    | None => resolve k rest
    end.
Proof.
  unfold resolve. rewrite lookup_rec_closures_app.
  destruct (lookup k handlers); reflexivity.
Qed.

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
  destruct (binds_statics (code_body c)); [ left; reflexivity | ].
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

(* ======================================================================== *)
(* Simulations                                                              *)
(* ======================================================================== *)

(* What two steps, or two runs of one length, come to, where the second
   may do anything if the first is undefined: otherwise states related by
   [R], or the same exit. *)
Definition result_simulated (R : state -> state -> Prop)
    (result result' : step_result) : Prop :=
  match result, result' with
  | Undefined, _ => True
  | Step s, Step s' => R s s'
  | Exit k vs, Exit k' vs' => k = k' ∧ vs = vs'
  | _, _ => False
  end.

Section Simulation.

Variable R : state -> state -> Prop.

Hypothesis R_step :
  ∀ s s' : state, R s s' -> result_simulated R (step s) (step s').

Lemma simulation_run (n : nat) :
  ∀ s s' : state, R s s' -> result_simulated R (run n s) (run n s').
Proof.
  induction n as [ | n IH]; intros s s' Hrel; simpl; [ exact Hrel | ].
  specialize (R_step s s' Hrel).
  destruct (step s), (step s'); simpl in R_step; try contradiction;
    try exact I; [ apply IH; exact R_step | exact R_step ].
Qed.

(* A state refines one related to it by a relation that steps preserve, in
   step with each other, as long as the first is defined. *)
Lemma simulation_refines (s s' : state) : R s s' -> refines s s'.
Proof.
  intros Hrel.
  pose proof (fun n => simulation_run n s s' Hrel) as Hrun.
  split.
  - intros k vs [n Hn]. exists n. specialize (Hrun n). rewrite Hn in Hrun.
    destruct (run n s'); simpl in Hrun; try contradiction.
    destruct Hrun as [-> ->]. reflexivity.
  - intros b Hterm Hb. destruct (behaves_ended s' b Hterm Hb) as [n Hended].
    specialize (Hrun n).
    destruct (run n s) as [t | k vs | ] eqn:Hs.
    + destruct (run n s'); simpl in Hrun; contradiction.
    + destruct (run n s') as [t' | k' vs' | ]; simpl in Hrun;
        try contradiction.
      destruct Hrun as [-> ->]. apply ended_exit in Hended. subst b.
      left. exists n. exact Hs.
    + right. exists n. exact Hs.
Qed.

End Simulation.

(* ======================================================================== *)
(* Two states at the same construct                                         *)
(* ======================================================================== *)

(* For each construct that binds, how to relate two states that are both
   at it and take the same step: both are undefined, or both step to their
   bodies, which are then to be related. A proof that goes under a binder
   uses these, and so does not depend on what the step of the binder is. *)

(* Two [Let]s whose defining expressions have the same value, or none. *)
Lemma let_equivalent_step (x x' : variable) (d d' : named)
    (body body' : expr) (vars vars' : env) (conts conts' : cont_env)
    (statics statics' : static_env) :
  eval_named statics' vars' d' = eval_named statics vars d ->
  (∀ v : value,
    eval_named statics vars d = Some v ->
    equivalent (State body ((x, v) :: vars) conts statics)
      (State body' ((x', v) :: vars') conts' statics')) ->
  equivalent (State (Let x d body) vars conts statics)
    (State (Let x' d' body') vars' conts' statics').
Proof.
  intros Hd' Hbodies.
  destruct (eval_named statics vars d) as [v | ] eqn:Hd.
  - eapply equivalent_step;
      [ rewrite step_let, Hd; reflexivity
      | rewrite step_let, Hd'; reflexivity | exact (Hbodies v eq_refl) ].
  - apply step_eq_equivalent. rewrite !step_let, Hd', Hd. reflexivity.
Qed.

Lemma let_refines_step (x x' : variable) (d d' : named) (body body' : expr)
    (vars vars' : env) (conts conts' : cont_env)
    (statics statics' : static_env) :
  eval_named statics' vars' d' = eval_named statics vars d ->
  (∀ v : value,
    eval_named statics vars d = Some v ->
    refines (State body ((x, v) :: vars) conts statics)
      (State body' ((x', v) :: vars') conts' statics')) ->
  refines (State (Let x d body) vars conts statics)
    (State (Let x' d' body') vars' conts' statics').
Proof.
  intros Hd' Hbodies.
  destruct (eval_named statics vars d) as [v | ] eqn:Hd.
  - eapply refines_step;
      [ rewrite step_let, Hd; reflexivity
      | rewrite step_let, Hd'; reflexivity | exact (Hbodies v eq_refl) ].
  - apply step_undefined_refines. rewrite step_let, Hd. reflexivity.
Qed.

(* Two [Let_static]s: both groups are bound, and the bodies are related
   under the static environments that result, or neither is. For a
   refinement the second may be anything when the first is not bound. *)
Lemma let_static_equivalent_step (bindings bindings' : list static_binding)
    (body body' : expr) (vars vars' : env) (conts conts' : cont_env)
    (statics statics' : static_env) :
  match
    eval_static_bindings vars bindings statics,
    eval_static_bindings vars' bindings' statics'
  with
  | Some extended, Some extended' =>
    equivalent (State body vars conts extended)
      (State body' vars' conts' extended')
  | None, None => True
  | _, _ => False
  end ->
  equivalent (State (Let_static bindings body) vars conts statics)
    (State (Let_static bindings' body') vars' conts' statics').
Proof.
  intros Hbodies.
  destruct (eval_static_bindings vars bindings statics) as [extended | ]
    eqn:Hbindings,
    (eval_static_bindings vars' bindings' statics') as [extended' | ]
      eqn:Hbindings';
    try contradiction.
  - eapply equivalent_step;
      [ rewrite step_let_static, Hbindings; reflexivity
      | rewrite step_let_static, Hbindings'; reflexivity | exact Hbodies ].
  - apply step_eq_equivalent.
    rewrite !step_let_static, Hbindings, Hbindings'. reflexivity.
Qed.

Lemma let_static_refines_step (bindings bindings' : list static_binding)
    (body body' : expr) (vars vars' : env) (conts conts' : cont_env)
    (statics statics' : static_env) :
  match
    eval_static_bindings vars bindings statics,
    eval_static_bindings vars' bindings' statics'
  with
  | Some extended, Some extended' =>
    refines (State body vars conts extended)
      (State body' vars' conts' extended')
  | Some _, None => False
  | None, _ => True
  end ->
  refines (State (Let_static bindings body) vars conts statics)
    (State (Let_static bindings' body') vars' conts' statics').
Proof.
  intros Hbodies.
  destruct (eval_static_bindings vars bindings statics) as [extended | ]
    eqn:Hbindings;
    [ | apply step_undefined_refines; rewrite step_let_static, Hbindings;
        reflexivity ].
  destruct (eval_static_bindings vars' bindings' statics')
    as [extended' | ] eqn:Hbindings'; [ | contradiction ].
  eapply refines_step;
    [ rewrite step_let_static, Hbindings; reflexivity
    | rewrite step_let_static, Hbindings'; reflexivity | exact Hbodies ].
Qed.

(* Two [Let_cont_non_recursive]s always step to their bodies. *)
Lemma let_cont_non_recursive_equivalent_step (k k' : continuation)
    (h h' : continuation_handler) (body body' : expr) (vars vars' : env)
    (conts conts' : cont_env) (statics statics' : static_env) :
  equivalent
    (State body vars ((k, Closure h vars conts []) :: conts) statics)
    (State body' vars' ((k', Closure h' vars' conts' []) :: conts')
       statics') ->
  equivalent (State (Let_cont_non_recursive k h body) vars conts statics)
    (State (Let_cont_non_recursive k' h' body') vars' conts' statics').
Proof.
  apply equivalent_step; apply step_let_cont_non_recursive.
Qed.

Lemma let_cont_non_recursive_refines_step (k k' : continuation)
    (h h' : continuation_handler) (body body' : expr) (vars vars' : env)
    (conts conts' : cont_env) (statics statics' : static_env) :
  refines (State body vars ((k, Closure h vars conts []) :: conts) statics)
    (State body' vars' ((k', Closure h' vars' conts' []) :: conts')
       statics') ->
  refines (State (Let_cont_non_recursive k h body) vars conts statics)
    (State (Let_cont_non_recursive k' h' body') vars' conts' statics').
Proof.
  apply refines_step; apply step_let_cont_non_recursive.
Qed.

(* Two [Let_cont_recursive]s that agree on whether their handlers bind
   something static: both are undefined, or both step to their bodies. *)
Lemma let_cont_recursive_equivalent_step
    (handlers handlers' : list (continuation * continuation_handler))
    (body body' : expr) (vars vars' : env) (conts conts' : cont_env)
    (statics statics' : static_env) :
  handlers_bind_statics handlers = handlers_bind_statics handlers' ->
  (handlers_bind_statics handlers = false ->
   equivalent
     (State body vars (rec_closures handlers vars conts ++ conts) statics)
     (State body' vars' (rec_closures handlers' vars' conts' ++ conts')
        statics')) ->
  equivalent (State (Let_cont_recursive handlers body) vars conts statics)
    (State (Let_cont_recursive handlers' body') vars' conts' statics').
Proof.
  intros Hbinds Hbodies.
  destruct (handlers_bind_statics handlers) eqn:Hsource.
  - apply step_eq_equivalent.
    rewrite !step_let_cont_recursive, <- Hbinds, Hsource. reflexivity.
  - eapply equivalent_step;
      [ rewrite step_let_cont_recursive, Hsource; reflexivity
      | rewrite step_let_cont_recursive, <- Hbinds; reflexivity
      | exact (Hbodies eq_refl) ].
Qed.

Lemma let_cont_recursive_refines_step
    (handlers handlers' : list (continuation * continuation_handler))
    (body body' : expr) (vars vars' : env) (conts conts' : cont_env)
    (statics statics' : static_env) :
  handlers_bind_statics handlers = handlers_bind_statics handlers' ->
  (handlers_bind_statics handlers = false ->
   refines
     (State body vars (rec_closures handlers vars conts ++ conts) statics)
     (State body' vars' (rec_closures handlers' vars' conts' ++ conts')
        statics')) ->
  refines (State (Let_cont_recursive handlers body) vars conts statics)
    (State (Let_cont_recursive handlers' body') vars' conts' statics').
Proof.
  intros Hbinds Hbodies.
  destruct (handlers_bind_statics handlers) eqn:Hsource.
  - apply step_undefined_refines.
    rewrite step_let_cont_recursive, Hsource. reflexivity.
  - eapply refines_step;
      [ rewrite step_let_cont_recursive, Hsource; reflexivity
      | rewrite step_let_cont_recursive, <- Hbinds; reflexivity
      | exact (Hbodies eq_refl) ].
Qed.
