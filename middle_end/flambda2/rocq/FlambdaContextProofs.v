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

(* Proofs of the statements of FlambdaContextSpec.v. Nothing here needs
   review.

   A hole in the body of a binder is one step away from the premise. A hole
   in a handler is not: the handler goes into a closure, which is applied
   later, any number of times. So the proof relates continuation
   environments whose closures have related handlers ([cont_env_related]),
   and shows that one expression under two related environments ends alike
   ([transfer]), by induction on the length of the run: where a closure is
   applied, the induction gives the first handler under the second
   environment, and the relation of the handlers then gives the second
   handler there. Divergence needs no argument of its own
   (FlambdaSemanticsProofs.equivalent_of_terminating). *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaContextSpec.
Import ListNotations.

(* ======================================================================== *)
(* Related continuation environments                                        *)
(* ======================================================================== *)

Section Transfer.

(* The relation between corresponding handlers, given their parameters and
   the variables of the closure they are in: a handler runs under those
   variables with its parameters bound, so the relation may depend on
   them. *)
Variable related : list variable -> env -> expr -> expr -> Prop.

Inductive handler_related (vars : env)
    : continuation_handler -> continuation_handler -> Prop :=
  | Handler_related (params : list variable) (e e' : expr) :
    related params vars e e' ->
    handler_related vars (Handler params e) (Handler params e')
  | Handler_same (h : continuation_handler) : handler_related vars h h.

Definition handlers_related (vars : env)
    (handlers handlers' : list (continuation * continuation_handler))
    : Prop :=
  Forall2
    (fun kh kh' =>
       fst kh = fst kh' ∧ handler_related vars (snd kh) (snd kh'))
    handlers handlers'.

(* Closures with related handlers and, in turn, related environments. (The
   warning silenced is about induction schemes, which nothing uses.) *)
#[local] Set Warnings "-register-all".
Inductive closure_related : cont_value -> cont_value -> Prop :=
  | Closure_related (h h' : continuation_handler) (vars : env)
      (conts conts' : cont_env)
      (recursive recursive' : list (continuation * continuation_handler)) :
    handler_related vars h h' ->
    Forall2
      (fun kc kc' => fst kc = fst kc' ∧ closure_related (snd kc) (snd kc'))
      conts conts' ->
    handlers_related vars recursive recursive' ->
    closure_related (Closure h vars conts recursive)
      (Closure h' vars conts' recursive')
  | Closure_same (c : cont_value) : closure_related c c.

Definition cont_env_related (conts conts' : cont_env) : Prop :=
  Forall2
    (fun kc kc' => fst kc = fst kc' ∧ closure_related (snd kc) (snd kc'))
    conts conts'.

Lemma cont_env_related_refl (conts : cont_env) : cont_env_related conts conts.
Proof.
  induction conts as [ | kc conts IH]; [ apply Forall2_nil | ].
  apply Forall2_cons; [ | exact IH ].
  split; [ reflexivity | apply Closure_same ].
Qed.

Lemma handlers_related_refl (vars : env)
    (handlers : list (continuation * continuation_handler)) :
  handlers_related vars handlers handlers.
Proof.
  induction handlers as [ | kh handlers IH]; [ apply Forall2_nil | ].
  apply Forall2_cons; [ | exact IH ].
  split; [ reflexivity | apply Handler_same ].
Qed.

Lemma closure_related_inv (c c' : cont_value) :
  closure_related c c' ->
  match c, c' with
  | Closure h vars conts recursive, Closure h' vars' conts' recursive' =>
    vars = vars' ∧ handler_related vars h h' ∧ cont_env_related conts conts'
    ∧ handlers_related vars recursive recursive'
  | Outer k, Outer k' => k = k'
  | _, _ => False
  end.
Proof.
  intros Hrel. inversion Hrel; subst.
  - auto.
  - destruct c' as [h vars conts recursive | k]; [ | reflexivity ].
    split; [ reflexivity | ]. split; [ apply Handler_same | ].
    split; [ apply cont_env_related_refl | apply handlers_related_refl ].
Qed.

Lemma handler_related_inv (vars : env) (params params' : list variable)
    (e e' : expr) :
  handler_related vars (Handler params e) (Handler params' e') ->
  params = params' ∧ (related params vars e e' ∨ e = e').
Proof. intros Hrel. inversion Hrel; subst; auto. Qed.

(* A continuation stands for related things under related environments. *)
Lemma resolve_related (k : continuation) (conts conts' : cont_env) :
  cont_env_related conts conts' ->
  closure_related (resolve k conts) (resolve k conts').
Proof.
  unfold resolve.
  induction 1 as [ | [k1 c] [k1' c'] conts conts' [Hk Hc] _ IH]; simpl;
    [ apply Closure_same | ].
  simpl in Hk. subst k1'. destruct (Pos.eqb k k1); [ exact Hc | exact IH ].
Qed.

(* [all] and [all'] are the whole lists of handlers, kept apart from the
   ones still to be gone through. *)
Lemma rec_closures_related_aux
    (handlers handlers' all all' : list (continuation * continuation_handler))
    (vars : env) (conts conts' : cont_env) :
  handlers_related vars handlers handlers' ->
  handlers_related vars all all' ->
  cont_env_related conts conts' ->
  cont_env_related
    (map (fun '(k, h) => (k, Closure h vars conts all)) handlers)
    (map (fun '(k, h) => (k, Closure h vars conts' all')) handlers').
Proof.
  intros Hhandlers Hall Hconts.
  induction Hhandlers as [ | [k h] [k' h'] handlers handlers' [Hk Hh] _ IH];
    simpl; [ apply Forall2_nil | ].
  apply Forall2_cons; [ | exact IH ].
  simpl in Hk, Hh. subst k'. split; [ reflexivity | ].
  apply Closure_related; assumption.
Qed.

Lemma rec_closures_related
    (handlers handlers' : list (continuation * continuation_handler))
    (vars : env) (conts conts' : cont_env) :
  handlers_related vars handlers handlers' ->
  cont_env_related conts conts' ->
  cont_env_related (rec_closures handlers vars conts)
    (rec_closures handlers' vars conts').
Proof.
  intros Hhandlers Hconts.
  apply rec_closures_related_aux; assumption.
Qed.

(* ======================================================================== *)
(* One expression under related environments                                *)
(* ======================================================================== *)

(* What is to be carried from a run under the first environment to the
   state under the second: a property of a state and a behaviour that holds
   of a state when it holds of the state it steps to, that holds of how a
   state ends at once, and that [related] carries from a handler to the
   corresponding one, under the variables of their closures with the
   parameters bound, and any continuations. *)
Variable carried : state -> behaviour -> Prop.

Hypothesis carried_step :
  ∀ (s s' : state) (b : behaviour),
    step s = Step s' -> carried s' b -> carried s b.

Hypothesis carried_exit :
  ∀ (s : state) (k : continuation) (vs : list value),
    step s = Exit k vs -> carried s (Exits k vs).

Hypothesis carried_undefined :
  ∀ s : state, step s = Undefined -> carried s Goes_wrong.

Hypothesis carried_related :
  ∀ (params : list variable) (def_vars : env) (e e' : expr)
    (vs : list value) (handler_vars : env) (conts : cont_env)
    (statics : static_env) (b : behaviour),
    related params def_vars e e' ->
    bind_params params vs def_vars = Some handler_vars ->
    carried (State e handler_vars conts statics) b ->
    carried (State e' handler_vars conts statics) b.

Lemma transfer (n : nat) :
  ∀ (e : expr) (vars : env) (conts conts' : cont_env) (statics : static_env)
    (b : behaviour),
    cont_env_related conts conts' ->
    ended (run n (State e vars conts statics)) b ->
    carried (State e vars conts' statics) b.
Proof.
  induction n as [ | n IH];
    intros e vars conts conts' statics b Hrel Hended;
    [ destruct b; contradiction | ].
  destruct e
    as [ x d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    simpl in Hended.
  - (* Let *)
    destruct (eval_named statics vars d) as [v | ] eqn:Hd; simpl in Hended.
    + apply (carried_step _ (State body ((x, v) :: vars) conts' statics));
        [ simpl; rewrite Hd; reflexivity | ].
      exact (IH _ _ _ _ _ _ Hrel Hended).
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hd. reflexivity.
  - (* Let_static: the same bindings *)
    destruct (eval_static_bindings vars bindings statics) as [statics' | ]
      eqn:Hbindings; simpl in Hended.
    + apply (carried_step _ (State body vars conts' statics'));
        [ simpl; rewrite Hbindings; reflexivity | ].
      exact (IH _ _ _ _ _ _ Hrel Hended).
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hbindings. reflexivity.
  - (* Let_cont_non_recursive *)
    eapply carried_step; [ simpl; reflexivity | ].
    eapply IH; [ | exact Hended ].
    apply Forall2_cons; [ | exact Hrel ].
    split; [ reflexivity | ].
    apply Closure_related;
      [ apply Handler_same | exact Hrel | apply Forall2_nil ].
  - (* Let_cont_recursive *)
    eapply carried_step; [ simpl; reflexivity | ].
    eapply IH; [ | exact Hended ].
    apply Forall2_app; [ | exact Hrel ].
    apply rec_closures_related; [ apply handlers_related_refl | exact Hrel ].
  - (* Apply: the same call, returning to related continuations *)
    destruct (eval_simple vars (ap_callee ap)) as [closure | ] eqn:Hcallee;
      simpl in Hended;
      [ destruct (eval_simples vars (ap_args ap)) as [vs | ] eqn:Hargs;
        simpl in Hended
      | ].
    + destruct (call_function_cases closure (ap_call_kind ap) vs statics)
        as [Hundefined | (body & callee_vars & ret & exn & Hcall)].
      * rewrite Hundefined in Hended. apply ended_undefined in Hended.
        subst b. apply carried_undefined. simpl. rewrite Hcallee, Hargs.
        apply Hundefined.
      * rewrite Hcall in Hended.
        eapply carried_step;
          [ simpl; rewrite Hcallee, Hargs; apply Hcall | ].
        eapply IH; [ | exact Hended ].
        apply Forall2_cons;
          [ split; [ reflexivity | apply resolve_related, Hrel ] | ].
        apply Forall2_cons;
          [ split; [ reflexivity | apply resolve_related, Hrel ] | ].
        apply Forall2_nil.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hcallee, Hargs. reflexivity.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hcallee. reflexivity.
  - (* Apply_cont *)
    destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hargs;
      simpl in Hended.
    + unfold apply_continuation in Hended.
      pose proof
        (closure_related_inv _ _
           (resolve_related (ac_continuation ac) _ _ Hrel))
        as Hclosure.
      destruct (resolve (ac_continuation ac) conts)
        as [[params body] def_vars def_conts recursive | exit] eqn:Hl,
        (resolve (ac_continuation ac) conts')
        as [[params' body'] def_vars' def_conts' recursive' | exit']
             eqn:Hl';
        try contradiction; simpl in Hended.
      * (* handlers: related closures *)
        destruct Hclosure as (<- & Hh & Hconts & Hrec).
        apply handler_related_inv in Hh as [<- Hbody].
        destruct (bind_params params vs def_vars) as [handler_vars | ]
          eqn:Hbind; simpl in Hended.
        -- assert (Hcarried :
             carried
               (State body handler_vars
                  (rec_closures recursive' def_vars def_conts' ++ def_conts')
                  statics)
               b).
           { eapply IH; [ | exact Hended ].
             apply Forall2_app; [ | exact Hconts ].
             apply rec_closures_related; assumption. }
           apply (carried_step _
             (State body' handler_vars
                (rec_closures recursive' def_vars def_conts' ++ def_conts')
                statics)).
           ++ simpl. rewrite Hargs. unfold apply_continuation.
              rewrite Hl'. simpl. rewrite Hbind. reflexivity.
           ++ destruct Hbody as [Hbody | <-]; [ | exact Hcarried ].
              exact
                (carried_related _ _ _ _ _ _ _ _ _ Hbody Hbind Hcarried).
        -- apply ended_undefined in Hended. subst b.
           apply carried_undefined. simpl. rewrite Hargs.
           unfold apply_continuation. rewrite Hl'. simpl. rewrite Hbind.
           reflexivity.
      * (* ways out: the same exit *)
        subst exit'. apply ended_exit in Hended. subst b.
        apply carried_exit. simpl. rewrite Hargs.
        unfold apply_continuation. rewrite Hl'. reflexivity.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hargs. reflexivity.
  - (* Switch *)
    destruct (eval_simple vars scrutinee) as [v | ] eqn:Hscrutinee;
      simpl in Hended;
      [ destruct (naked_immediate_of_value v) as [i | ] eqn:Himmediate;
        simpl in Hended;
        [ destruct (find_arm i arms) as [ac | ] eqn:Hfind; simpl in Hended
        | ]
      | ].
    + apply (carried_step _ (State (Apply_cont ac) vars conts' statics));
        [ simpl; rewrite Hscrutinee, Himmediate, Hfind; reflexivity | ].
      exact (IH _ _ _ _ _ _ Hrel Hended).
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl.
      rewrite Hscrutinee, Himmediate, Hfind. reflexivity.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hscrutinee, Himmediate.
      reflexivity.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hscrutinee. reflexivity.
  - (* Invalid *)
    apply ended_undefined in Hended. subst b.
    apply carried_undefined. reflexivity.
Qed.

End Transfer.

(* ======================================================================== *)
(* Refinement under related environments                                    *)
(* ======================================================================== *)

(* The two halves of [refines], as properties to carry: forwards an exit,
   backwards the way the target ends or that the source goes wrong. *)
Definition exits_carried (s : state) (b : behaviour) : Prop :=
  match b with
  | Exits _ _ => behaves s b
  | Goes_wrong | Diverges => True
  end.

Definition ends_or_wrong (s : state) (b : behaviour) : Prop :=
  b <> Diverges -> behaves s b ∨ behaves s Goes_wrong.

(* A handler refines another where it runs: under the variables of its
   closure with its parameters bound, and any continuations. *)
Definition handler_refines_at (params : list variable) (def_vars : env)
    (source target : expr) : Prop :=
  ∀ (vs : list value) (handler_vars : env) (conts : cont_env)
    (statics : static_env),
    bind_params params vs def_vars = Some handler_vars ->
    refines (State source handler_vars conts statics)
      (State target handler_vars conts statics).

(* An expression under an environment refines it under one whose closures
   have refining handlers. The relation is needed in both directions, as
   the two halves of [refines] run different sides. *)
Lemma related_envs_refines (e : expr) (vars : env) (conts conts' : cont_env)
    (statics : static_env) :
  cont_env_related handler_refines_at conts conts' ->
  cont_env_related
    (fun params def_vars target source =>
       handler_refines_at params def_vars source target)
    conts' conts ->
  refines (State e vars conts statics) (State e vars conts' statics).
Proof.
  intros Hrel Hrel'. split.
  - intros k vs [n Hrun].
    refine (transfer handler_refines_at exits_carried _ _ _ _ n e vars conts
      conts' statics (Exits k vs) Hrel _).
    + intros s s' b Hstep.
      destruct b as [k' vs' | | ]; unfold exits_carried; auto.
      intros Hb. apply (step_behaves s (Exits k' vs')). rewrite Hstep.
      exact Hb.
    + intros s k' vs' Hstep. apply (step_behaves s (Exits k' vs')).
      rewrite Hstep. reflexivity.
    + intros s _. exact I.
    + intros params def_vars source target vs' handler_vars conts'' statics'
        b Hrefines Hbind.
      destruct b; unfold exits_carried; auto.
      apply (proj1 (Hrefines vs' handler_vars conts'' statics' Hbind)).
    + rewrite Hrun. simpl. auto.
  - intros b Hterm Hb. destruct (behaves_ended _ _ Hterm Hb) as [n Hended].
    refine (transfer
      (fun params def_vars target source =>
         handler_refines_at params def_vars source target)
      ends_or_wrong _ _ _ _ n e vars conts' conts statics b Hrel' Hended
      Hterm).
    + intros s s' b' Hstep Hcarried Hterm'.
      destruct (Hcarried Hterm') as [Hb' | Hwrong]; [ left | right ];
        [ apply (step_behaves s b') | apply (step_behaves s Goes_wrong) ];
        rewrite Hstep; assumption.
    + intros s k vs Hstep _. left. apply (step_behaves s (Exits k vs)).
      rewrite Hstep. reflexivity.
    + intros s Hstep _. left. apply (step_behaves s Goes_wrong).
      rewrite Hstep. reflexivity.
    + intros params def_vars target source vs handler_vars conts'' statics'
        b' Hrefines Hbind Hcarried Hterm'.
      destruct (Hrefines vs handler_vars conts'' statics' Hbind)
        as [_ Hends].
      destruct (Hcarried Hterm') as [Hb' | Hwrong];
        [ exact (Hends b' Hterm' Hb') | ].
      destruct (Hends Goes_wrong ltac:(discriminate) Hwrong); right;
        assumption.
Qed.

(* A [Let_cont] refines the same with a handler replaced by one that
   refines it where it runs. *)
Lemma let_cont_handler_refines_at (k : continuation) (params : list variable)
    (handler handler' body : expr) (vars : env) (conts : cont_env)
    (statics : static_env) :
  handler_refines_at params vars handler handler' ->
  refines
    (State (Let_cont_non_recursive k (Handler params handler) body) vars
       conts statics)
    (State (Let_cont_non_recursive k (Handler params handler') body) vars
       conts statics).
Proof.
  intros Hhandler. eapply refines_step; [ reflexivity | reflexivity | ].
  apply related_envs_refines;
    (apply Forall2_cons; [ | apply cont_env_related_refl ]);
    (split; [ reflexivity | ]);
    (apply Closure_related;
      [ apply Handler_related; exact Hhandler | apply cont_env_related_refl
      | apply Forall2_nil ]).
Qed.

Lemma let_cont_recursive_handler_refines_at
    (before : list (continuation * continuation_handler)) (k : continuation)
    (params : list variable) (handler handler' : expr)
    (after : list (continuation * continuation_handler)) (body : expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  handler_refines_at params vars handler handler' ->
  refines
    (State
       (Let_cont_recursive (before ++ (k, Handler params handler) :: after)
          body)
       vars conts statics)
    (State
       (Let_cont_recursive (before ++ (k, Handler params handler') :: after)
          body)
       vars conts statics).
Proof.
  intros Hhandler. eapply refines_step; [ reflexivity | reflexivity | ].
  apply related_envs_refines;
    (apply Forall2_app; [ | apply cont_env_related_refl ]);
    (apply rec_closures_related; [ | apply cont_env_related_refl ]);
    (apply Forall2_app; [ apply handlers_related_refl | ]);
    (apply Forall2_cons; [ | apply handlers_related_refl ]);
    (split; [ reflexivity | apply Handler_related; exact Hhandler ]).
Qed.

(* ======================================================================== *)
(* Contexts                                                                 *)
(* ======================================================================== *)

(* By induction on the context. A hole in a body: one step, then the
   induction. A hole in a handler: the handler refines where it runs, as
   it does everywhere. *)
Theorem plug_refines : plug_refines_statement.
Proof.
  intros c source target Hrefines.
  induction c
    as [ | x d c IH | bindings c IH | k h c IH | k params c IH body
       | handlers c IH | before k params c IH after body ];
    simpl; [ exact Hrefines | | | | | | ]; intros vars conts statics.
  - destruct (eval_named statics vars d) as [v | ] eqn:Hd.
    + eapply refines_step;
        [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity
        | apply IH ].
    + apply goes_wrong_refines. exists 1. simpl. rewrite Hd. reflexivity.
  - destruct (eval_static_bindings vars bindings statics) as [statics' | ]
      eqn:Hbindings.
    + eapply refines_step;
        [ simpl; rewrite Hbindings; reflexivity
        | simpl; rewrite Hbindings; reflexivity | apply IH ].
    + apply goes_wrong_refines. exists 1. simpl. rewrite Hbindings.
      reflexivity.
  - eapply refines_step; [ reflexivity | reflexivity | apply IH ].
  - apply let_cont_handler_refines_at.
    intros vs handler_vars conts' statics' _. apply IH.
  - eapply refines_step; [ reflexivity | reflexivity | apply IH ].
  - apply let_cont_recursive_handler_refines_at.
    intros vs handler_vars conts' statics' _. apply IH.
Qed.

Theorem plug_equivalent : plug_equivalent_statement.
Proof.
  intros c e e' Hequiv vars conts statics.
  apply refines_antisymmetric; apply plug_refines;
    apply expr_equivalent_refines; [ exact Hequiv | ].
  intros vars' conts' statics'. apply equivalent_sym, Hequiv.
Qed.
