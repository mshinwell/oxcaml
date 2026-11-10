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

(* The relation between the bodies of corresponding handlers. *)
Variable related : expr -> expr -> Prop.

Inductive handler_related
    : continuation_handler -> continuation_handler -> Prop :=
  | Handler_related (params : list variable) (e e' : expr) :
    related e e' -> handler_related (Handler params e) (Handler params e')
  | Handler_same (h : continuation_handler) : handler_related h h.

Definition handlers_related
    (handlers handlers' : list (continuation * continuation_handler))
    : Prop :=
  Forall2
    (fun kh kh' => fst kh = fst kh' ∧ handler_related (snd kh) (snd kh'))
    handlers handlers'.

(* Closures with related handlers and, in turn, related environments. (The
   warning silenced is about induction schemes, which nothing uses.) *)
#[local] Set Warnings "-register-all".
Inductive closure_related : cont_value -> cont_value -> Prop :=
  | Closure_related (h h' : continuation_handler) (vars : env)
      (conts conts' : cont_env)
      (recursive recursive' : list (continuation * continuation_handler)) :
    handler_related h h' ->
    Forall2
      (fun kc kc' => fst kc = fst kc' ∧ closure_related (snd kc) (snd kc'))
      conts conts' ->
    handlers_related recursive recursive' ->
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

Lemma handlers_related_refl
    (handlers : list (continuation * continuation_handler)) :
  handlers_related handlers handlers.
Proof.
  induction handlers as [ | kh handlers IH]; [ apply Forall2_nil | ].
  apply Forall2_cons; [ | exact IH ].
  split; [ reflexivity | apply Handler_same ].
Qed.

Lemma closure_related_inv (h h' : continuation_handler) (vars vars' : env)
    (conts conts' : cont_env)
    (recursive recursive' : list (continuation * continuation_handler)) :
  closure_related (Closure h vars conts recursive)
    (Closure h' vars' conts' recursive') ->
  vars = vars' ∧ handler_related h h' ∧ cont_env_related conts conts'
  ∧ handlers_related recursive recursive'.
Proof.
  intros Hrel. inversion Hrel; subst.
  - auto.
  - split; [ reflexivity | ]. split; [ apply Handler_same | ].
    split; [ apply cont_env_related_refl | apply handlers_related_refl ].
Qed.

Lemma handler_related_inv (params params' : list variable) (e e' : expr) :
  handler_related (Handler params e) (Handler params' e') ->
  params = params' ∧ (related e e' ∨ e = e').
Proof. intros Hrel. inversion Hrel; subst; auto. Qed.

(* Related environments bind the same continuations, to related closures. *)
Lemma lookup_related (k : continuation) (conts conts' : cont_env) :
  cont_env_related conts conts' ->
  match lookup k conts, lookup k conts' with
  | None, None => True
  | Some c, Some c' => closure_related c c'
  | _, _ => False
  end.
Proof.
  induction 1 as [ | [k1 c] [k1' c'] conts conts' [Hk Hc] _ IH]; simpl;
    [ exact I | ].
  simpl in Hk. subst k1'. destruct (Pos.eqb k k1); [ exact Hc | exact IH ].
Qed.

(* [all] and [all'] are the whole lists of handlers, kept apart from the
   ones still to be gone through. *)
Lemma rec_closures_related_aux
    (handlers handlers' all all' : list (continuation * continuation_handler))
    (vars : env) (conts conts' : cont_env) :
  handlers_related handlers handlers' ->
  handlers_related all all' ->
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
  handlers_related handlers handlers' ->
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
   corresponding one, under any one pair of environments. *)
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
  ∀ (e e' : expr) (vars : env) (conts : cont_env) (b : behaviour),
    related e e' ->
    carried (State e vars conts) b -> carried (State e' vars conts) b.

Lemma transfer (n : nat) :
  ∀ (e : expr) (vars : env) (conts conts' : cont_env) (b : behaviour),
    cont_env_related conts conts' ->
    ended (run n (State e vars conts)) b ->
    carried (State e vars conts') b.
Proof.
  induction n as [ | n IH]; intros e vars conts conts' b Hrel Hended;
    [ destruct b; contradiction | ].
  destruct e as [x d body | k h body | handlers body | ac | scrutinee arms | ];
    simpl in Hended.
  - (* Let *)
    destruct (eval_named vars d) as [v | ] eqn:Hd; simpl in Hended.
    + apply (carried_step _ (State body ((x, v) :: vars) conts'));
        [ simpl; rewrite Hd; reflexivity | ].
      exact (IH _ _ _ _ _ Hrel Hended).
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hd. reflexivity.
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
  - (* Apply_cont *)
    destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hargs;
      simpl in Hended.
    + unfold apply_continuation in Hended.
      pose proof (lookup_related (ac_continuation ac) _ _ Hrel) as Hlookup.
      destruct (lookup (ac_continuation ac) conts)
        as [[[params body] def_vars def_conts recursive] | ] eqn:Hl,
        (lookup (ac_continuation ac) conts')
        as [[[params' body'] def_vars' def_conts' recursive'] | ] eqn:Hl';
        try contradiction.
      * (* a bound continuation: related closures *)
        apply closure_related_inv in Hlookup as (<- & Hh & Hconts & Hrec).
        apply handler_related_inv in Hh as [<- Hbody].
        destruct (bind_params params vs def_vars) as [handler_vars | ]
          eqn:Hbind; simpl in Hended.
        -- assert (Hcarried :
             carried
               (State body handler_vars
                  (rec_closures recursive' def_vars def_conts' ++ def_conts'))
               b).
           { eapply IH; [ | exact Hended ].
             apply Forall2_app; [ | exact Hconts ].
             apply rec_closures_related; assumption. }
           apply (carried_step _
             (State body' handler_vars
                (rec_closures recursive' def_vars def_conts' ++ def_conts'))).
           ++ simpl. rewrite Hargs. unfold apply_continuation.
              rewrite Hl', Hbind. reflexivity.
           ++ destruct Hbody as [Hbody | <-]; [ | exact Hcarried ].
              exact (carried_related _ _ _ _ _ Hbody Hcarried).
        -- apply ended_undefined in Hended. subst b.
           apply carried_undefined. simpl. rewrite Hargs.
           unfold apply_continuation. rewrite Hl', Hbind. reflexivity.
      * (* an unbound continuation: the same exit *)
        apply ended_exit in Hended. subst b.
        apply carried_exit. simpl. rewrite Hargs.
        unfold apply_continuation. rewrite Hl'. reflexivity.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hargs. reflexivity.
  - (* Switch *)
    destruct (eval_simple vars scrutinee) as [[[i | i]] | ] eqn:Hscrutinee;
      simpl in Hended;
      [ destruct (find_arm i arms) as [ac | ] eqn:Hfind; simpl in Hended
      | | ].
    + apply (carried_step _ (State (Apply_cont ac) vars conts'));
        [ simpl; rewrite Hscrutinee, Hfind; reflexivity | ].
      exact (IH _ _ _ _ _ Hrel Hended).
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hscrutinee, Hfind.
      reflexivity.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. simpl. rewrite Hscrutinee. reflexivity.
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

(* An expression under an environment refines it under one whose closures
   have refining handlers. The relation is needed in both directions, as
   the two halves of [refines] run different sides. *)
Lemma related_envs_refines (e : expr) (vars : env) (conts conts' : cont_env) :
  cont_env_related expr_refines conts conts' ->
  cont_env_related (fun target source => expr_refines source target)
    conts' conts ->
  refines (State e vars conts) (State e vars conts').
Proof.
  intros Hrel Hrel'. split.
  - intros k vs [n Hrun].
    refine (transfer expr_refines exits_carried _ _ _ _ n e vars conts conts'
      (Exits k vs) Hrel _).
    + intros s s' b Hstep.
      destruct b as [k' vs' | | ]; unfold exits_carried; auto.
      intros Hb. apply (step_behaves s (Exits k' vs')). rewrite Hstep.
      exact Hb.
    + intros s k' vs' Hstep. apply (step_behaves s (Exits k' vs')).
      rewrite Hstep. reflexivity.
    + intros s _. exact I.
    + intros source target vars' conts'' b Hrefines.
      destruct b; unfold exits_carried; auto.
      apply (proj1 (Hrefines vars' conts'')).
    + rewrite Hrun. simpl. auto.
  - intros b Hterm Hb. destruct (behaves_ended _ _ Hterm Hb) as [n Hended].
    refine (transfer (fun target source => expr_refines source target)
      ends_or_wrong _ _ _ _ n e vars conts' conts b Hrel' Hended Hterm).
    + intros s s' b' Hstep Hcarried Hterm'.
      destruct (Hcarried Hterm') as [Hb' | Hwrong]; [ left | right ];
        [ apply (step_behaves s b') | apply (step_behaves s Goes_wrong) ];
        rewrite Hstep; assumption.
    + intros s k vs Hstep _. left. apply (step_behaves s (Exits k vs)).
      rewrite Hstep. reflexivity.
    + intros s Hstep _. left. apply (step_behaves s Goes_wrong).
      rewrite Hstep. reflexivity.
    + intros target source vars' conts'' b' Hrefines Hcarried Hterm'.
      destruct (Hrefines vars' conts'') as [_ Hends].
      destruct (Hcarried Hterm') as [Hb' | Hwrong];
        [ exact (Hends b' Hterm' Hb') | ].
      destruct (Hends Goes_wrong ltac:(discriminate) Hwrong); right;
        assumption.
Qed.

(* ======================================================================== *)
(* Contexts                                                                 *)
(* ======================================================================== *)

(* By induction on the context. A hole in a body: one step, then the
   induction. A hole in a handler: one step, which builds closures that
   differ in that handler only. *)
Theorem plug_refines : plug_refines_statement.
Proof.
  intros c source target Hrefines.
  induction c
    as [ | x d c IH | k h c IH | k params c IH body | handlers c IH
       | before k params c IH after body ];
    simpl; [ exact Hrefines | | | | | ]; intros vars conts.
  - destruct (eval_named vars d) as [v | ] eqn:Hd.
    + eapply refines_step;
        [ simpl; rewrite Hd; reflexivity | simpl; rewrite Hd; reflexivity
        | apply IH ].
    + apply goes_wrong_refines. exists 1. simpl. rewrite Hd. reflexivity.
  - eapply refines_step; [ reflexivity | reflexivity | apply IH ].
  - eapply refines_step; [ reflexivity | reflexivity | ].
    apply related_envs_refines;
      (apply Forall2_cons; [ | apply cont_env_related_refl ]);
      (split; [ reflexivity | ]);
      (apply Closure_related;
        [ apply Handler_related, IH | apply cont_env_related_refl
        | apply Forall2_nil ]).
  - eapply refines_step; [ reflexivity | reflexivity | apply IH ].
  - eapply refines_step; [ reflexivity | reflexivity | ].
    apply related_envs_refines;
      (apply Forall2_app; [ | apply cont_env_related_refl ]);
      (apply rec_closures_related; [ | apply cont_env_related_refl ]);
      (apply Forall2_app; [ apply handlers_related_refl | ]);
      (apply Forall2_cons; [ | apply handlers_related_refl ]);
      (split; [ reflexivity | apply Handler_related, IH ]).
Qed.

Theorem plug_equivalent : plug_equivalent_statement.
Proof.
  intros c e e' Hequiv vars conts.
  apply refines_antisymmetric; apply plug_refines;
    apply expr_equivalent_refines; [ exact Hequiv | ].
  intros vars' conts'. apply equivalent_sym, Hequiv.
Qed.
