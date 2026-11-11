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

(* Continuations that behave alike may stand for each other. Nothing here
   needs review: there is no Spec file, as no reviewed statement is made
   with these definitions; they are a tool of proof.

   FlambdaContextProofs.v lets the handler of a continuation be replaced
   by one that refines it under all continuations. That is too much to
   ask of a rewrite which relies on what the continuations in scope at
   the handler stand for: moving a [Let_cont] into the handler that
   alone uses it is one (FlambdaSinkContsProofs.v). What such a rewrite
   can show is that the two closures, applied to the same values,
   come to the same thing ([applies_alike]): the closures are given, with
   the environments of their definition, so the continuations in scope
   are known.

   [replace_closure_equivalent] says that this is enough: an expression
   behaves alike under two continuation environments that differ in what
   one name is bound to, if the two things apply alike. The proof is
   that of FlambdaContextProofs.transfer, by induction on the length of
   a run that ends: the closures made on the way hold the one
   environment or the other and are otherwise the same ([alike]), and
   where one of the two given is applied the other comes to the same by
   assumption, with no need of the induction. Divergence follows
   (FlambdaSemanticsProofs.equivalent_of_terminating). *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaSemanticsProofs.
Import ListNotations.

(* ======================================================================== *)
(* What a result that has ended, or the state it is at, comes to            *)
(* ======================================================================== *)

Lemma ended_terminating (result : step_result) (b : behaviour) :
  ended result b -> b <> Diverges.
Proof. destruct result, b; simpl; try contradiction; discriminate. Qed.

(* A step followed by a run that has ended: the result of the step has
   the behaviour. *)
Lemma ended_after_step (result : step_result) (n : nat) (b : behaviour) :
  ended
    match result with
    | Step s' => run n s'
    | Exit k vs => Exit k vs
    | Undefined => Undefined
    end
    b ->
  result_behaves result b.
Proof.
  destruct result as [s' | k vs | ]; simpl.
  - apply ended_behaves.
  - apply ended_exit.
  - apply ended_undefined.
Qed.

(* A state has the behaviours of the result of its step. *)
Lemma behaves_of_step (s : state) (result : step_result) (b : behaviour) :
  step s = result -> result_behaves result b -> behaves s b.
Proof. intros <-. apply step_behaves. Qed.

(* ======================================================================== *)
(* Closures that are the same but for continuations that apply alike        *)
(* ======================================================================== *)

Section Alike.

(* The continuations that are taken to stand for each other. *)
Variable base : cont_value -> cont_value -> Prop.

(* The same continuation; two that are taken to stand for each other;
   closures of one handler under the same variables, whose continuations
   are in turn alike; or two that are alike, with the same extra
   arguments. (The warning silenced is about induction schemes for the
   nested occurrence, which nothing uses.) *)
#[local] Set Warnings "-register-all".
Inductive alike : cont_value -> cont_value -> Prop :=
  | Alike_same (c : cont_value) : alike c c
  | Alike_base (c c' : cont_value) : base c c' -> alike c c'
  | Alike_closure (h : continuation_handler) (vars : env)
      (conts conts' : cont_env)
      (recursive : list (continuation * continuation_handler)) :
    Forall2 (fun kc kc' => fst kc = fst kc' ∧ alike (snd kc) (snd kc')) conts
      conts' ->
    alike (Closure h vars conts recursive) (Closure h vars conts' recursive)
  | Alike_extra_args (c c' : cont_value) (extra : list value) :
    alike c c' -> alike (Extra_args c extra) (Extra_args c' extra).

Definition conts_alike (conts conts' : cont_env) : Prop :=
  Forall2 (fun kc kc' => fst kc = fst kc' ∧ alike (snd kc) (snd kc')) conts
    conts'.

Lemma conts_alike_refl (conts : cont_env) : conts_alike conts conts.
Proof.
  induction conts as [ | kc conts IH]; [ apply Forall2_nil | ].
  apply Forall2_cons; [ | exact IH ].
  split; [ reflexivity | apply Alike_same ].
Qed.

Lemma with_extra_args_alike (c c' : cont_value) (extra : list value) :
  alike c c' -> alike (with_extra_args c extra) (with_extra_args c' extra).
Proof.
  intros Halike. destruct extra; simpl;
    [ exact Halike | apply Alike_extra_args, Halike ].
Qed.

Lemma resolve_alike (k : continuation) (conts conts' : cont_env) :
  conts_alike conts conts' -> alike (resolve k conts) (resolve k conts').
Proof.
  unfold resolve.
  induction 1 as [ | [k1 c] [k1' c'] conts conts' [Hk Hc] _ IH]; simpl;
    [ apply Alike_same | ].
  simpl in Hk. subst k1'. destruct (Pos.eqb k k1); [ exact Hc | exact IH ].
Qed.

(* [all] is the whole list of handlers, kept apart from the ones still to
   be gone through. *)
Lemma rec_closures_alike_aux
    (handlers all : list (continuation * continuation_handler)) (vars : env)
    (conts conts' : cont_env) :
  conts_alike conts conts' ->
  conts_alike (map (fun '(k, h) => (k, Closure h vars conts all)) handlers)
    (map (fun '(k, h) => (k, Closure h vars conts' all)) handlers).
Proof.
  intros Hconts.
  induction handlers as [ | [k h] handlers IH]; simpl; [ apply Forall2_nil | ].
  apply Forall2_cons; [ | exact IH ].
  split; [ reflexivity | apply Alike_closure, Hconts ].
Qed.

Lemma rec_closures_alike
    (handlers : list (continuation * continuation_handler)) (vars : env)
    (conts conts' : cont_env) :
  conts_alike conts conts' ->
  conts_alike (rec_closures handlers vars conts ++ conts)
    (rec_closures handlers vars conts' ++ conts').
Proof.
  intros Hconts. apply Forall2_app; [ | exact Hconts ].
  apply rec_closures_alike_aux, Hconts.
Qed.

(* What is assumed of two continuations taken to stand for each other:
   applied to the same values, the second has every behaviour of the
   first that ends. *)
Hypothesis base_carries :
  ∀ (c c' : cont_value) (vs : list value) (statics : static_env)
    (b : behaviour),
    base c c' ->
    b <> Diverges ->
    result_behaves (apply_cont_value c vs statics) b ->
    result_behaves (apply_cont_value c' vs statics) b.

(* A run that ends under the first environment ends alike under the
   second. *)
Lemma alike_carries (n : nat) :
  ∀ (e : expr) (vars : env) (conts conts' : cont_env) (statics : static_env)
    (b : behaviour),
    conts_alike conts conts' ->
    ended (run n (State e vars conts statics)) b ->
    behaves (State e vars conts' statics) b.
Proof.
  induction n as [ | n IH];
    intros e vars conts conts' statics b Hrel Hended;
    [ destruct b; contradiction | ].
  rewrite run_succ in Hended.
  destruct e
    as [ x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    autorewrite with step in Hended.
  - (* Let *)
    eapply behaves_of_step; [ apply step_let | ].
    destruct (eval_named statics vars d) as [v | ]; simpl in Hended |- *;
      [ exact (IH _ _ _ _ _ _ Hrel Hended) | apply ended_undefined, Hended ].
  - (* Let_static *)
    eapply behaves_of_step; [ apply step_let_static | ].
    destruct (eval_static_bindings vars bindings statics) as [extended | ];
      simpl in Hended |- *;
      [ exact (IH _ _ _ _ _ _ Hrel Hended) | apply ended_undefined, Hended ].
  - (* Let_cont_non_recursive *)
    eapply behaves_of_step; [ apply step_let_cont_non_recursive | ].
    simpl in Hended |- *. refine (IH _ _ _ _ _ _ _ Hended).
    apply Forall2_cons; [ | exact Hrel ].
    split; [ reflexivity | apply Alike_closure, Hrel ].
  - (* Let_cont_recursive *)
    eapply behaves_of_step; [ apply step_let_cont_recursive | ].
    destruct (handlers_bind_statics handlers); simpl in Hended |- *;
      [ apply ended_undefined, Hended | ].
    exact (IH _ _ _ _ _ _ (rec_closures_alike _ _ _ _ Hrel) Hended).
  - (* Apply: the same call, returning to continuations that are alike *)
    eapply behaves_of_step; [ apply step_apply | ].
    destruct (eval_simple vars (ap_callee ap)) as [callee | ];
      [ | apply ended_undefined, Hended ].
    destruct (eval_simples vars (ap_args ap)) as [vs | ];
      [ | apply ended_undefined, Hended ].
    destruct (eval_simples vars (exn_extra_simples ap)) as [extra | ];
      [ | apply ended_undefined, Hended ].
    destruct (call_function_cases callee (ap_call_kind ap) vs
                (ap_args_arity ap) (ap_return_arity ap) statics)
      as [Hundefined | (body & callee_vars & ret & exn & Hcall)].
    + rewrite Hundefined in Hended |- *. apply ended_undefined, Hended.
    + rewrite Hcall in Hended |- *. simpl in Hended |- *.
      refine (IH _ _ _ _ _ _ _ Hended).
      apply Forall2_cons;
        [ split; [ reflexivity | apply resolve_alike, Hrel ] | ].
      apply Forall2_cons;
        [ split;
            [ reflexivity
            | apply with_extra_args_alike, resolve_alike, Hrel ]
        | ].
      apply Forall2_nil.
  - (* Apply_cont *)
    eapply behaves_of_step; [ apply step_apply_cont | ].
    destruct (eval_simples vars (ac_args ac)) as [vs | ];
      [ | apply ended_undefined, Hended ].
    unfold apply_continuation in Hended |- *.
    pose proof (resolve_alike (ac_continuation ac) _ _ Hrel) as Halike.
    remember (resolve (ac_continuation ac) conts) as c eqn:Hc.
    remember (resolve (ac_continuation ac) conts') as c' eqn:Hc'.
    clear Hc Hc'. revert vs Hended.
    induction Halike
      as [c | c c' Hbase
         | [params metadata handler] def_vars def_conts def_conts' recursive
             Hconts
         | c c' extra Halike IHalike];
      intros vs Hended.
    + (* the same continuation *)
      exact (ended_after_step _ _ _ Hended).
    + (* two that stand for each other *)
      exact (base_carries c c' vs statics b Hbase
        (ended_terminating _ _ Hended) (ended_after_step _ _ _ Hended)).
    + (* closures of one handler *)
      simpl in Hended |- *.
      destruct (bind_params params vs def_vars) as [handler_vars | ];
        simpl in Hended |- *; [ | apply ended_undefined, Hended ].
      exact (IH _ _ _ _ _ _ (rec_closures_alike _ _ _ _ Hconts) Hended).
    + (* the same extra arguments *)
      simpl in Hended |- *. exact (IHalike _ Hended).
  - (* Switch *)
    eapply behaves_of_step; [ apply step_switch | ].
    destruct (eval_simple vars scrutinee) as [v | ];
      [ | apply ended_undefined, Hended ].
    destruct (naked_immediate_of_value v) as [i | ];
      [ | apply ended_undefined, Hended ].
    destruct (find_arm i arms) as [ac | ];
      [ | apply ended_undefined, Hended ].
    simpl in Hended |- *. exact (IH _ _ _ _ _ _ Hrel Hended).
  - (* Invalid *)
    eapply behaves_of_step; [ apply step_invalid | ].
    apply ended_undefined, Hended.
Qed.

End Alike.

(* ======================================================================== *)
(* Continuations that apply alike                                           *)
(* ======================================================================== *)

(* Applied to the same values under the same static environment, the two
   are both undefined, or exit alike, or step to states that are
   equivalent. *)
Definition applies_alike (c c' : cont_value) : Prop :=
  ∀ (vs : list value) (statics : static_env),
    result_related equivalent (apply_cont_value c vs statics)
      (apply_cont_value c' vs statics).

Lemma applies_alike_sym (c c' : cont_value) :
  applies_alike c c' -> applies_alike c' c.
Proof.
  intros Halike vs statics. specialize (Halike vs statics).
  destruct (apply_cont_value c vs statics),
    (apply_cont_value c' vs statics);
    simpl in Halike |- *; try contradiction;
    [ apply equivalent_sym, Halike | | exact I ].
  destruct Halike as [-> ->]. auto.
Qed.

Lemma applies_alike_carries (c c' : cont_value) (vs : list value)
    (statics : static_env) (b : behaviour) :
  applies_alike c c' ->
  b <> Diverges ->
  result_behaves (apply_cont_value c vs statics) b ->
  result_behaves (apply_cont_value c' vs statics) b.
Proof.
  intros Halike _. specialize (Halike vs statics).
  destruct (apply_cont_value c vs statics),
    (apply_cont_value c' vs statics);
    simpl in Halike |- *; try contradiction;
    [ apply Halike | | auto ].
  destruct Halike as [-> ->]. auto.
Qed.

(* An expression behaves alike under two continuation environments that
   differ in what one name is bound to, if the two things apply alike. *)
Theorem replace_closure_equivalent (k : continuation) (c c' : cont_value)
    (e : expr) (vars : env) (conts : cont_env) (statics : static_env) :
  applies_alike c c' ->
  equivalent (State e vars ((k, c) :: conts) statics)
    (State e vars ((k, c') :: conts) statics).
Proof.
  intros Halike. apply equivalent_of_terminating. intros b Hb.
  split; intros Hbehaves;
    destruct (behaves_ended _ _ Hb Hbehaves) as [n Hended].
  - refine (alike_carries applies_alike applies_alike_carries n _ _ _ _ _ _ _
      Hended).
    apply Forall2_cons; [ | apply conts_alike_refl ].
    split; [ reflexivity | apply Alike_base, Halike ].
  - refine (alike_carries (fun c1 c2 => applies_alike c2 c1) _ n _ _ _ _ _ _ _
      Hended).
    + intros c1 c2 vs statics' b' Hbase.
      apply applies_alike_carries, applies_alike_sym, Hbase.
    + apply Forall2_cons; [ | apply conts_alike_refl ].
      split; [ reflexivity | apply Alike_base, Halike ].
Qed.

(* The same of a [Let_cont]: its handler may be replaced by one that, in
   a closure made where the [Let_cont] is, applies alike. *)
Lemma let_cont_handler_alike (k : continuation) (h h' : continuation_handler)
    (body : expr) (vars : env) (conts : cont_env) (statics : static_env) :
  applies_alike (Closure h vars conts []) (Closure h' vars conts []) ->
  equivalent (State (Let_cont_non_recursive k h body) vars conts statics)
    (State (Let_cont_non_recursive k h' body) vars conts statics).
Proof.
  intros Halike. apply let_cont_non_recursive_equivalent_step.
  apply replace_closure_equivalent, Halike.
Qed.
