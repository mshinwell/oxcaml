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


(* Proofs for FlambdaGiveScrutineeSpec.v. This file needs no review: what
   is to be reviewed is the statement there.

   [give_scrutinee x k i] changes an argument only where the variable
   holds the constant that the argument is, so the two runs are in
   step and pass the same values: a bisimulation, in which the term
   and the result are run under the same variables, and a continuation
   stands in the second run for the closure of the handler rewritten.
   What is known of [x] where an expression is holds of the variables
   that it runs under ([holds]).

   One closure is not so: that of a continuation whose handler is
   rewritten for the number of the arm that applies it (arm_fact),
   when [x] is not that number. It is in scope in the [Switch] and in
   the arm that the [Switch] takes, and nowhere else; the arm taken
   has another number, so does not apply it. The two states in which
   it is in scope have their own cases of the relation
   ([Rel_state_switch], [Rel_state_arm]). *)

From Stdlib Require Import ZArith List Bool Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaMapSpec FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaContextSpec FlambdaContextProofs
  FlambdaNormaliseSpec FlambdaNormaliseProofs
  FlambdaUnaliasParamsSpec FlambdaUnaliasParamsProofs
  FlambdaGiveScrutineeSpec.
Import ListNotations.

(* ======================================================================== *)
(* What the rewrite keeps of the syntax                                     *)
(* ======================================================================== *)

Lemma give_in_apply_cont_continuation (x : variable) (k : continuation)
    (i : nat) (known : option Z) (ac : apply_cont) :
  ac_continuation (give_in_apply_cont x k i known ac) = ac_continuation ac.
Proof.
  unfold give_in_apply_cont.
  destruct known; [ destruct (Pos.eqb _ _) | ]; reflexivity.
Qed.

Fixpoint give_scrutinee_binds_statics (x : variable) (k : continuation)
    (i : nat) (known : option Z) (e : expr) {struct e} :
  binds_statics (give_scrutinee x k i known e) = binds_statics e
with give_in_handler_binds_statics (x : variable) (k : continuation)
    (i : nat) (known : option Z) (h : continuation_handler) {struct h} :
  handler_binds_statics (give_in_handler x k i known h)
  = handler_binds_statics h.
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [give_scrutinee binds_statics]; try reflexivity.
    + apply give_scrutinee_binds_statics.
    + rewrite give_scrutinee_binds_statics. reflexivity.
    + rewrite give_in_handler_binds_statics, give_scrutinee_binds_statics.
      reflexivity.
    + rewrite give_scrutinee_binds_statics. f_equal.
      induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
      cbn [map existsb].
      rewrite give_in_handler_binds_statics, IH. reflexivity.
  - destruct h as [params metadata handler].
    cbn [give_in_handler handler_binds_statics].
    apply give_scrutinee_binds_statics.
Qed.

Definition give_handlers (x : variable) (k : continuation) (i : nat)
    (known : option Z) (handlers : list (continuation * continuation_handler))
    : list (continuation * continuation_handler) :=
  map (fun '(k', h) => (k', give_in_handler x k i known h)) handlers.

Lemma give_handlers_bind_statics (x : variable) (k : continuation) (i : nat)
    (known : option Z)
    (handlers : list (continuation * continuation_handler)) :
  handlers_bind_statics (give_handlers x k i known handlers)
  = handlers_bind_statics handlers.
Proof.
  unfold handlers_bind_statics, give_handlers.
  induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
  cbn [map existsb]. rewrite give_in_handler_binds_statics, IH.
  reflexivity.
Qed.

Lemma lookup_give_handlers (x : variable) (k : continuation) (i : nat)
    (known : option Z) (k1 : continuation)
    (handlers : list (continuation * continuation_handler)) :
  lookup k1 (give_handlers x k i known handlers)
  = option_map (give_in_handler x k i known) (lookup k1 handlers).
Proof.
  unfold give_handlers.
  induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
  cbn [map]. rewrite !lookup_cons, IH.
  destruct (Pos.eqb k1 k'); reflexivity.
Qed.

Lemma find_arm_give (x : variable) (k : continuation) (i : nat)
    (known : option Z) (scrutinee : simple) (j : Z)
    (arms : list (Z * apply_cont)) :
  find_arm j
    (map
       (fun '(d, ac) =>
          (d, give_in_apply_cont x k i (arm_known x scrutinee d known) ac))
       arms)
  = option_map (give_in_apply_cont x k i (arm_known x scrutinee j known))
      (find_arm j arms).
Proof.
  induction arms as [ | [d ac] arms IH]; [ reflexivity | ].
  cbn [map find_arm].
  destruct (Z.eqb_spec j d) as [-> | _]; [ reflexivity | exact IH ].
Qed.

(* What [arm_fact] finds. *)
Lemma arm_fact_some (x : variable) (k : continuation) (body : expr) (c : Z) :
  arm_fact x k body = Some c ->
  ∃ arms : list (Z * apply_cont),
    body = Switch (Var x) arms ∧ only_arm k c arms = true.
Proof.
  unfold arm_fact.
  destruct body as [ | | | | | | scrutinee arms | ]; try discriminate.
  destruct scrutinee as [y | | ]; try discriminate.
  destruct (Pos.eqb_spec y x) as [-> | _]; [ | discriminate ].
  destruct (first_arm_of k arms) as [c' | ]; [ | discriminate ].
  destruct (only_arm k c' arms) eqn:Honly; [ | discriminate ].
  intros [= <-]. exists arms. split; [ reflexivity | exact Honly ].
Qed.

(* An arm of another number does not apply the continuation. *)
Lemma only_arm_other (k : continuation) (c : Z)
    (arms : list (Z * apply_cont)) (j : Z) (ac : apply_cont) :
  only_arm k c arms = true ->
  (j, ac) ∈ arms ->
  j <> c ->
  ac_continuation ac <> k.
Proof.
  unfold only_arm. rewrite forallb_forall. intros Hall Hin Hne Heq.
  specialize (Hall (j, ac) Hin). cbn beta iota in Hall.
  apply orb_true_iff in Hall as [Hk | Hc].
  - apply negb_true_iff, Pos.eqb_neq in Hk. exact (Hk Heq).
  - apply Z.eqb_eq in Hc. exact (Hne Hc).
Qed.

(* ======================================================================== *)
(* Values                                                                   *)
(* ======================================================================== *)

Lemma naked_immediate_of_value_some (v : value) (j : Z) :
  naked_immediate_of_value v = Some j -> v = Value_const (Naked_immediate j).
Proof.
  destruct v; cbn [naked_immediate_of_value]; try discriminate.
  match goal with c : const |- _ => destruct c end; try discriminate.
  intros [= ->]. reflexivity.
Qed.

(* The arguments are worth what they were where the variable holds the
   constant. *)
Lemma eval_simples_give_nth (x : variable) (c : Z) (vars : env) :
  lookup x vars = Some (Value_const (Naked_immediate c)) ->
  ∀ (i : nat) (args : list simple),
    eval_simples vars (give_nth x c i args) = eval_simples vars args.
Proof.
  intros Hx. induction i as [ | i IH]; intros [ | a args]; cbn [give_nth];
    try reflexivity.
  - destruct a as [y | s | c0]; try reflexivity.
    destruct c0; try reflexivity.
    match goal with
    | |- context [Z.eqb ?c' c] => destruct (Z.eqb_spec c' c) as [-> | _]
    end; [ | reflexivity ].
    cbn [eval_simples eval_simple]. rewrite Hx. reflexivity.
  - cbn [eval_simples]. rewrite IH. reflexivity.
Qed.

(* ======================================================================== *)
(* One variable, one continuation, one position                             *)
(* ======================================================================== *)

Section Site.

Variables (x : variable) (k : continuation) (i : nat).

(* What is known of [x] holds of the variables. *)
Definition holds (known : option Z) (vars : env) : Prop :=
  ∀ c : Z,
    known = Some c -> lookup x vars = Some (Value_const (Naked_immediate c)).

Lemma eval_args_given (known : option Z) (vars : env) (ac : apply_cont) :
  holds known vars ->
  eval_simples vars (ac_args (give_in_apply_cont x k i known ac))
  = eval_simples vars (ac_args ac).
Proof.
  intros Hholds. unfold give_in_apply_cont.
  destruct known as [c | ]; [ | reflexivity ].
  destruct (Pos.eqb _ _); [ | reflexivity ].
  cbn [ac_args]. apply eval_simples_give_nth, Hholds. reflexivity.
Qed.

(* What a continuation name stands for in the two runs: the same thing;
   or two closures of one handler, under continuations so related; or
   the closure of a handler and that of the handler rewritten for what
   is known of [x] under the variables of the closure; or two so
   related with the same extra arguments; or what is left of the same
   over-application. *)
Inductive cont_rel : cont_value -> cont_value -> Prop :=
  | Rel_same (c : cont_value) : cont_rel c c
  | Rel_plain (hh : continuation_handler) (dv : env) (dc dc' : cont_env)
      (recursive : list (continuation * continuation_handler)) :
    (∀ k1 : continuation, cont_rel (resolve k1 dc) (resolve k1 dc')) ->
    cont_rel (Closure hh dv dc recursive) (Closure hh dv dc' recursive)
  | Rel_given (known : option Z) (hh : continuation_handler) (dv : env)
      (dc dc' : cont_env)
      (recursive : list (continuation * continuation_handler)) :
    holds known dv ->
    (∀ k1 : continuation, cont_rel (resolve k1 dc) (resolve k1 dc')) ->
    cont_rel (Closure hh dv dc recursive)
      (Closure (give_in_handler x k i known hh) dv dc'
         (give_handlers x k i known recursive))
  | Rel_extra (c c' : cont_value) (extra : list value) :
    cont_rel c c' -> cont_rel (Extra_args c extra) (Extra_args c' extra)
  | Rel_over (remaining : list value) (remaining_arity return_arity : arity)
      (return_to return_to' exn_to exn_to' : cont_value) :
    cont_rel return_to return_to' ->
    cont_rel exn_to exn_to' ->
    cont_rel
      (Over_application remaining remaining_arity return_arity return_to
         exn_to)
      (Over_application remaining remaining_arity return_arity return_to'
         exn_to').

Definition conts_rel (conts conts' : cont_env) : Prop :=
  ∀ k1 : continuation, cont_rel (resolve k1 conts) (resolve k1 conts').

(* Two states: an expression and the same rewritten for what is known,
   which holds; the same expression; and the two states that have in
   scope a continuation [k2] whose handler was rewritten for a number
   [c] that [x] is not: the [Switch] on [x], of which only arms of the
   number [c] apply [k2], and the arm taken, which does not apply
   it. *)
Inductive state_rel : state -> state -> Prop :=
  | Rel_state (known : option Z) (e : expr) (vars : env)
      (conts conts' : cont_env) (statics : static_env) (hp : heap) :
    holds known vars ->
    conts_rel conts conts' ->
    state_rel (State e vars conts statics hp)
      (State (give_scrutinee x k i known e) vars conts' statics hp)
  | Rel_state_same (e : expr) (vars : env) (conts conts' : cont_env)
      (statics : static_env) (hp : heap) :
    conts_rel conts conts' ->
    state_rel (State e vars conts statics hp) (State e vars conts' statics hp)
  | Rel_state_switch (c : Z) (k2 : continuation) (clo clo' : cont_value)
      (known : option Z) (arms : list (Z * apply_cont)) (vars : env)
      (conts conts' : cont_env) (statics : static_env) (hp : heap) :
    lookup x vars <> Some (Value_const (Naked_immediate c)) ->
    only_arm k2 c arms = true ->
    conts_rel conts conts' ->
    state_rel
      (State (Switch (Var x) arms) vars ((k2, clo) :: conts) statics hp)
      (State (give_scrutinee x k i known (Switch (Var x) arms)) vars
         ((k2, clo') :: conts') statics hp)
  | Rel_state_arm (k2 : continuation) (clo clo' : cont_value)
      (known : option Z) (ac : apply_cont) (vars : env)
      (conts conts' : cont_env) (statics : static_env) (hp : heap) :
    ac_continuation ac <> k2 ->
    holds known vars ->
    conts_rel conts conts' ->
    state_rel (State (Apply_cont ac) vars ((k2, clo) :: conts) statics hp)
      (State (Apply_cont (give_in_apply_cont x k i known ac)) vars
         ((k2, clo') :: conts') statics hp).

Lemma state_rel_refl (s : state) : state_rel s s.
Proof.
  destruct s as [e vars conts statics hp].
  apply Rel_state_same. intros k1. apply Rel_same.
Qed.

Lemma with_extra_args_rel (c c' : cont_value) (extra : list value) :
  cont_rel c c' ->
  cont_rel (with_extra_args c extra) (with_extra_args c' extra).
Proof.
  intros Hc. destruct extra; simpl; [ exact Hc | apply Rel_extra, Hc ].
Qed.

(* The closures of the handlers of a recursive [Let_cont]. *)
Lemma rec_conts_plain
    (handlers : list (continuation * continuation_handler))
    (vars : env) (conts conts' : cont_env) :
  conts_rel conts conts' ->
  conts_rel (rec_closures handlers vars conts ++ conts)
    (rec_closures handlers vars conts' ++ conts').
Proof.
  intros Hconts k1. rewrite !resolve_rec_closures.
  destruct (lookup k1 handlers) as [hh | ]; [ | apply Hconts ].
  apply Rel_plain. exact Hconts.
Qed.

Lemma rec_conts_given (known : option Z)
    (handlers : list (continuation * continuation_handler))
    (vars : env) (conts conts' : cont_env) :
  holds known vars ->
  conts_rel conts conts' ->
  conts_rel (rec_closures handlers vars conts ++ conts)
    (rec_closures (give_handlers x k i known handlers) vars conts' ++ conts').
Proof.
  intros Hholds Hconts k1.
  rewrite !resolve_rec_closures, lookup_give_handlers.
  destruct (lookup k1 handlers) as [hh | ]; cbn [option_map];
    [ | apply Hconts ].
  apply Rel_given; assumption.
Qed.

(* The same full call, returning and raising to related continuations. *)
Lemma call_code_rel (closure : value) (c : code) (vs : list value)
    (args_arity return_arity : arity)
    (return_to return_to' exn_to exn_to' : cont_value)
    (statics : static_env) (hp : heap) :
  cont_rel return_to return_to' ->
  cont_rel exn_to exn_to' ->
  result_related state_rel
    (call_code closure c vs args_arity return_arity return_to exn_to statics hp)
    (call_code closure c vs args_arity return_arity return_to' exn_to'
       statics hp).
Proof.
  intros Hreturn Hraise.
  destruct (call_code_cases closure c vs args_arity return_arity statics hp)
    as [Hundefined | (callee_vars & Hcall)].
  - rewrite !Hundefined. exact I.
  - rewrite !Hcall. simpl.
    apply Rel_state_same.
    intros k'.
    destruct (Pos.eq_dec k' (code_return_continuation c)) as [-> | Hne];
      [ rewrite !resolve_head; exact Hreturn | ].
    rewrite !(resolve_other k' (code_return_continuation c)) by exact Hne.
    destruct (Pos.eq_dec k' (code_exn_continuation c)) as [-> | Hne'];
      [ rewrite !resolve_head; exact Hraise | ].
    rewrite !(resolve_other k' (code_exn_continuation c)) by exact Hne'.
    apply Rel_same.
Qed.

Lemma run_call_rel (shape : option call_shape) (return_arity : arity)
    (return_to return_to' exn_to exn_to' : cont_value)
    (statics : static_env) (hp : heap) :
  cont_rel return_to return_to' ->
  cont_rel exn_to exn_to' ->
  (∀ partial : value,
    result_related state_rel
      (apply_cont_value return_to [partial] statics hp)
      (apply_cont_value return_to' [partial] statics hp)) ->
  result_related state_rel
    (run_call (fun partial => apply_cont_value return_to [partial] statics hp)
       shape return_arity return_to exn_to statics hp)
    (run_call (fun partial => apply_cont_value return_to' [partial] statics hp)
       shape return_arity return_to' exn_to' statics hp).
Proof.
  intros Hreturn Hraise Hpartial.
  destruct shape
    as [[closure c vs args_arity
        | closure c vs remaining args_arity remaining_arity | partial] | ];
    simpl.
  - apply call_code_rel; assumption.
  - apply call_code_rel; [ apply Rel_over; assumption | exact Hraise ].
  - apply Hpartial.
  - exact I.
Qed.

(* Related continuations, applied to the same values. *)
Lemma apply_cont_value_rel (c c' : cont_value) (statics : static_env)
    (hp : heap) :
  cont_rel c c' ->
  ∀ vs : list value,
    result_related state_rel (apply_cont_value c vs statics hp)
      (apply_cont_value c' vs statics hp).
Proof.
  intros Hc.
  induction Hc
    as [c
       | [ps m he] dv dc dc' recursive Hdc _
       | known [ps m he] dv dc dc' recursive Hholds Hdc _
       | c c' extra Hc IHc
       | remaining remaining_arity return_arity return_to return_to' exn_to
           exn_to' Hreturn IHreturn Hraise _];
    intros vs.
  - apply result_related_refl, state_rel_refl.
  - simpl.
    destruct (kinds_eqb (map kind_of_value vs) (hm_params_kinds m));
      [ | exact I ].
    destruct (bind_params ps vs dv) as [bound | ]; [ | exact I ].
    simpl. apply Rel_state_same. apply rec_conts_plain. exact Hdc.
  - cbn [give_in_handler apply_cont_value].
    destruct (kinds_eqb (map kind_of_value vs) (hm_params_kinds m));
      [ | exact I ].
    destruct (bind_params ps vs dv) as [bound | ] eqn:Hbound; [ | exact I ].
    cbn [result_related].
    apply (Rel_state (known_under x ps known)).
    + unfold known_under. destruct (among x ps) eqn:Hx; intros c Hc;
        [ discriminate | ].
      rewrite (lookup_bind_params_out ps vs dv bound x Hx Hbound).
      exact (Hholds c Hc).
    + apply rec_conts_given; assumption.
  - exact (IHc (vs ++ extra)).
  - rewrite !apply_cont_value_over_application.
    destruct vs as [ | v [ | v' vs]]; try exact I.
    unfold call_function.
    apply run_call_rel; [ exact Hreturn | exact Hraise | ].
    intros partial. exact (IHreturn [partial]).
Qed.

Lemma call_function_rel (callee : value) (call_kind : call_kind)
    (vs : list value) (args_arity return_arity : arity)
    (return_to return_to' exn_to exn_to' : cont_value)
    (statics : static_env) (hp : heap) :
  cont_rel return_to return_to' ->
  cont_rel exn_to exn_to' ->
  result_related state_rel
    (call_function callee call_kind vs args_arity return_arity return_to
       exn_to statics hp)
    (call_function callee call_kind vs args_arity return_arity return_to'
       exn_to' statics hp).
Proof.
  intros Hreturn Hraise. unfold call_function.
  apply run_call_rel; [ exact Hreturn | exact Hraise | ].
  intros partial. apply apply_cont_value_rel, Hreturn.
Qed.

(* A continuation bound over related continuations. *)
Lemma conts_rel_cons (k1 : continuation) (c c' : cont_value)
    (conts conts' : cont_env) :
  cont_rel c c' ->
  conts_rel conts conts' ->
  conts_rel ((k1, c) :: conts) ((k1, c') :: conts').
Proof.
  intros Hc Hconts k2. destruct (Pos.eq_dec k2 k1) as [-> | Hne].
  - rewrite !resolve_head. exact Hc.
  - rewrite !(resolve_other k2 k1) by exact Hne. apply Hconts.
Qed.

(* Two related states step together. *)
Lemma give_step (s s' : state) :
  state_rel s s' -> result_related state_rel (step s) (step s').
Proof.
  intros
    [known e vars conts conts' statics hp Hholds Hconts
    | e vars conts conts' statics hp Hconts
    | c k2 clo clo' known arms vars conts conts' statics hp Hnot Honly Hconts
    | k2 clo clo' known ac vars conts conts' statics hp Hne Hholds Hconts].
  - (* an expression and the same rewritten *)
    destruct e as [y kind1 d body | bindings body | k1 hh body
                  | handlers body | ap | ac | scrutinee arms | ];
      cbn [give_scrutinee].
    + rewrite !step_let.
      destruct (eval_named statics vars d) as [v | ]; [ | exact I ].
      destruct (kind_eqb (kind_of_value v) kind1); [ | exact I ].
      cbn [result_related]. apply Rel_state; [ | exact Hconts ].
      intros c Hc. destruct (Pos.eqb_spec y x) as [-> | Hyx];
        [ discriminate | ].
      rewrite lookup_other by congruence. exact (Hholds c Hc).
    + rewrite !step_let_static.
      destruct (eval_static_bindings vars bindings statics); [ | exact I ].
      cbn [result_related]. apply Rel_state; assumption.
    + rewrite !step_let_cont_non_recursive. cbn [result_related].
      destruct (arm_fact x k1 body) as [c | ] eqn:Hfact.
      * destruct (arm_fact_some x k1 body c Hfact) as (arms & -> & Honly).
        destruct (lookup x vars) as [v | ] eqn:Hv.
        -- destruct (naked_immediate_of_value v) as [j | ] eqn:Hj.
           ++ apply naked_immediate_of_value_some in Hj. subst v.
              destruct (Z.eq_dec j c) as [-> | Hjc].
              ** apply (Rel_state known (Switch (Var x) arms));
                   [ exact Hholds | ].
                 apply conts_rel_cons; [ | exact Hconts ].
                 apply (Rel_given (Some c) hh vars conts conts' []);
                   [ | exact Hconts ].
                 intros c' [= <-]. exact Hv.
              ** apply (Rel_state_switch c k1 _ _ known arms);
                   [ | exact Honly | exact Hconts ].
                 rewrite Hv. intros [= Heq]. exact (Hjc Heq).
           ++ apply (Rel_state_switch c k1 _ _ known arms);
                [ | exact Honly | exact Hconts ].
              rewrite Hv. intros [= ->]. discriminate.
        -- apply (Rel_state_switch c k1 _ _ known arms);
             [ | exact Honly | exact Hconts ].
           rewrite Hv. discriminate.
      * apply (Rel_state known body); [ exact Hholds | ].
        apply conts_rel_cons; [ | exact Hconts ].
        apply (Rel_given known hh vars conts conts' []); assumption.
    + rewrite !step_let_cont_recursive.
      fold (give_handlers x k i known handlers).
      rewrite give_handlers_bind_statics.
      destruct (handlers_bind_statics handlers); [ exact I | ].
      cbn [result_related]. apply (Rel_state known body); [ exact Hholds | ].
      apply rec_conts_given; assumption.
    + rewrite !step_apply.
      destruct (eval_simple vars (ap_callee ap)) as [callee | ]; [ | exact I ].
      destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | exact I ].
      destruct (eval_simples vars (exn_extra_simples ap)) as [extra | ];
        [ | exact I ].
      apply call_function_rel;
        [ apply Hconts | apply with_extra_args_rel, Hconts ].
    + rewrite !step_apply_cont, (eval_args_given known vars ac Hholds),
        give_in_apply_cont_continuation.
      destruct (eval_simples vars (ac_args ac)) as [vs | ]; [ | exact I ].
      unfold apply_continuation. apply apply_cont_value_rel, Hconts.
    + rewrite !step_switch.
      destruct (eval_simple vars scrutinee) as [v | ] eqn:Hv; [ | exact I ].
      destruct (naked_immediate_of_value v) as [j | ] eqn:Hj; [ | exact I ].
      rewrite find_arm_give.
      destruct (find_arm j arms) as [ac | ]; [ | exact I ].
      cbn [option_map result_related].
      apply (Rel_state (arm_known x scrutinee j known) (Apply_cont ac));
        [ | exact Hconts ].
      unfold arm_known. destruct scrutinee as [y | sym | cst];
        try exact Hholds.
      destruct (Pos.eqb_spec y x) as [-> | _]; [ | exact Hholds ].
      intros c' [= <-]. cbn [eval_simple] in Hv. rewrite Hv. f_equal.
      exact (naked_immediate_of_value_some v j Hj).
    + rewrite !step_invalid. exact I.
  - (* the same expression *)
    destruct e as [y kind1 d body | bindings body | k1 hh body
                  | handlers body | ap | ac | scrutinee arms | ].
    + rewrite !step_let.
      destruct (eval_named statics vars d) as [v | ]; [ | exact I ].
      destruct (kind_eqb (kind_of_value v) kind1); [ | exact I ].
      cbn [result_related]. apply Rel_state_same, Hconts.
    + rewrite !step_let_static.
      destruct (eval_static_bindings vars bindings statics); [ | exact I ].
      cbn [result_related]. apply Rel_state_same, Hconts.
    + rewrite !step_let_cont_non_recursive. cbn [result_related].
      apply Rel_state_same. apply conts_rel_cons; [ | exact Hconts ].
      apply Rel_plain, Hconts.
    + rewrite !step_let_cont_recursive.
      destruct (handlers_bind_statics handlers); [ exact I | ].
      cbn [result_related]. apply Rel_state_same, rec_conts_plain, Hconts.
    + rewrite !step_apply.
      destruct (eval_simple vars (ap_callee ap)) as [callee | ]; [ | exact I ].
      destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | exact I ].
      destruct (eval_simples vars (exn_extra_simples ap)) as [extra | ];
        [ | exact I ].
      apply call_function_rel;
        [ apply Hconts | apply with_extra_args_rel, Hconts ].
    + rewrite !step_apply_cont.
      destruct (eval_simples vars (ac_args ac)) as [vs | ]; [ | exact I ].
      unfold apply_continuation. apply apply_cont_value_rel, Hconts.
    + rewrite !step_switch.
      destruct (eval_simple vars scrutinee) as [v | ]; [ | exact I ].
      destruct (naked_immediate_of_value v) as [j | ]; [ | exact I ].
      destruct (find_arm j arms) as [ac | ]; [ | exact I ].
      cbn [result_related]. apply Rel_state_same, Hconts.
    + rewrite !step_invalid. exact I.
  - (* the [Switch], with a continuation in scope that is not applied *)
    cbn [give_scrutinee]. rewrite !step_switch. cbn [eval_simple].
    destruct (lookup x vars) as [v | ] eqn:Hv; [ | exact I ].
    destruct (naked_immediate_of_value v) as [j | ] eqn:Hj; [ | exact I ].
    rewrite find_arm_give.
    destruct (find_arm j arms) as [ac | ] eqn:Hfind; [ | exact I ].
    cbn [option_map result_related].
    apply naked_immediate_of_value_some in Hj. subst v.
    assert (Hjc : j <> c) by (intros ->; apply Hnot; reflexivity).
    apply (Rel_state_arm k2 clo clo' (arm_known x (Var x) j known) ac);
      [ | | exact Hconts ].
    + exact (only_arm_other k2 c arms j ac Honly (find_arm_in j arms ac Hfind)
        Hjc).
    + unfold arm_known. rewrite Pos.eqb_refl. intros c' [= <-]. exact Hv.
  - (* the arm taken *)
    rewrite !step_apply_cont, (eval_args_given known vars ac Hholds),
      give_in_apply_cont_continuation.
    destruct (eval_simples vars (ac_args ac)) as [vs | ]; [ | exact I ].
    unfold apply_continuation.
    rewrite !(resolve_other (ac_continuation ac) k2) by exact Hne.
    apply apply_cont_value_rel, Hconts.
Qed.

(* The rewrite gives an equivalent term, whatever is given. *)
Lemma give_scrutinee_equivalent (e : expr) :
  expr_equivalent e (give_scrutinee x k i None e).
Proof.
  intros vars conts statics hp.
  apply (bisimulation_equivalent state_rel give_step).
  apply (Rel_state None); [ intros c; discriminate | ].
  intros k1. apply Rel_same.
Qed.

End Site.

(* ======================================================================== *)
(* The pass                                                                 *)
(* ======================================================================== *)

Lemma give_at_equivalent (i : nat) (k : continuation)
    (h : continuation_handler) (body : expr) :
  expr_equivalent (Let_cont_non_recursive k h body)
    (Let_cont_non_recursive k h (give_at i k h body)).
Proof.
  unfold give_at.
  destruct (first_scrutinee k i None body) as [[x | ] | ];
    try (intros vars conts statics hp; apply equivalent_refl).
  destruct (unalias_param i k h (give_scrutinee x k i None body));
    [ | intros vars conts statics hp; apply equivalent_refl ].
  exact (plug_equivalent (Let_cont_non_recursive_body k h Hole) _ _
    (not_many _) (give_scrutinee_equivalent x k i body)).
Qed.

Lemma give_from_equivalent (i : nat) :
  ∀ (k : continuation) (h : continuation_handler) (body : expr),
    expr_equivalent (Let_cont_non_recursive k h body)
      (Let_cont_non_recursive k h (give_from i k h body)).
Proof.
  induction i as [ | i IH]; intros k h body; cbn [give_from].
  - intros vars conts statics hp. apply equivalent_refl.
  - exact (expr_equivalent_trans _ _ _ (give_at_equivalent i k h body)
      (IH k h (give_at i k h body))).
Qed.

(* Each layer is a context around what the induction gives; then the
   parameters of the [Let_cont] are looked at. *)
Fixpoint give_scrutinees_equivalent_aux (e : expr) :
  expr_equivalent e (give_scrutinees e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    cbn [give_scrutinees];
    try (intros vars conts statics hp; apply equivalent_refl).
  - exact (plug_equivalent (Let_body x kind d Hole) _ _ (not_many _)
      (give_scrutinees_equivalent_aux body)).
  - exact (plug_equivalent (Let_static_body bindings Hole) _ _ (not_many _)
      (give_scrutinees_equivalent_aux body)).
  - apply (expr_equivalent_trans _
      (Let_cont_non_recursive k
         (Handler params metadata (give_scrutinees handler)) body)).
    + exact (plug_equivalent
        (Let_cont_non_recursive_handler k params metadata Hole body) _ _
        (not_many _) (give_scrutinees_equivalent_aux handler)).
    + apply (expr_equivalent_trans _
        (Let_cont_non_recursive k
           (Handler params metadata (give_scrutinees handler))
           (give_scrutinees body))).
      * exact (plug_equivalent
          (Let_cont_non_recursive_body k
             (Handler params metadata (give_scrutinees handler)) Hole)
          _ _ (not_many _) (give_scrutinees_equivalent_aux body)).
      * apply give_from_equivalent.
  - exact (plug_equivalent (Let_cont_recursive_body handlers Hole) _ _
      (not_many _) (give_scrutinees_equivalent_aux body)).
Qed.

Theorem give_scrutinees_equivalent : give_scrutinees_equivalent_statement.
Proof. exact give_scrutinees_equivalent_aux. Qed.
