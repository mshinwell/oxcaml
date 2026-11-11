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
   (FlambdaSemanticsProofs.equivalent_of_terminating).

   A hole in code is the same again for the static environment: the proof
   relates static environments whose code has related bodies
   ([statics_related]), and where the code is called the induction gives
   the first body under the second environments. Values hold code ids and
   not code, so the values of the two runs stay equal.

   The relations may rely on a property of the static environment that,
   once it holds, holds of every extension ([statics_ok]): what a name is
   bound to never changes (FlambdaWellFormedSpec.v), so a handler may be
   rewritten using the bindings made before its definition. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaSemanticsProofs FlambdaWellFormedSpec
  FlambdaWellFormedProofs FlambdaContextSpec.
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
  | Handler_related (params : list variable) (metadata : handler_metadata)
      (e e' : expr) :
    related params vars e e' ->
    handler_related vars (Handler params metadata e)
      (Handler params metadata e')
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
    (metadata metadata' : handler_metadata) (e e' : expr) :
  handler_related vars (Handler params metadata e)
    (Handler params' metadata' e') ->
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

(* ======================================================================== *)
(* Related static environments                                              *)
(* ======================================================================== *)

(* The relation between the bodies of corresponding code. Code runs under
   variables, continuations and a static environment that the call
   decides, so the relation is not relative to any. *)
Variable code_related : expr -> expr -> Prop.

Inductive codes_related : code -> code -> Prop :=
  | Codes_related (params : list variable) (my_closure : variable)
      (ret exn : continuation) (metadata : code_metadata)
      (body body' : expr) :
    binds_statics body = binds_statics body' ->
    code_related body body' ->
    codes_related (Code params my_closure ret exn metadata body)
      (Code params my_closure ret exn metadata body')
  | Codes_same (c : code) : codes_related c c.

Inductive binding_related : static_binding -> static_binding -> Prop :=
  | Binding_code (id : code_id) (c c' : code) :
    codes_related c c' -> binding_related (Bind_code id c) (Bind_code id c')
  | Binding_same (binding : static_binding) : binding_related binding binding.

(* Static environments with the same statically allocated values and, for
   each code id, related code. Values hold code ids and not code, so they
   need no relation. *)
Definition statics_related (statics statics' : static_env) : Prop :=
  Forall2
    (fun ic ic' => fst ic = fst ic' ∧ codes_related (snd ic) (snd ic'))
    (static_code statics) (static_code statics')
  ∧ static_values statics = static_values statics'.

Lemma statics_related_refl (statics : static_env) :
  statics_related statics statics.
Proof.
  split; [ | reflexivity ].
  induction (static_code statics) as [ | ic code IH];
    [ apply Forall2_nil | ].
  apply Forall2_cons; [ | exact IH ].
  split; [ reflexivity | apply Codes_same ].
Qed.

Lemma bindings_related_refl (bindings : list static_binding) :
  Forall2 binding_related bindings bindings.
Proof.
  induction bindings as [ | binding bindings IH]; [ apply Forall2_nil | ].
  apply Forall2_cons; [ apply Binding_same | exact IH ].
Qed.

Lemma lookup_code_related (id : code_id) (statics statics' : static_env) :
  statics_related statics statics' ->
  match lookup id (static_code statics), lookup id (static_code statics') with
  | Some c, Some c' => codes_related c c'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros [Hcode _].
  induction Hcode as [ | [id1 c] [id1' c'] code code' [Hid Hc] _ IH]; simpl;
    [ exact I | ].
  simpl in Hid. subst id1'. destruct (Pos.eqb id id1); [ exact Hc | exact IH ].
Qed.

Lemma closure_of_related (statics statics' : static_env) (v : value) :
  statics_related statics statics' ->
  closure_of statics v = closure_of statics' v.
Proof.
  intros [_ Hvalues]. unfold closure_of. rewrite Hvalues. reflexivity.
Qed.

Lemma project_value_slot_related (statics statics' : static_env)
    (project_from : function_slot) (slot : value_slot) (v : value) :
  statics_related statics statics' ->
  project_value_slot statics project_from slot v
  = project_value_slot statics' project_from slot v.
Proof.
  intros [_ Hvalues]. unfold project_value_slot, closure_in_set.
  rewrite Hvalues. reflexivity.
Qed.

Lemma project_function_slot_related (statics statics' : static_env)
    (move_from move_to : function_slot) (v : value) :
  statics_related statics statics' ->
  project_function_slot statics move_from move_to v
  = project_function_slot statics' move_from move_to v.
Proof.
  intros [_ Hvalues]. unfold project_function_slot. rewrite Hvalues.
  reflexivity.
Qed.

Lemma eval_named_related (statics statics' : static_env) (vars : env)
    (d : named) :
  statics_related statics statics' ->
  eval_named statics vars d = eval_named statics' vars d.
Proof.
  intros Hstatics.
  destruct d as
    [s | p args | code slots | slot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure];
    simpl; try reflexivity.
  - destruct (eval_simples vars args) as [vs | ]; simpl; [ | reflexivity ].
    apply eval_prim_same_static_values, Hstatics.
  - destruct (eval_simple vars closure) as [v | ]; simpl; [ | reflexivity ].
    rewrite (closure_of_related statics statics' v Hstatics). reflexivity.
  - destruct (eval_simple vars closure) as [v | ]; simpl; [ | reflexivity ].
    apply project_value_slot_related, Hstatics.
  - destruct (eval_simple vars closure) as [v | ]; simpl; [ | reflexivity ].
    apply project_function_slot_related, Hstatics.
Qed.

(* Related groups of bindings added to related static environments: both
   fail, or the results are related. *)
Lemma eval_static_bindings_related (vars : env)
    (bindings bindings' : list static_binding) :
  Forall2 binding_related bindings bindings' ->
  ∀ statics statics' : static_env,
    statics_related statics statics' ->
    match
      eval_static_bindings vars bindings statics,
      eval_static_bindings vars bindings' statics'
    with
    | Some extended, Some extended' => statics_related extended extended'
    | None, None => True
    | _, _ => False
    end.
Proof.
  induction 1 as [ | binding binding' bindings bindings' Hbinding _ IH];
    intros statics statics' Hstatics; simpl; [ exact Hstatics | ].
  pose proof Hstatics as [Hcode Hvalues].
  destruct Hbinding as [id c c' Hc | [id c | id | sym const]]; simpl.
  - pose proof (lookup_code_related id statics statics' Hstatics) as Hid.
    destruct (lookup id (static_code statics)),
      (lookup id (static_code statics')); try contradiction; [ exact I | ].
    apply IH. split; [ | exact Hvalues ].
    apply Forall2_cons; [ split; [ reflexivity | exact Hc ] | exact Hcode ].
  - pose proof (lookup_code_related id statics statics' Hstatics) as Hid.
    destruct (lookup id (static_code statics)),
      (lookup id (static_code statics')); try contradiction; [ exact I | ].
    apply IH. split; [ | exact Hvalues ].
    apply Forall2_cons; [ | exact Hcode ].
    split; [ reflexivity | apply Codes_same ].
  - apply IH. split; assumption.
  - rewrite <- Hvalues.
    destruct (lookup sym (static_values statics)); [ exact I | ].
    destruct (eval_static_const vars const) as [allocated | ]; simpl;
      [ | exact I ].
    apply IH. split; [ exact Hcode | ]. simpl. rewrite Hvalues. reflexivity.
Qed.

(* A call under related static environments: undefined under both, or it
   runs related bodies under the same variables, with the two
   continuations of the code bound to what the caller gave. *)
Lemma call_function_related (callee : value) (kind : call_kind)
    (vs : list value) (statics statics' : static_env) :
  statics_related statics statics' ->
  ((∀ return_to exn_to : cont_value,
     call_function callee kind vs return_to exn_to statics = Undefined)
   ∧ (∀ return_to exn_to : cont_value,
       call_function callee kind vs return_to exn_to statics' = Undefined))
  ∨ (∃ (body body' : expr) (callee_vars : env) (ret exn : continuation),
      (code_related body body' ∨ body = body')
      ∧ (∀ return_to exn_to : cont_value,
          call_function callee kind vs return_to exn_to statics
          = Step
              (State body callee_vars [(ret, return_to); (exn, exn_to)]
                 statics))
      ∧ (∀ return_to exn_to : cont_value,
          call_function callee kind vs return_to exn_to statics'
          = Step
              (State body' callee_vars [(ret, return_to); (exn, exn_to)]
                 statics'))).
Proof.
  intros Hstatics. unfold call_function.
  rewrite <- (closure_of_related statics statics' callee Hstatics).
  destruct (closure_of statics callee) as [[called slots] | ];
    [ | left; split; reflexivity ].
  destruct
    (match kind with
     | Direct named => Pos.eqb called named
     | Indirect => true
     end);
    [ | left; split; reflexivity ].
  pose proof (lookup_code_related called statics statics' Hstatics) as Hc.
  destruct (lookup called (static_code statics)) as [c | ],
    (lookup called (static_code statics')) as [c' | ];
    try contradiction; [ | left; split; reflexivity ].
  destruct Hc
    as [params my_closure ret exn metadata body body'
          Hbinds Hbody
       | c];
    simpl.
  - rewrite <- Hbinds.
    destruct (binds_statics body); [ left; split; reflexivity | ].
    destruct (bind_params params vs [(my_closure, callee)])
      as [callee_vars | ]; [ | left; split; reflexivity ].
    right. exists body, body', callee_vars, ret, exn.
    split; [ left; exact Hbody | split; reflexivity ].
  - destruct (binds_statics (code_body c)); [ left; split; reflexivity | ].
    destruct (bind_params (code_params c) vs [(code_my_closure c, callee)])
      as [callee_vars | ]; [ | left; split; reflexivity ].
    right.
    exists (code_body c), (code_body c), callee_vars,
      (code_return_continuation c), (code_exn_continuation c).
    split; [ right; reflexivity | split; reflexivity ].
Qed.

(* ======================================================================== *)
(* One expression under related environments                                *)
(* ======================================================================== *)

(* What is to be carried from a run under the first environments to the
   state under the second: a property of a state and a behaviour that holds
   of a state when it holds of the state it steps to, that holds of how a
   state ends at once, and that [related] carries from a handler to the
   corresponding one, under the variables of their closures with the
   parameters bound, and [code_related] from a body to the corresponding
   one, under any environments. *)
Variable statics_ok : static_env -> Prop.

Hypothesis statics_ok_extend :
  ∀ statics statics' : static_env,
    statics_ok statics -> statics_extend statics statics' ->
    statics_ok statics'.

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
    statics_ok statics ->
    bind_params params vs def_vars = Some handler_vars ->
    carried (State e handler_vars conts statics) b ->
    carried (State e' handler_vars conts statics) b.

Hypothesis carried_code_related :
  ∀ (e e' : expr) (vars : env) (conts : cont_env) (statics : static_env)
    (b : behaviour),
    code_related e e' ->
    statics_ok statics ->
    carried (State e vars conts statics) b ->
    carried (State e' vars conts statics) b.

Lemma transfer (n : nat) :
  ∀ (e : expr) (vars : env) (conts conts' : cont_env)
    (statics statics' : static_env) (b : behaviour),
    cont_env_related conts conts' ->
    statics_related statics statics' ->
    statics_ok statics' ->
    ended (run n (State e vars conts statics)) b ->
    carried (State e vars conts' statics') b.
Proof.
  induction n as [ | n IH];
    intros e vars conts conts' statics statics' b Hrel Hstatics Hok Hended;
    [ destruct b; contradiction | ].
  rewrite run_succ in Hended.
  destruct e
    as [ x kind d body | bindings body | k h body | handlers body | ap | ac
       | scrutinee arms | ];
    autorewrite with step in Hended; simpl in Hended.
  - (* Let *)
    destruct (eval_named statics vars d) as [v | ] eqn:Hd; simpl in Hended.
    + apply (carried_step _ (State body ((x, v) :: vars) conts' statics'));
        [ rewrite step_let,
            <- (eval_named_related statics statics' vars d Hstatics), Hd;
          reflexivity
        | ].
      exact (IH _ _ _ _ _ _ _ Hrel Hstatics Hok Hended).
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined.
      rewrite step_let,
        <- (eval_named_related statics statics' vars d Hstatics), Hd.
      reflexivity.
  - (* Let_static: the same bindings, added to related environments *)
    pose proof (eval_static_bindings_related vars bindings bindings
      (bindings_related_refl bindings) statics statics' Hstatics)
      as Hextended.
    destruct (eval_static_bindings vars bindings statics) as [extended | ],
      (eval_static_bindings vars bindings statics') as [extended' | ]
        eqn:Hbindings';
      try contradiction; simpl in Hended.
    + apply (carried_step _ (State body vars conts' extended'));
        [ rewrite step_let_static, Hbindings'; reflexivity | ].
      refine (IH _ _ _ _ _ _ _ Hrel Hextended _ Hended).
      exact (statics_ok_extend _ _ Hok
        (eval_static_bindings_extend vars bindings statics' extended'
           Hbindings')).
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. rewrite step_let_static, Hbindings'.
      reflexivity.
  - (* Let_cont_non_recursive *)
    eapply carried_step; [ apply step_let_cont_non_recursive | ].
    eapply IH; [ | exact Hstatics | exact Hok | exact Hended ].
    apply Forall2_cons; [ | exact Hrel ].
    split; [ reflexivity | ].
    apply Closure_related;
      [ apply Handler_same | exact Hrel | apply Forall2_nil ].
  - (* Let_cont_recursive *)
    destruct (handlers_bind_statics handlers) eqn:Hbinds; simpl in Hended;
      [ apply ended_undefined in Hended; subst b; apply carried_undefined;
        rewrite step_let_cont_recursive, Hbinds; reflexivity
      | ].
    eapply carried_step;
      [ rewrite step_let_cont_recursive, Hbinds; reflexivity | ].
    eapply IH; [ | exact Hstatics | exact Hok | exact Hended ].
    apply Forall2_app; [ | exact Hrel ].
    apply rec_closures_related; [ apply handlers_related_refl | exact Hrel ].
  - (* Apply: the same call of related code, returning to related
       continuations *)
    destruct (eval_simple vars (ap_callee ap)) as [closure | ] eqn:Hcallee;
      simpl in Hended;
      [ destruct (eval_simples vars (ap_args ap)) as [vs | ] eqn:Hargs;
        simpl in Hended
      | ].
    + destruct (call_function_related closure (ap_call_kind ap) vs statics
                  statics' Hstatics)
        as [[Hundefined Hundefined']
           | (body & body' & callee_vars & ret & exn & Hbody & Hcall
              & Hcall')].
      * rewrite Hundefined in Hended. apply ended_undefined in Hended.
        subst b. apply carried_undefined. rewrite step_apply, Hcallee, Hargs.
        apply Hundefined'.
      * rewrite Hcall in Hended.
        assert (Hcarried :
          carried
            (State body callee_vars
               [(ret, resolve (ap_continuation ap) conts');
                (exn, resolve (ap_exn_continuation ap) conts')]
               statics')
            b).
        { eapply IH; [ | exact Hstatics | exact Hok | exact Hended ].
          apply Forall2_cons;
            [ split; [ reflexivity | apply resolve_related, Hrel ] | ].
          apply Forall2_cons;
            [ split; [ reflexivity | apply resolve_related, Hrel ] | ].
          apply Forall2_nil. }
        apply (carried_step _
          (State body' callee_vars
             [(ret, resolve (ap_continuation ap) conts');
              (exn, resolve (ap_exn_continuation ap) conts')]
             statics'));
          [ rewrite step_apply, Hcallee, Hargs; apply Hcall' | ].
        destruct Hbody as [Hbody | <-]; [ | exact Hcarried ].
        exact (carried_code_related _ _ _ _ _ _ Hbody Hok Hcarried).
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. rewrite step_apply, Hcallee, Hargs. reflexivity.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. rewrite step_apply, Hcallee. reflexivity.
  - (* Apply_cont *)
    destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hargs;
      simpl in Hended.
    + unfold apply_continuation in Hended.
      pose proof
        (closure_related_inv _ _
           (resolve_related (ac_continuation ac) _ _ Hrel))
        as Hclosure.
      destruct (resolve (ac_continuation ac) conts)
        as [[params metadata body] def_vars def_conts recursive | exit]
             eqn:Hl,
        (resolve (ac_continuation ac) conts')
        as [[params' metadata' body'] def_vars' def_conts' recursive'
           | exit']
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
                  statics')
               b).
           { eapply IH; [ | exact Hstatics | exact Hok | exact Hended ].
             apply Forall2_app; [ | exact Hconts ].
             apply rec_closures_related; assumption. }
           apply (carried_step _
             (State body' handler_vars
                (rec_closures recursive' def_vars def_conts' ++ def_conts')
                statics')).
           ++ exact
                (step_apply_cont_handler _ _ _ _ _ _ _ _ _ _ _ _ Hargs Hl'
                   Hbind).
           ++ destruct Hbody as [Hbody | <-]; [ | exact Hcarried ].
              exact
                (carried_related _ _ _ _ _ _ _ _ _ Hbody Hok Hbind Hcarried).
        -- apply ended_undefined in Hended. subst b.
           apply carried_undefined. rewrite step_apply_cont, Hargs.
           unfold apply_continuation. rewrite Hl'. simpl. rewrite Hbind.
           reflexivity.
      * (* ways out: the same exit *)
        subst exit'. apply ended_exit in Hended. subst b.
        apply carried_exit.
        exact (step_apply_cont_exit _ _ _ _ _ _ Hargs Hl').
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. rewrite step_apply_cont, Hargs. reflexivity.
  - (* Switch *)
    destruct (eval_simple vars scrutinee) as [v | ] eqn:Hscrutinee;
      simpl in Hended;
      [ destruct (naked_immediate_of_value v) as [i | ] eqn:Himmediate;
        simpl in Hended;
        [ destruct (find_arm i arms) as [ac | ] eqn:Hfind; simpl in Hended
        | ]
      | ].
    + apply (carried_step _ (State (Apply_cont ac) vars conts' statics'));
        [ rewrite step_switch, Hscrutinee, Himmediate, Hfind; reflexivity | ].
      exact (IH _ _ _ _ _ _ _ Hrel Hstatics Hok Hended).
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined.
      rewrite step_switch, Hscrutinee, Himmediate, Hfind. reflexivity.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. rewrite step_switch, Hscrutinee, Himmediate.
      reflexivity.
    + apply ended_undefined in Hended. subst b.
      apply carried_undefined. rewrite step_switch, Hscrutinee. reflexivity.
  - (* Invalid *)
    apply ended_undefined in Hended. subst b.
    apply carried_undefined, step_invalid.
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
   closure with its parameters bound, any continuations, and any static
   environment of which [ok] holds. *)
Definition handler_refines_where (ok : static_env -> Prop)
    (params : list variable) (def_vars : env) (source target : expr)
    : Prop :=
  ∀ (vs : list value) (handler_vars : env) (conts : cont_env)
    (statics : static_env),
    ok statics ->
    bind_params params vs def_vars = Some handler_vars ->
    refines (State source handler_vars conts statics)
      (State target handler_vars conts statics).

Definition expr_refines_where (ok : static_env -> Prop)
    (source target : expr) : Prop :=
  ∀ (vars : env) (conts : cont_env) (statics : static_env),
    ok statics ->
    refines (State source vars conts statics)
      (State target vars conts statics).

(* The same under any static environment. *)
Definition handler_refines_at (params : list variable) (def_vars : env)
    (source target : expr) : Prop :=
  ∀ (vs : list value) (handler_vars : env) (conts : cont_env)
    (statics : static_env),
    bind_params params vs def_vars = Some handler_vars ->
    refines (State source handler_vars conts statics)
      (State target handler_vars conts statics).

Definition always (statics : static_env) : Prop := True.

Lemma always_extend (statics statics' : static_env) :
  always statics -> statics_extend statics statics' -> always statics'.
Proof. intros _ _. exact I. Qed.

Section Where.

Variable ok : static_env -> Prop.

Hypothesis ok_extend :
  ∀ statics statics' : static_env,
    ok statics -> statics_extend statics statics' -> ok statics'.

(* An expression under environments refines it under ones whose closures
   have refining handlers and whose code has refining bodies. The
   relations are needed in both directions, as the two halves of [refines]
   run different sides. *)
Lemma related_states_refines (e : expr) (vars : env)
    (conts conts' : cont_env) (statics statics' : static_env) :
  ok statics -> ok statics' ->
  cont_env_related (handler_refines_where ok) conts conts' ->
  cont_env_related
    (fun params def_vars target source =>
       handler_refines_where ok params def_vars source target)
    conts' conts ->
  statics_related (expr_refines_where ok) statics statics' ->
  statics_related (fun target source => expr_refines_where ok source target)
    statics' statics ->
  refines (State e vars conts statics) (State e vars conts' statics').
Proof.
  intros Hok Hok' Hrel Hrel' Hstatics Hstatics'. split.
  - intros k vs [n Hrun].
    refine (transfer (handler_refines_where ok) (expr_refines_where ok) ok
      ok_extend exits_carried _ _ _ _ _
      n e vars conts conts' statics statics' (Exits k vs) Hrel Hstatics
      Hok' _).
    + intros s s' b Hstep.
      destruct b as [k' vs' | | ]; unfold exits_carried; auto.
      intros Hb. apply (step_behaves s (Exits k' vs')). rewrite Hstep.
      exact Hb.
    + intros s k' vs' Hstep. apply (step_behaves s (Exits k' vs')).
      rewrite Hstep. reflexivity.
    + intros s _. exact I.
    + intros params def_vars source target vs' handler_vars conts''
        statics'' b Hrefines Hok'' Hbind.
      destruct b; unfold exits_carried; auto.
      apply (proj1 (Hrefines vs' handler_vars conts'' statics'' Hok'' Hbind)).
    + intros source target vars' conts'' statics'' b Hrefines Hok''.
      destruct b; unfold exits_carried; auto.
      apply (proj1 (Hrefines vars' conts'' statics'' Hok'')).
    + rewrite Hrun. simpl. auto.
  - intros b Hterm Hb. destruct (behaves_ended _ _ Hterm Hb) as [n Hended].
    refine (transfer
      (fun params def_vars target source =>
         handler_refines_where ok params def_vars source target)
      (fun target source => expr_refines_where ok source target)
      ok ok_extend ends_or_wrong _ _ _ _ _ n e vars conts' conts statics'
      statics b Hrel' Hstatics' Hok Hended Hterm).
    + intros s s' b' Hstep Hcarried Hterm'.
      destruct (Hcarried Hterm') as [Hb' | Hwrong]; [ left | right ];
        [ apply (step_behaves s b') | apply (step_behaves s Goes_wrong) ];
        rewrite Hstep; assumption.
    + intros s k vs Hstep _. left. apply (step_behaves s (Exits k vs)).
      rewrite Hstep. reflexivity.
    + intros s Hstep _. left. apply (step_behaves s Goes_wrong).
      rewrite Hstep. reflexivity.
    + intros params def_vars target source vs handler_vars conts''
        statics'' b' Hrefines Hok'' Hbind Hcarried Hterm'.
      destruct (Hrefines vs handler_vars conts'' statics'' Hok'' Hbind)
        as [_ Hends].
      destruct (Hcarried Hterm') as [Hb' | Hwrong];
        [ exact (Hends b' Hterm' Hb') | ].
      destruct (Hends Goes_wrong ltac:(discriminate) Hwrong); right;
        assumption.
    + intros target source vars' conts'' statics'' b' Hrefines Hok''
        Hcarried Hterm'.
      destruct (Hrefines vars' conts'' statics'' Hok'') as [_ Hends].
      destruct (Hcarried Hterm') as [Hb' | Hwrong];
        [ exact (Hends b' Hterm' Hb') | ].
      destruct (Hends Goes_wrong ltac:(discriminate) Hwrong); right;
        assumption.
Qed.

(* The case of one static environment. *)
Lemma related_envs_refines (e : expr) (vars : env) (conts conts' : cont_env)
    (statics : static_env) :
  ok statics ->
  cont_env_related (handler_refines_where ok) conts conts' ->
  cont_env_related
    (fun params def_vars target source =>
       handler_refines_where ok params def_vars source target)
    conts' conts ->
  refines (State e vars conts statics) (State e vars conts' statics).
Proof.
  intros Hok Hrel Hrel'.
  apply related_states_refines; try assumption; apply statics_related_refl.
Qed.

(* A [Let_cont] refines the same with a handler replaced by one that
   refines it where it runs. *)
Lemma let_cont_handler_refines_where (k : continuation)
    (params : list variable) (metadata : handler_metadata)
    (handler handler' body : expr) (vars : env) (conts : cont_env)
    (statics : static_env) :
  ok statics ->
  handler_refines_where ok params vars handler handler' ->
  refines
    (State
       (Let_cont_non_recursive k (Handler params metadata handler) body)
       vars conts statics)
    (State
       (Let_cont_non_recursive k (Handler params metadata handler') body)
       vars conts statics).
Proof.
  intros Hok Hhandler. apply let_cont_non_recursive_refines_step.
  apply related_envs_refines; [ exact Hok | | ];
    (apply Forall2_cons; [ | apply cont_env_related_refl ]);
    (split; [ reflexivity | ]);
    (apply Closure_related;
      [ apply Handler_related; exact Hhandler | apply cont_env_related_refl
      | apply Forall2_nil ]).
Qed.

(* The same for recursive handlers, any number of them replaced. *)
Lemma let_cont_recursive_handlers_refine_where
    (handlers handlers' : list (continuation * continuation_handler))
    (body : expr) (vars : env) (conts : cont_env) (statics : static_env) :
  ok statics ->
  handlers_bind_statics handlers = handlers_bind_statics handlers' ->
  handlers_related (handler_refines_where ok) vars handlers handlers' ->
  handlers_related
    (fun params def_vars target source =>
       handler_refines_where ok params def_vars source target)
    vars handlers' handlers ->
  refines (State (Let_cont_recursive handlers body) vars conts statics)
    (State (Let_cont_recursive handlers' body) vars conts statics).
Proof.
  intros Hok Hbinds Hhandlers Hhandlers'.
  apply let_cont_recursive_refines_step; [ exact Hbinds | intros _ ].
  apply related_envs_refines; [ exact Hok | | ];
    (apply Forall2_app; [ | apply cont_env_related_refl ]);
    (apply rec_closures_related; [ assumption | apply cont_env_related_refl ]).
Qed.

End Where.

Lemma handler_refines_at_where (params : list variable) (def_vars : env)
    (source target : expr) :
  handler_refines_at params def_vars source target ->
  handler_refines_where always params def_vars source target.
Proof. intros H vs handler_vars conts statics _. apply H. Qed.

Lemma let_cont_handler_refines_at (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler handler' body : expr) (vars : env)
    (conts : cont_env) (statics : static_env) :
  handler_refines_at params vars handler handler' ->
  refines
    (State
       (Let_cont_non_recursive k (Handler params metadata handler) body)
       vars conts statics)
    (State
       (Let_cont_non_recursive k (Handler params metadata handler') body)
       vars conts statics).
Proof.
  intros Hhandler.
  apply (let_cont_handler_refines_where always always_extend);
    [ exact I | apply handler_refines_at_where, Hhandler ].
Qed.

Lemma let_cont_recursive_handler_refines_at
    (before : list (continuation * continuation_handler)) (k : continuation)
    (params : list variable) (metadata : handler_metadata)
    (handler handler' : expr)
    (after : list (continuation * continuation_handler)) (body : expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  binds_statics handler = binds_statics handler' ->
  handler_refines_at params vars handler handler' ->
  refines
    (State
       (Let_cont_recursive
          (before ++ (k, Handler params metadata handler) :: after) body)
       vars conts statics)
    (State
       (Let_cont_recursive
          (before ++ (k, Handler params metadata handler') :: after) body)
       vars conts statics).
Proof.
  intros Hbinds Hhandler.
  apply (let_cont_recursive_handlers_refine_where always always_extend);
    [ exact I
    | unfold handlers_bind_statics; rewrite !existsb_app; simpl;
      rewrite Hbinds; reflexivity
    | | ];
    (apply Forall2_app; [ apply handlers_related_refl | ]);
    (apply Forall2_cons; [ | apply handlers_related_refl ]);
    (split; [ reflexivity | ]); apply Handler_related;
    apply handler_refines_at_where, Hhandler.
Qed.

(* A [Let_static] refines the same with the body of a piece of code
   replaced by one that refines it. *)
Lemma let_static_code_refines (before : list static_binding) (id : code_id)
    (params : list variable) (my_closure : variable)
    (ret exn : continuation) (metadata : code_metadata)
    (code_body code_body' : expr) (after : list static_binding) (body : expr)
    (vars : env) (conts : cont_env) (statics : static_env) :
  binds_statics code_body = binds_statics code_body' ->
  expr_refines code_body code_body' ->
  refines
    (State
       (Let_static
          (before
           ++ Bind_code id
                (Code params my_closure ret exn metadata code_body)
           :: after)
          body)
       vars conts statics)
    (State
       (Let_static
          (before
           ++ Bind_code id
                (Code params my_closure ret exn metadata code_body')
           :: after)
          body)
       vars conts statics).
Proof.
  intros Hbinds Hcode.
  set (c := Code params my_closure ret exn metadata code_body).
  set (c' := Code params my_closure ret exn metadata code_body').
  assert (Hbindings :
    ∀ (R : expr -> expr -> Prop) (c1 c2 : code),
      codes_related R c1 c2 ->
      Forall2 (binding_related R) (before ++ Bind_code id c1 :: after)
        (before ++ Bind_code id c2 :: after)).
  { intros R c1 c2 Hc. apply Forall2_app; [ apply bindings_related_refl | ].
    apply Forall2_cons; [ | apply bindings_related_refl ].
    apply Binding_code, Hc. }
  assert (Hwhere : expr_refines_where always code_body code_body')
    by (intros vars' conts' statics' _; apply Hcode).
  pose proof (eval_static_bindings_related (expr_refines_where always) vars
    _ _
    (Hbindings (expr_refines_where always) c c'
       (Codes_related _ _ _ _ _ _ _ _ Hbinds Hwhere))
    statics statics (statics_related_refl _ statics)) as Hforwards.
  pose proof (eval_static_bindings_related
    (fun target source => expr_refines_where always source target) vars _ _
    (Hbindings _ c' c
       (Codes_related
          (fun target source => expr_refines_where always source target)
          params my_closure ret exn metadata code_body'
          code_body (eq_sym Hbinds) Hwhere))
    statics statics (statics_related_refl _ statics)) as Hbackwards.
  apply let_static_refines_step.
  destruct
    (eval_static_bindings vars (before ++ Bind_code id c :: after) statics)
    as [extended | ],
    (eval_static_bindings vars (before ++ Bind_code id c' :: after) statics)
    as [extended' | ];
    try contradiction; [ | exact I ].
  apply (related_states_refines always always_extend);
    [ exact I | exact I | apply cont_env_related_refl
    | apply cont_env_related_refl | exact Hforwards | exact Hbackwards ].
Qed.

(* ======================================================================== *)
(* Contexts                                                                 *)
(* ======================================================================== *)

(* For a context whose hole is not in code or in a recursive handler. *)
Lemma not_many (P : Prop) : false = true -> P.
Proof. discriminate. Qed.

Lemma plug_binds_statics (c : context) (e e' : expr) :
  binds_statics e = binds_statics e' ->
  binds_statics (plug c e) = binds_statics (plug c e').
Proof.
  intros Hbinds.
  induction c
    as [ | x kind d c IH | bindings c IH
       | before id params my_closure ret exn metadata c IH
           after body
       | k h c IH | k params metadata c IH body | handlers c IH
       | before k params metadata c IH after body ];
    simpl; try congruence.
  - rewrite !existsb_app. reflexivity.
  - rewrite !existsb_app. simpl. rewrite IH. reflexivity.
Qed.

(* By induction on the context. A hole in a body: one step, then the
   induction. A hole in a handler: the handler refines where it runs, as
   it does everywhere. A hole in code: the body refines. *)
Theorem plug_refines : plug_refines_statement.
Proof.
  intros c source target Hbinds Hrefines.
  induction c
    as [ | x kind d c IH | bindings c IH
       | before id params my_closure ret exn metadata c IH
           after body
       | k h c IH | k params metadata c IH body | handlers c IH
       | before k params metadata c IH after body ];
    simpl in Hbinds |- *; [ exact Hrefines | | | | | | | ];
    intros vars conts statics.
  - apply let_refines_step; [ reflexivity | intros v _ ]. apply IH, Hbinds.
  - apply let_static_refines_step.
    destruct (eval_static_bindings vars bindings statics) as [statics' | ];
      [ apply IH, Hbinds | exact I ].
  - apply let_static_code_refines;
      [ apply plug_binds_statics, Hbinds, eq_refl
      | apply IH; intros _; apply Hbinds, eq_refl ].
  - apply let_cont_non_recursive_refines_step, IH, Hbinds.
  - apply let_cont_handler_refines_at.
    intros vs handler_vars conts' statics' _. apply IH, Hbinds.
  - apply let_cont_recursive_refines_step; [ reflexivity | intros _ ].
    apply IH, Hbinds.
  - apply let_cont_recursive_handler_refines_at;
      [ apply plug_binds_statics, Hbinds, eq_refl | ].
    intros vs handler_vars conts' statics' _. apply IH.
    intros _. apply Hbinds, eq_refl.
Qed.

Theorem plug_equivalent : plug_equivalent_statement.
Proof.
  intros c e e' Hbinds Hequiv vars conts statics.
  apply refines_antisymmetric; apply plug_refines;
    try (apply expr_equivalent_refines; exact Hequiv);
    try exact Hbinds.
  - intros Hmany. symmetry. apply Hbinds, Hmany.
  - intros vars' conts' statics'. apply equivalent_refines, equivalent_sym.
    apply Hequiv.
Qed.
