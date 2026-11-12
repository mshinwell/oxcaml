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

(* Proofs of the statements of FlambdaLoopsScopeSpec.v. Nothing here
   needs review. The relation between a term and one that keeps its
   scope, with its lemmas, is in FlambdaScopedProofs.v; what is known
   of the following of aliases is in FlambdaKeepsScopeProofs.v. *)

From Stdlib Require Import ZArith List Bool Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaBindersSpec
  FlambdaNormaliseSpec FlambdaNormaliseProofs FlambdaUnusedContsSpec
  FlambdaUnusedContsProofs FlambdaLoopAliasesSpec FlambdaLoopifySpec
  FlambdaRecHandlersSpec FlambdaShortcutSpec FlambdaSinkContsSpec
  FlambdaUnusedParamsSpec FlambdaValidatorEquivarianceSpec
  FlambdaScopedProofs FlambdaKeepsScopeProofs FlambdaLoopsScopeSpec.
From OxCamlFlambda2Types Require Import FlambdaTypesSpec FlambdaAliasesSpec.
Import ListNotations.

(* Moving a continuation to the handler that alone uses it. *)

(* A [Let_cont] moved past a [Let], past a group of static bindings,
   into the handler of the next [Let_cont], and past that one. *)
Lemma scoped_let_cont_past_let (k : continuation) (h : continuation_handler)
    (x : variable) (kind : flambda_kind) (d : named) (body sunk : expr) :
  scoped (Let_cont_non_recursive k h body) sunk ->
  scoped (Let_cont_non_recursive k h (Let x kind d body))
    (Let x kind d sunk).
Proof.
  intros Hsunk Hclosed. scope_in Hclosed. scope.
  destruct (Hsunk Hclosed) as (Hclosed' & Hv & Hk). scope_in Hv. scope_in Hk.
  split; [ exact Hclosed' | split; [ | exact Hk ] ].
  intros y Hy. apply in_app_or in Hy. apply in_or_app.
  destruct Hy as [Hy | Hy]; [ right; apply in_or_app; left; exact Hy | ].
  apply in_without in Hy. destruct Hy as [Hy Hx].
  apply Hv, in_app_or in Hy.
  destruct Hy as [Hy | Hy]; [ left; exact Hy | right ].
  apply in_or_app. right. apply in_without. split; assumption.
Qed.

Lemma scoped_let_cont_past_let_static (k : continuation)
    (h : continuation_handler) (bindings : list static_binding)
    (body sunk : expr) :
  scoped (Let_cont_non_recursive k h body) sunk ->
  scoped (Let_cont_non_recursive k h (Let_static bindings body))
    (Let_static bindings sunk).
Proof.
  intros Hsunk Hclosed. scope_in Hclosed. scope.
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hh Hclosed].
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hgroup Hbody].
  assert (Hboth : code_closed (Let_cont_non_recursive k h body) = true)
    by (scope; rewrite Hh, Hbody; reflexivity).
  destruct (Hsunk Hboth) as (Hclosed' & Hv & Hk). scope_in Hv. scope_in Hk.
  rewrite Hgroup, Hclosed'. split; [ reflexivity | split ].
  - intros y Hy. apply in_app_or in Hy. apply in_or_app.
    destruct Hy as [Hy | Hy]; [ right; apply in_or_app; left; exact Hy | ].
    apply Hv, in_app_or in Hy.
    destruct Hy as [Hy | Hy]; [ left; exact Hy | right ].
    apply in_or_app. right. exact Hy.
  - rewrite (bindings_closed_no_continuations bindings Hgroup). exact Hk.
Qed.

Lemma scoped_let_cont_into_handler (k k' : continuation)
    (h : continuation_handler) (params : list variable)
    (metadata : handler_metadata) (handler body sunk : expr) :
  cont_free_b k body = false ->
  scoped (Let_cont_non_recursive k h handler) sunk ->
  scoped
    (Let_cont_non_recursive k h
       (Let_cont_non_recursive k' (Handler params metadata handler) body))
    (Let_cont_non_recursive k' (Handler params metadata sunk) body).
Proof.
  intros Hunused Hsunk Hclosed. scope_in Hclosed. scope.
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hh Hclosed].
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hhandler Hbody].
  assert (Hboth : code_closed (Let_cont_non_recursive k h handler) = true)
    by (scope; rewrite Hh, Hhandler; reflexivity).
  destruct (Hsunk Hboth) as (Hclosed' & Hv & Hk). scope_in Hv. scope_in Hk.
  rewrite Hclosed', Hbody. split; [ reflexivity | split ].
  - intros y Hy. apply in_app_or in Hy. apply in_or_app.
    destruct Hy as [Hy | Hy];
      [ | right; apply in_or_app; right; exact Hy ].
    apply in_without in Hy. destruct Hy as [Hy Hparams].
    apply Hv, in_app_or in Hy.
    destruct Hy as [Hy | Hy]; [ left; exact Hy | right ].
    apply in_or_app. left. apply in_without. split; assumption.
  - intros j Hj. apply in_app_or in Hj. apply in_or_app.
    destruct Hj as [Hj | Hj].
    + apply Hk, in_app_or in Hj.
      destruct Hj as [Hj | Hj]; [ left; exact Hj | right ].
      apply in_without in Hj. destruct Hj as [Hj Hout].
      apply in_without.
      split; [ apply in_or_app; left; exact Hj | exact Hout ].
    + right. apply in_without.
      split; [ apply in_or_app; right; exact Hj | ].
      apply in_without in Hj. destruct Hj as [Hj _].
      intros [<- | []].
      rewrite (cont_free_b_free k body Hbody Hj) in Hunused. discriminate.
Qed.

Lemma scoped_let_cont_past_let_cont (k k' : continuation)
    (h : continuation_handler) (params : list variable)
    (metadata : handler_metadata) (handler body sunk : expr) :
  cont_free_b k handler = false ->
  scoped (Let_cont_non_recursive k h body) sunk ->
  scoped
    (Let_cont_non_recursive k h
       (Let_cont_non_recursive k' (Handler params metadata handler) body))
    (Let_cont_non_recursive k' (Handler params metadata handler) sunk).
Proof.
  intros Hunused Hsunk Hclosed. scope_in Hclosed. scope.
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hh Hclosed].
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hhandler Hbody].
  assert (Hboth : code_closed (Let_cont_non_recursive k h body) = true)
    by (scope; rewrite Hh, Hbody; reflexivity).
  destruct (Hsunk Hboth) as (Hclosed' & Hv & Hk). scope_in Hv. scope_in Hk.
  rewrite Hhandler, Hclosed'. split; [ reflexivity | split ].
  - intros y Hy. apply in_app_or in Hy. apply in_or_app.
    destruct Hy as [Hy | Hy];
      [ right; apply in_or_app; left; exact Hy | ].
    apply Hv, in_app_or in Hy.
    destruct Hy as [Hy | Hy]; [ left; exact Hy | right ].
    apply in_or_app. right. exact Hy.
  - intros j Hj. apply in_app_or in Hj. apply in_or_app.
    destruct Hj as [Hj | Hj].
    + right. apply in_without.
      split; [ apply in_or_app; left; exact Hj | ].
      intros [<- | []].
      rewrite (cont_free_b_free k handler Hhandler Hj) in Hunused.
      discriminate.
    + apply in_without in Hj. destruct Hj as [Hj Hout'].
      apply Hk, in_app_or in Hj.
      destruct Hj as [Hj | Hj]; [ left; exact Hj | right ].
      apply in_without in Hj. destruct Hj as [Hj Hout].
      apply in_without. split; [ | exact Hout ].
      apply in_or_app. right. apply in_without. split; assumption.
Qed.

Fixpoint sink_into_handler_scoped (k : continuation)
    (h : continuation_handler) (body : expr) {struct body} :
  ∀ sunk : expr,
    sink_into_handler k h body = Some sunk ->
    scoped (Let_cont_non_recursive k h body) sunk.
Proof.
  destruct body
    as [x kind d body | bindings body | k' [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    cbn [sink_into_handler]; intros sunk;
    try (intros Hsunk; discriminate Hsunk).
  - destruct (var_free_in_handler_b x h);
      [ intros Hsunk; discriminate Hsunk | ].
    destruct (sink_into_handler k h body) as [sunk' | ] eqn:Hbody;
      cbn [option_map]; intros Hsunk; [ | discriminate Hsunk ].
    injection Hsunk as <-.
    apply scoped_let_cont_past_let, sink_into_handler_scoped, Hbody.
  - destruct (sink_into_handler k h body) as [sunk' | ] eqn:Hbody;
      cbn [option_map]; intros Hsunk; [ | discriminate Hsunk ].
    injection Hsunk as <-.
    apply scoped_let_cont_past_let_static, sink_into_handler_scoped, Hbody.
  - match goal with
    | |- (if ?test then _ else _) = _ -> _ => destruct test eqn:Hinto
    end.
    + apply andb_true_iff in Hinto. destruct Hinto as [Hinto _].
      apply andb_true_iff in Hinto. destruct Hinto as [Hunused _].
      apply negb_true_iff in Hunused.
      destruct (sink_into_handler k h handler) as [sunk' | ] eqn:Hhandler.
      * intros Hsunk. injection Hsunk as <-.
        apply scoped_let_cont_into_handler;
          [ exact Hunused | apply sink_into_handler_scoped, Hhandler ].
      * destruct (applied_at_tail k h handler); intros Hsunk;
          [ | discriminate Hsunk ].
        injection Hsunk as <-.
        apply scoped_let_cont_into_handler;
          [ exact Hunused | apply scoped_refl ].
    + match goal with
      | |- (if ?test then _ else _) = _ -> _ =>
        destruct test eqn:Hpast; [ | intros Hsunk; discriminate Hsunk ]
      end.
      apply andb_true_iff in Hpast. destruct Hpast as [Hpast _].
      apply andb_true_iff in Hpast. destruct Hpast as [_ Hunused].
      apply negb_true_iff in Hunused.
      destruct (sink_into_handler k h body) as [sunk' | ] eqn:Hbody;
        cbn [option_map]; intros Hsunk; [ | discriminate Hsunk ].
      injection Hsunk as <-.
      apply scoped_let_cont_past_let_cont;
        [ exact Hunused | apply sink_into_handler_scoped, Hbody ].
Qed.

Fixpoint sink_let_conts_scoped (e : expr) : scoped e (sink_let_conts e).
Proof.
  destruct e
    as [x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    cbn [sink_let_conts]; try (scoped_under_binders sink_let_conts_scoped).
  cbv zeta.
  destruct
    (sink_into_handler k (Handler params metadata (sink_let_conts handler))
       (sink_let_conts body))
    as [sunk | ] eqn:Hsunk.
  - eapply scoped_trans;
      [ | exact (sink_into_handler_scoped _ _ _ _ Hsunk) ].
    scoped_under_binders sink_let_conts_scoped.
  - scoped_under_binders sink_let_conts_scoped.
Qed.

Theorem sink_let_conts_keeps_scope : sink_let_conts_keeps_scope_statement.
Proof. apply keeps_scope_intro, sink_let_conts_scoped. Qed.

(* An arm of a switch that goes where its continuation goes. *)

(* An arm as it was, or the application of the handler. *)
Lemma shortcut_arm_from (k : continuation) (target : apply_cont)
    (arm : Z * apply_cont) :
  snd (shortcut_arm k target arm) = snd arm
  ∨ snd (shortcut_arm k target arm) = target.
Proof.
  unfold shortcut_arm. destruct (ac_args (snd arm)); [ | left; reflexivity ].
  destruct
    (Pos.eqb (ac_continuation (snd arm)) k && no_trap_action (snd arm));
    [ right | left ]; reflexivity.
Qed.

Lemma shortcut_arms_names (f : apply_cont -> list positive) (k : continuation)
    (target : apply_cont) (arms : list (Z * apply_cont)) :
  incl (flat_map (fun arm => f (snd arm)) (map (shortcut_arm k target) arms))
    (f target ++ flat_map (fun arm => f (snd arm)) arms).
Proof.
  intros a Ha. apply in_flat_map in Ha. destruct Ha as (arm' & Harm' & Ha).
  apply in_map_iff in Harm'. destruct Harm' as (arm & <- & Harm).
  apply in_or_app.
  destruct (shortcut_arm_from k target arm) as [Hsame | Htarget].
  - right. apply in_flat_map. exists arm. rewrite <- Hsame.
    split; [ exact Harm | exact Ha ].
  - left. rewrite <- Htarget. exact Ha.
Qed.

Lemma shortcut_switch_scoped (k : continuation) (h : continuation_handler)
    (body : expr) :
  scoped (Let_cont_non_recursive k h body) (shortcut_switch k h body).
Proof.
  unfold shortcut_switch.
  destruct h as [[ | param params] metadata handler]; destruct handler;
    destruct body; try apply scoped_refl.
  destruct (hm_params_kinds metadata); [ | apply scoped_refl ].
  match goal with
  | |- context [Pos.eqb (ac_continuation ?target) k || ?exn || ?trap] =>
    destruct (Pos.eqb (ac_continuation target) k || exn || trap);
      [ apply scoped_refl | ]
  end.
  cbv zeta. intros _.
  match goal with
  | |- context [map (shortcut_arm k ?target) ?arms] =>
    pose proof
      (shortcut_arms_names free_variables_of_apply_cont k target arms) as Hv;
    pose proof (shortcut_arms_names apply_cont_continuations k target arms)
      as Hk;
    destruct (arms_apply k (map (shortcut_arm k target) arms)) eqn:Happly
  end;
    scope; (split; [ reflexivity | split ]).
  - intros x Hx. apply in_app_or in Hx. apply in_or_app.
    destruct Hx as [Hx | Hx]; [ left; exact Hx | ].
    apply in_app_or in Hx.
    destruct Hx as [Hx | Hx]; [ right; apply in_or_app; left; exact Hx | ].
    apply Hv, in_app_or in Hx.
    destruct Hx as [Hx | Hx];
      [ left | right; apply in_or_app; right; exact Hx ].
    apply in_without. split; [ exact Hx | intros [] ].
  - intros j Hj. apply in_app_or in Hj. apply in_or_app.
    destruct Hj as [Hj | Hj]; [ left; exact Hj | ].
    apply in_without in Hj. destruct Hj as [Hj Hout].
    apply Hk, in_app_or in Hj.
    destruct Hj as [Hj | Hj];
      [ left; exact Hj | right; apply in_without; split; assumption ].
  - intros x Hx. apply in_app_or in Hx. apply in_or_app.
    destruct Hx as [Hx | Hx]; [ right; apply in_or_app; left; exact Hx | ].
    apply Hv, in_app_or in Hx.
    destruct Hx as [Hx | Hx];
      [ left | right; apply in_or_app; right; exact Hx ].
    apply in_without. split; [ exact Hx | intros [] ].
  - intros j Hj. apply in_or_app.
    pose proof (arms_apply_none k _ Happly) as Hnone.
    assert (Hout : ~ In j [k]) by (intros [<- | []]; exact (Hnone Hj)).
    apply Hk, in_app_or in Hj.
    destruct Hj as [Hj | Hj];
      [ left; exact Hj | right; apply in_without; split; assumption ].
Qed.

Fixpoint shortcut_switches_scoped (e : expr) :
  scoped e (shortcut_switches e).
Proof.
  destruct e
    as [x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    cbn [shortcut_switches];
    try (scoped_under_binders shortcut_switches_scoped).
  eapply scoped_trans; [ | apply shortcut_switch_scoped ].
  scoped_under_binders shortcut_switches_scoped.
Qed.

Theorem shortcut_switches_keeps_scope :
  shortcut_switches_keeps_scope_statement.
Proof. apply keeps_scope_intro, shortcut_switches_scoped. Qed.

(* A rewrite taken into the handlers of recursive continuations. *)

Section Rewrite_rec_handlers.

Variable f : expr -> expr.

Hypothesis f_keeps_scope : keeps_scope f.

Fixpoint rewrite_rec_handlers_scoped (e : expr) :
  scoped e (rewrite_rec_handlers f e)
with rewrite_rec_handlers_in_handler_scoped (h : continuation_handler) :
  scoped_handler h (rewrite_rec_handlers_in_handler f h)
with rewrite_rec_handler_scoped (h : continuation_handler) :
  scoped_handler h (rewrite_rec_handler f h).
Proof.
  - destruct e
      as [x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [rewrite_rec_handlers rewrite_rec_handlers_in_handler
           rewrite_rec_handler].
    + apply scoped_let;
        [ apply incl_refl | apply rewrite_rec_handlers_scoped ].
    + apply scoped_let_static;
        [ apply scoped_bindings_refl | apply rewrite_rec_handlers_scoped ].
    + apply scoped_let_cont;
        [ apply rewrite_rec_handlers_in_handler_scoped
        | apply rewrite_rec_handlers_scoped ].
    + apply scoped_let_cont_recursive;
        [ | | apply rewrite_rec_handlers_scoped ].
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply rewrite_rec_handler_scoped | exact IH ].
    + apply scoped_refl.
    + apply scoped_refl.
    + apply scoped_refl.
    + apply scoped_refl.
  - destruct h as [params metadata handler].
    cbn [rewrite_rec_handlers rewrite_rec_handlers_in_handler
         rewrite_rec_handler].
    apply scoped_handler_intro, rewrite_rec_handlers_scoped.
  - destruct h as [params metadata handler].
    cbn [rewrite_rec_handlers rewrite_rec_handlers_in_handler
         rewrite_rec_handler].
    apply scoped_handler_intro.
    eapply scoped_trans;
      [ apply rewrite_rec_handlers_scoped
      | apply rewrite_code_body_scoped, f_keeps_scope ].
Qed.

End Rewrite_rec_handlers.

Theorem rewrite_rec_handlers_keeps_scope :
  rewrite_rec_handlers_keeps_scope_statement.
Proof.
  intros f Hf. apply keeps_scope_intro. intros e.
  exact (rewrite_rec_handlers_scoped f Hf e).
Qed.

(* Following aliases into the handlers of recursive continuations. *)

(* [scoped_under] for a handler and for a group of handlers. *)
Definition scoped_handler_under (names : list variable)
    (h h' : continuation_handler) : Prop :=
  handler_code_closed h = true ->
  handler_code_closed h' = true
  ∧ incl (free_variables_of_handler h') (free_variables_of_handler h ++ names)
  ∧ incl (free_continuations_of_handler h')
      (free_continuations_of_handler h).

Definition scoped_handlers_under (names : list variable)
    (handlers handlers' : list (continuation * continuation_handler))
    : Prop :=
  forallb (fun '(_, h) => handler_code_closed h) handlers = true ->
  forallb (fun '(_, h) => handler_code_closed h) handlers' = true
  ∧ incl (flat_map (fun '(_, h) => free_variables_of_handler h) handlers')
      (flat_map (fun '(_, h) => free_variables_of_handler h) handlers
       ++ names)
  ∧ incl
      (flat_map (fun '(_, h) => free_continuations_of_handler h) handlers')
      (flat_map (fun '(_, h) => free_continuations_of_handler h) handlers).

Lemma scoped_under_trans (names : list variable) (e e' e'' : expr) :
  scoped_under names e e' ->
  scoped_under names e' e'' ->
  scoped_under names e e''.
Proof.
  intros Hfirst Hsecond Hclosed.
  destruct (Hfirst Hclosed) as (Hclosed' & Hv & Hk).
  destruct (Hsecond Hclosed') as (Hclosed'' & Hv' & Hk').
  split; [ exact Hclosed'' | split; [ | eapply incl_tran; eassumption ] ].
  intros y Hy. apply Hv', in_app_or in Hy.
  destruct Hy as [Hy | Hy]; [ exact (Hv y Hy) | ].
  apply in_or_app. right. exact Hy.
Qed.

Lemma scoped_handler_under_intro (names : list variable)
    (params : list variable) (metadata : handler_metadata)
    (handler handler' : expr) :
  scoped_under names handler handler' ->
  scoped_handler_under names (Handler params metadata handler)
    (Handler params metadata handler').
Proof.
  intros Hhandler Hclosed. scope_in Hclosed. scope.
  destruct (Hhandler Hclosed) as (Hclosed' & Hv & Hk).
  split; [ exact Hclosed' | split; [ | exact Hk ] ].
  intros y Hy. apply in_without in Hy. destruct Hy as [Hy Hparams].
  apply Hv, in_app_or in Hy. apply in_or_app.
  destruct Hy as [Hy | Hy]; [ left | right; exact Hy ].
  apply in_without. split; assumption.
Qed.

Lemma scoped_handlers_under_nil (names : list variable) :
  scoped_handlers_under names [] [].
Proof.
  intros Hclosed.
  split; [ exact Hclosed | split; [ apply incl_appl | ]; apply incl_refl ].
Qed.

Lemma scoped_handlers_under_cons (names : list variable)
    (k k' : continuation) (h h' : continuation_handler)
    (handlers handlers' : list (continuation * continuation_handler)) :
  scoped_handler_under names h h' ->
  scoped_handlers_under names handlers handlers' ->
  scoped_handlers_under names ((k, h) :: handlers) ((k', h') :: handlers').
Proof.
  intros Hh Hhandlers Hclosed. cbn [forallb flat_map] in Hclosed |- *.
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hfirst Hrest].
  destruct (Hh Hfirst) as (Hfirst' & Hv & Hk).
  destruct (Hhandlers Hrest) as (Hrest' & Hv' & Hk').
  rewrite Hfirst', Hrest'.
  split; [ reflexivity | split; [ | apply incl_app_app; assumption ] ].
  apply incl_app_under; assumption.
Qed.

(* A recursive [Let_cont] whose handlers may change. *)
Lemma scoped_under_let_cont_recursive_handlers (names : list variable)
    (handlers handlers' : list (continuation * continuation_handler))
    (body body' : expr) :
  map fst handlers' = map fst handlers ->
  scoped_handlers_under names handlers handlers' ->
  scoped_under names body body' ->
  scoped_under names (Let_cont_recursive handlers body)
    (Let_cont_recursive handlers' body').
Proof.
  intros Hnames Hhandlers Hbody Hclosed. scope_in Hclosed. scope.
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hfirst Hrest].
  destruct (Hhandlers Hfirst) as (Hfirst' & Hv & Hk).
  destruct (Hbody Hrest) as (Hrest' & Hv' & Hk').
  rewrite Hfirst', Hrest'. split; [ reflexivity | split ].
  - apply incl_app_under; assumption.
  - rewrite Hnames. apply incl_without, incl_app_app; assumption.
Qed.

Fixpoint follow_aliases_in_loops_scoped_under (e : expr) :
  ∀ (names : list variable) (tenv : typing_env),
    tenv_within names tenv ->
    scoped_under names e (follow_aliases_in_loops tenv e)
with follow_aliases_in_loop_scoped_under (h : continuation_handler) :
  ∀ (names : list variable) (tenv : typing_env),
    tenv_within names tenv ->
    scoped_handler_under names h (follow_aliases_in_loop tenv h).
Proof.
  - destruct e
      as [x kind d body | bindings body | k [params metadata handler] body
         | handlers body | ap | ac | scrutinee arms | ];
      intros names tenv Htenv;
      cbn [follow_aliases_in_loops follow_aliases_in_loops_in_handler
           follow_aliases_in_loop].
    + apply scoped_under_let; [ apply incl_appl, incl_refl | ].
      apply follow_aliases_in_loops_scoped_under.
      eapply tenv_within_weaken;
        [ | apply typing_env_under_let_within, Htenv ].
      apply incl_tl, incl_refl.
    + apply scoped_under_let_static.
      apply follow_aliases_in_loops_scoped_under.
      eapply tenv_within_weaken; [ | exact Htenv ]. apply incl_appl, incl_refl.
    + apply scoped_under_let_cont;
        apply follow_aliases_in_loops_scoped_under;
        [ apply drop_vars_within, Htenv | exact Htenv ].
    + apply scoped_under_let_cont_recursive_handlers.
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_under_nil | ].
        apply scoped_handlers_under_cons;
          [ apply follow_aliases_in_loop_scoped_under, Htenv | exact IH ].
      * apply follow_aliases_in_loops_scoped_under, Htenv.
    + apply scoped_under_refl.
    + apply scoped_under_refl.
    + apply scoped_under_refl.
    + apply scoped_under_refl.
  - destruct h as [params metadata handler]. intros names tenv Htenv.
    cbn [follow_aliases_in_loops follow_aliases_in_loops_in_handler
         follow_aliases_in_loop].
    apply scoped_handler_under_intro.
    eapply scoped_under_trans;
      [ apply follow_aliases_in_loops_scoped_under, drop_vars_within, Htenv
      | ].
    unfold rewrite_code_body. cbv zeta.
    match goal with
    | |- context [Bool.eqb ?b ?b'] => destruct (Bool.eqb b b')
    end;
      [ apply follow_aliases_scoped_under, drop_vars_within, Htenv
      | apply scoped_under_refl ].
Qed.

Lemma follow_aliases_in_loops_scoped (e : expr) :
  scoped e (follow_aliases_in_loops [] e).
Proof.
  apply scoped_under_none, follow_aliases_in_loops_scoped_under.
  intros entry [].
Qed.

Theorem follow_aliases_in_loops_keeps_scope :
  follow_aliases_in_loops_keeps_scope_statement.
Proof. apply keeps_scope_intro, follow_aliases_in_loops_scoped. Qed.

(* Removing the parameters that a handler does not use. *)

Lemma keep_incl {A : Type} (mask : list bool) :
  ∀ l : list A, incl (keep mask l) l.
Proof.
  induction mask as [ | used mask IH]; intros [ | a l]; cbn [keep].
  - intros x [].
  - intros x [].
  - destruct used; intros x [].
  - destruct used.
    + intros x [<- | Hx]; [ left; reflexivity | right; exact (IH l x Hx) ].
    + intros x Hx. right. exact (IH l x Hx).
Qed.

Lemma keep_all_or_incl {A : Type} (mask : option (list bool)) (l : list A) :
  incl (keep_all_or mask l) l.
Proof.
  destruct mask as [mask | ]; cbn [keep_all_or];
    [ apply keep_incl | apply incl_refl ].
Qed.

Lemma drop_args_free (known : masks) (ac : apply_cont) :
  incl (free_variables_of_apply_cont (drop_args known ac))
    (free_variables_of_apply_cont ac).
Proof.
  unfold free_variables_of_apply_cont, drop_args, free_variables_of_simples.
  cbn [ac_args]. intros x Hx. apply in_flat_map in Hx.
  destruct Hx as (s & Hs & Hx). apply in_flat_map. exists s.
  split; [ exact (keep_all_or_incl _ _ s Hs) | exact Hx ].
Qed.

(* A parameter that the test says is used is kept. *)
Lemma keep_used (used : variable -> bool) (x : variable)
    (params : list variable) :
  In x params -> used x = true -> In x (keep (map used params) params).
Proof.
  induction params as [ | param params IH]; cbn [map keep]; [ intros [] | ].
  intros [-> | Hx] Hused.
  - rewrite Hused. left. reflexivity.
  - destruct (used param); [ right | ]; exact (IH Hx Hused).
Qed.

Lemma used_params_kept (is_exn_handler : bool) (params : list variable)
    (handler : expr) (x : variable) :
  In x params ->
  var_free_b x handler = true ->
  In x (keep_all_or (used_params is_exn_handler params handler) params).
Proof.
  intros Hx Hused. unfold used_params. cbv zeta.
  pose proof
    (keep_used (fun param => var_free_b param handler) x params Hx Hused)
    as Hkept.
  destruct is_exn_handler;
    [ destruct params as [ | param params]; cbn [map] | ];
    match goal with
    | |- context [forallb ?test ?mask] => destruct (forallb test mask)
    end;
    cbn [keep_all_or keep]; try exact Hx; try exact Hkept.
  destruct Hx as [<- | Hx]; [ left; reflexivity | right ].
  exact (keep_used (fun param => var_free_b param handler) x params Hx Hused).
Qed.

(* A handler less the parameters that it does not use, as the test
   says of the handler before or of the handler after. *)
Lemma scoped_handler_unused_params (is_exn_handler : bool)
    (params : list variable) (metadata metadata' : handler_metadata)
    (handler handler' tested : expr) (mask : option (list bool)) :
  mask = None ∨ mask = used_params is_exn_handler params tested ->
  tested = handler ∨ tested = handler' ->
  scoped handler handler' ->
  scoped_handler (Handler params metadata handler)
    (Handler (keep_all_or mask params) metadata' handler').
Proof.
  intros Hmask Htested Hhandler Hclosed. scope_in Hclosed. scope.
  destruct (Hhandler Hclosed) as (Hclosed' & Hv & Hk).
  split; [ exact Hclosed' | split; [ | exact Hk ] ].
  intros y Hy. apply in_without in Hy. destruct Hy as [Hy Hkept].
  apply in_without. split; [ apply Hv, Hy | ].
  intros Hparam. apply Hkept.
  destruct Hmask as [-> | ->]; [ exact Hparam | ].
  apply used_params_kept; [ exact Hparam | ].
  destruct Htested as [-> | ->]; apply var_free_b_free;
    solve [ assumption | apply Hv, Hy ].
Qed.

Fixpoint drop_params_scoped (e : expr) :
  ∀ known : masks, scoped e (drop_params known e)
with drop_params_in_loop_scoped (h : continuation_handler) :
  ∀ (known : masks) (k : continuation) (whole : expr),
    scoped_handler h
      (drop_params_in_loop known (used_params_in_loop k h whole) h).
Proof.
  - destruct e
      as [x kind d body | bindings body | k [params metadata handler] body
         | handlers body | ap | ac | scrutinee arms | ];
      intros known; cbn [drop_params drop_params_in_loop]; cbv zeta.
    + apply scoped_let; [ apply incl_refl | apply drop_params_scoped ].
    + apply scoped_let_static;
        [ apply scoped_bindings_refl | apply drop_params_scoped ].
    + apply scoped_let_cont; [ | apply drop_params_scoped ].
      apply
        (scoped_handler_unused_params (hm_is_exn_handler metadata) _ _ _ _ _
           (drop_params known handler));
        [ destruct (returned_to k body); [ left | right ]; reflexivity
        | right; reflexivity | apply drop_params_scoped ].
    + apply scoped_let_cont_recursive; [ | | apply drop_params_scoped ].
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * set (known' := _ ++ known). clearbody known'.
        set (whole := Let_cont_recursive handlers body). clearbody whole.
        induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply drop_params_in_loop_scoped | exact IH ].
    + apply scoped_refl.
    + intros _. scope.
      split; [ reflexivity | split; [ apply drop_args_free | ] ].
      apply incl_refl.
    + intros _. scope. split; [ reflexivity | split ].
      * apply incl_app_app; [ apply incl_refl | ].
        intros x Hx. apply in_flat_map in Hx.
        destruct Hx as (arm' & Harm' & Hx). apply in_map_iff in Harm'.
        destruct Harm' as (arm & <- & Harm). apply in_flat_map. exists arm.
        split; [ exact Harm | exact (drop_args_free known (snd arm) x Hx) ].
      * rewrite
          (flat_map_map_same (fun arm => apply_cont_continuations (snd arm))
             (fun arm => apply_cont_continuations (snd arm)));
          [ apply incl_refl | intros arm; reflexivity ].
    + apply scoped_refl.
  - destruct h as [params metadata handler]. intros known k whole.
    unfold used_params_in_loop. cbn [drop_params drop_params_in_loop].
    apply
      (scoped_handler_unused_params (hm_is_exn_handler metadata) _ _ _ _ _
         handler);
      [ destruct (returned_to k whole); [ left | right ]; reflexivity
      | left; reflexivity | apply drop_params_scoped ].
Qed.

Theorem drop_unused_params_keeps_scope :
  drop_unused_params_keeps_scope_statement.
Proof.
  apply keeps_scope_intro. intros e. unfold drop_unused_params.
  apply drop_params_scoped.
Qed.

(* Loopify. *)

Lemma without_nil_incl (bound names : list positive) :
  without bound names = [] -> incl names bound.
Proof.
  intros Hnone a Ha. destruct (among a bound) eqn:Hamong;
    [ apply among_In; exact Hamong | ].
  assert (Hin : In a (without bound names)).
  { apply in_without. split; [ exact Ha | ].
    intros Hbound. apply among_In in Hbound. congruence. }
  rewrite Hnone in Hin. destruct Hin.
Qed.

Lemma free_variables_of_vars (xs : list variable) :
  free_variables_of_simples (map Var xs) = xs.
Proof.
  unfold free_variables_of_simples.
  induction xs as [ | x xs IH]; cbn [map flat_map free_variables_of_simple];
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

(* The body of code with its self tail calls made jumps: its code is
   closed as that of the body is, its free variables are free in the
   body, and its free continuations are free in the body or the name of
   the loop. *)
Fixpoint loop_calls_scope (my_closure : variable) (a : arity)
    (ret exn self : continuation) (e : expr) :
  code_closed (loop_calls my_closure a ret exn self e) = code_closed e
  ∧ incl (free_variables_of_expr (loop_calls my_closure a ret exn self e))
      (free_variables_of_expr e)
  ∧ incl (free_continuations_of_expr (loop_calls my_closure a ret exn self e))
      (self :: free_continuations_of_expr e)
with loop_calls_in_handler_scope (my_closure : variable)
    (a : arity) (ret exn self : continuation)
    (h : continuation_handler) :
  handler_code_closed (loop_calls_in_handler my_closure a ret exn self h)
  = handler_code_closed h
  ∧ incl
      (free_variables_of_handler
         (loop_calls_in_handler my_closure a ret exn self h))
      (free_variables_of_handler h)
  ∧ incl
      (free_continuations_of_handler
         (loop_calls_in_handler my_closure a ret exn self h))
      (self :: free_continuations_of_handler h).
Proof.
  - destruct e
      as [x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      cbn [loop_calls loop_calls_in_handler].
    + destruct (loop_calls_scope my_closure a ret exn self body)
        as (Hc & Hv & Hk).
      scope. split; [ exact Hc | split; [ | exact Hk ] ].
      apply incl_app_app; [ apply incl_refl | apply incl_without, Hv ].
    + destruct (loop_calls_scope my_closure a ret exn self body)
        as (Hc & Hv & Hk).
      scope. rewrite Hc. split; [ reflexivity | split ].
      * apply incl_app_app; [ apply incl_refl | exact Hv ].
      * intros j Hj. apply in_app_or in Hj.
        destruct Hj as [Hj | Hj]; [ right; apply in_or_app; left; exact Hj | ].
        destruct (Hk j Hj) as [<- | Hj'];
          [ left; reflexivity | right; apply in_or_app; right; exact Hj' ].
    + destruct (loop_calls_in_handler_scope my_closure a ret exn self h)
        as (Hc & Hv & Hk).
      destruct (loop_calls_scope my_closure a ret exn self body)
        as (Hc' & Hv' & Hk').
      scope. rewrite Hc, Hc'. split; [ reflexivity | split ].
      * apply incl_app_app; assumption.
      * intros j Hj. apply in_app_or in Hj. destruct Hj as [Hj | Hj].
        -- destruct (Hk j Hj) as [<- | Hj'];
             [ left; reflexivity | right; apply in_or_app; left; exact Hj' ].
        -- apply in_without in Hj. destruct Hj as [Hj Hout].
           destruct (Hk' j Hj) as [<- | Hj']; [ left; reflexivity | right ].
           apply in_or_app. right. apply in_without. split; assumption.
    + destruct (loop_calls_scope my_closure a ret exn self body)
        as (Hc' & Hv' & Hk').
      assert (Hgroup :
        map fst
          (map
             (fun '(k, h) =>
                (k, loop_calls_in_handler my_closure a ret exn self h))
             handlers)
        = map fst handlers
        ∧ forallb (fun '(_, h) => handler_code_closed h)
            (map
               (fun '(k, h) =>
                  (k, loop_calls_in_handler my_closure a ret exn self h))
               handlers)
          = forallb (fun '(_, h) => handler_code_closed h) handlers
        ∧ incl
            (flat_map (fun '(_, h) => free_variables_of_handler h)
               (map
                  (fun '(k, h) =>
                     (k, loop_calls_in_handler my_closure a ret exn self h))
                  handlers))
            (flat_map (fun '(_, h) => free_variables_of_handler h) handlers)
        ∧ incl
            (flat_map (fun '(_, h) => free_continuations_of_handler h)
               (map
                  (fun '(k, h) =>
                     (k, loop_calls_in_handler my_closure a ret exn self h))
                  handlers))
            (self
             :: flat_map (fun '(_, h) => free_continuations_of_handler h)
                  handlers)).
      { induction handlers as [ | [k h] handlers IH];
          cbn [map fst forallb flat_map].
        - split; [ reflexivity | split; [ reflexivity | split ] ];
            intros j [].
        - destruct IH as (Hnames & Hc & Hv & Hk).
          destruct (loop_calls_in_handler_scope my_closure a ret exn self h)
            as (Hc0 & Hv0 & Hk0).
          rewrite Hnames, Hc, Hc0.
          split; [ reflexivity | split; [ reflexivity | split ] ].
          + apply incl_app_app; assumption.
          + intros j Hj. apply in_app_or in Hj. destruct Hj as [Hj | Hj].
            * destruct (Hk0 j Hj) as [<- | Hj'];
                [ left; reflexivity
                | right; apply in_or_app; left; exact Hj' ].
            * destruct (Hk j Hj) as [<- | Hj'];
                [ left; reflexivity
                | right; apply in_or_app; right; exact Hj' ]. }
      destruct Hgroup as (Hnames & Hc & Hv & Hk).
      scope. rewrite Hnames, Hc, Hc'. split; [ reflexivity | split ].
      * apply incl_app_app; assumption.
      * intros j Hj. apply in_without in Hj. destruct Hj as [Hj Hout].
        apply in_app_or in Hj. destruct Hj as [Hj | Hj].
        -- destruct (Hk j Hj) as [<- | Hj']; [ left; reflexivity | right ].
           apply in_without.
           split; [ apply in_or_app; left; exact Hj' | exact Hout ].
        -- destruct (Hk' j Hj) as [<- | Hj']; [ left; reflexivity | right ].
           apply in_without.
           split; [ apply in_or_app; right; exact Hj' | exact Hout ].
    + destruct (is_self_tail_call my_closure a ret exn ap).
      * scope. split; [ reflexivity | split ].
        -- unfold free_variables_of_apply_cont, free_variables_of_apply.
           cbn [ac_args]. apply incl_appr, incl_appl, incl_refl.
        -- cbn [apply_cont_continuations ac_continuation ac_trap_action].
           intros j [<- | []]. left. reflexivity.
      * split; [ reflexivity | split; [ apply incl_refl | ] ].
        apply incl_tl, incl_refl.
    + split; [ reflexivity | split; [ apply incl_refl | ] ].
      apply incl_tl, incl_refl.
    + split; [ reflexivity | split; [ apply incl_refl | ] ].
      apply incl_tl, incl_refl.
    + split; [ reflexivity | split; [ apply incl_refl | ] ].
      apply incl_tl, incl_refl.
  - destruct h as [params metadata handler].
    cbn [loop_calls loop_calls_in_handler].
    destruct (loop_calls_scope my_closure a ret exn self handler)
      as (Hc & Hv & Hk).
    scope. split; [ exact Hc | split; [ apply incl_without, Hv | exact Hk ] ].
Qed.

(* Code whose body is made the handler of a loop that is entered with
   the parameters. *)
Lemma scoped_code_looped (params : list variable) (my_closure : variable)
    (ret exn self : continuation) (metadata : code_metadata)
    (loop_metadata : handler_metadata) (body looped : expr) :
  code_closed looped = code_closed body ->
  incl (free_variables_of_expr looped) (free_variables_of_expr body) ->
  incl (free_continuations_of_expr looped)
    (self :: free_continuations_of_expr body) ->
  scoped_code (Code params my_closure ret exn metadata body)
    (Code params my_closure ret exn metadata
       (Let_cont_recursive [(self, Handler params loop_metadata looped)]
          (Apply_cont (Apply_cont_expr self (map Var params) None)))).
Proof.
  intros Hc Hv Hk Hclosed. scope_in Hclosed.
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hclosed Hbody].
  apply andb_true_iff in Hclosed. destruct Hclosed as [Hvars Hconts].
  apply is_empty_nil, without_nil_incl in Hvars.
  apply is_empty_nil, without_nil_incl in Hconts.
  scope. cbn [forallb flat_map map fst]. scope.
  cbn [apply_cont_continuations ac_continuation ac_trap_action].
  unfold free_variables_of_apply_cont. cbn [ac_args].
  rewrite free_variables_of_vars, Hc, Hbody, !app_nil_r.
  apply andb_true_iff. split; [ apply andb_true_iff; split | reflexivity ].
  - apply (incl_is_empty _ []); [ | reflexivity ].
    intros y Hy. apply in_without in Hy. destruct Hy as [Hy Hbound].
    destruct Hbound. apply in_app_or in Hy. destruct Hy as [Hy | Hy].
    + apply in_without in Hy. apply Hvars, Hv, (proj1 Hy).
    + right. exact Hy.
  - apply (incl_is_empty _ []); [ | reflexivity ].
    intros j Hj. apply in_without in Hj. destruct Hj as [Hj Hbound].
    destruct Hbound. apply in_without in Hj. destruct Hj as [Hj Hself].
    apply in_app_or in Hj.
    destruct Hj as [Hj | [<- | []]];
      [ | destruct Hself; left; reflexivity ].
    destruct (Hk j Hj) as [<- | Hj'];
      [ destruct Hself; left; reflexivity | exact (Hconts j Hj') ].
Qed.

Lemma loopify_code_scoped (self : continuation) (c : code) :
  scoped_code c (loopify_code self c).
Proof.
  unfold loopify_code.
  destruct (loopable self c); [ | intros Hclosed; exact Hclosed ].
  destruct c as [params my_closure ret exn metadata body].
  unfold looped_code, loop_handler.
  cbn [code_params code_my_closure code_return_continuation
       code_exn_continuation code_body].
  destruct
    (loop_calls_scope my_closure (cm_params_arity metadata) ret exn self
       body)
    as (Hc & Hv & Hk).
  apply scoped_code_looped; assumption.
Qed.

Lemma loopify_bindings_scoped (G : loopified)
    (bindings : list static_binding) :
  scoped_bindings bindings (map (loopify_binding G) bindings).
Proof.
  induction bindings as [ | binding bindings IH]; cbn [map];
    [ apply scoped_bindings_nil | ].
  destruct binding as [id c | id | sym const]; cbn [loopify_binding];
    [ | apply scoped_bindings_cons_same, IH
    | apply scoped_bindings_cons_same, IH ].
  destruct (lookup id G) as [self | ];
    [ | apply scoped_bindings_cons_same, IH ].
  apply scoped_bindings_cons_code; [ apply loopify_code_scoped | exact IH ].
Qed.

Fixpoint loopify_unit_scoped (G : loopified) (e : expr) :
  scoped e (loopify_unit G e).
Proof.
  destruct e
    as [x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    cbn [loopify_unit];
    first
      [ apply scoped_let_static;
        [ apply loopify_bindings_scoped | apply loopify_unit_scoped ]
      | scoped_under_binders (loopify_unit_scoped G) ].
Qed.

Theorem loopify_unit_keeps_scope : loopify_unit_keeps_scope_statement.
Proof.
  intros G. apply keeps_scope_intro. intros e. apply loopify_unit_scoped.
Qed.
