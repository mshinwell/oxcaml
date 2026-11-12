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

(* Proofs of the statements of FlambdaValidateScopeSpec.v. Nothing here
   needs review. A round is a chain of rewrites, each of which keeps
   scope by a lemma of FlambdaKeepsScopeProofs.v or of
   FlambdaLoopsScopeProofs.v. The chain is taken apart by a tactic that
   finds those lemmas among its hints, so a rewrite that is added to a
   round, or moved in it, needs its lemma among the hints and nothing
   else. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaBindersSpec
  FlambdaBindersProofs FlambdaNominalSpec FlambdaNominalProofs
  FlambdaAlphaSpec FlambdaAlphaProofs FlambdaEquivarianceProofs
  FlambdaFreeNamesSpec FlambdaFreeNamesProofs FlambdaApplySpec
  FlambdaInlineSiblingsSpec FlambdaGuardScopeSpec
  FlambdaNormaliseSpec FlambdaNormaliseProofs FlambdaBlockLoadSpec
  FlambdaCseSpec FlambdaIdentitiesSpec FlambdaRenameApartSpec
  FlambdaUnboxSpec FlambdaUnusedContsSpec FlambdaForwardSpec
  FlambdaLoopAliasesSpec FlambdaLoopLetsSpec FlambdaParamAliasesSpec
  FlambdaRecHandlersSpec FlambdaShortcutSpec FlambdaSinkContsSpec
  FlambdaUnusedParamsSpec FlambdaValidateSpec
  FlambdaValidatorEquivarianceSpec FlambdaScopedProofs
  FlambdaKeepsScopeProofs FlambdaLoopsScopeSpec FlambdaLoopsScopeProofs
  FlambdaValidateScopeSpec.
From OxCamlFlambda2Types Require Import FlambdaTypesSpec FlambdaAliasesSpec.
Import ListNotations.

Lemma rename_apart_scoped (e : expr) : scoped e (rename_apart e).
Proof. apply keeps_scope_scoped, rename_apart_keeps_scope. Qed.

Lemma rename_apart_avoiding_scoped (avoid : list continuation) (e : expr) :
  scoped e (rename_apart_avoiding avoid e).
Proof. apply keeps_scope_scoped, rename_apart_avoiding_keeps_scope. Qed.

Lemma drop_unused_params_scoped (e : expr) : scoped e (drop_unused_params e).
Proof. apply keeps_scope_scoped, drop_unused_params_keeps_scope. Qed.

(* The lemmas that say of a rewrite that its result keeps the scope of
   the term. A rewrite that takes another asks that the other keeps
   scope, which [keeps_scope_intro] makes of a lemma of this form. The
   hints go to the files that import this one, with the tactic. *)
Create HintDb scoped.

#[export] Hint Resolve keeps_scope_intro rename_apart_scoped
  rename_apart_avoiding_scoped
  fold_constants_scoped collapse_switches_scoped remove_unused_conts_scoped
  remove_unused_lets_scoped remove_unused_defined_lets_scoped
  apply_identities_scoped inline_tail_conts_scoped thread_switches_scoped
  drop_deleted_code_scoped merge_statics_scoped rewrite_code_scoped
  load_known_blocks_scoped unbox_known_numbers_scoped
  share_known_primitives_scoped follow_aliases_scoped sink_let_conts_scoped
  shortcut_switches_scoped follow_aliases_in_loops_scoped
  drop_unused_params_scoped rewrite_rec_handlers_scoped
  bind_aliased_params_scoped forward_applications_scoped
  remove_unused_defined_lets_in_loops_scoped
  : scoped.

(* A chain of rewrites, taken apart from the outside. *)
Ltac scoped_chain :=
  repeat
    first
      [ apply scoped_refl
      | eapply scoped_trans; [ | solve [ eauto with scoped ] ] ].

Lemma normalise_expr_before_scoped (e : expr) :
  scoped e (normalise_expr_before e).
Proof. unfold normalise_expr_before. cbv zeta. scoped_chain. Qed.

#[export] Hint Resolve normalise_expr_before_scoped : scoped.

Theorem normalise_expr_before_keeps_scope :
  normalise_expr_before_keeps_scope_statement.
Proof. apply keeps_scope_intro, normalise_expr_before_scoped. Qed.

Lemma normalise_code_before_scoped (e : expr) :
  scoped e (normalise_code_before e).
Proof. unfold normalise_code_before. scoped_chain. Qed.

#[export] Hint Resolve normalise_code_before_scoped : scoped.

Theorem normalise_code_before_keeps_scope :
  normalise_code_before_keeps_scope_statement.
Proof. apply keeps_scope_intro, normalise_code_before_scoped. Qed.

Lemma normalise_expr_params_scoped (e : expr) :
  scoped e (normalise_expr_params e).
Proof. unfold normalise_expr_params. cbv zeta. scoped_chain. Qed.

#[export] Hint Resolve normalise_expr_params_scoped : scoped.

Theorem normalise_expr_params_keeps_scope :
  normalise_expr_params_keeps_scope_statement.
Proof. apply keeps_scope_intro, normalise_expr_params_scoped. Qed.

Lemma normalise_code_params_scoped (e : expr) :
  scoped e (normalise_code_params e).
Proof. unfold normalise_code_params. scoped_chain. Qed.

#[export] Hint Resolve normalise_code_params_scoped : scoped.

Theorem normalise_code_params_keeps_scope :
  normalise_code_params_keeps_scope_statement.
Proof. apply keeps_scope_intro, normalise_code_params_scoped. Qed.

Lemma normalise_params_round_scoped (e : expr) :
  scoped e (normalise_params_round e).
Proof. unfold normalise_params_round. scoped_chain. Qed.

#[export] Hint Resolve normalise_params_round_scoped : scoped.

Theorem normalise_params_round_keeps_scope :
  normalise_params_round_keeps_scope_statement.
Proof. apply keeps_scope_intro, normalise_params_round_scoped. Qed.

(* ======================================================================== *)
(* A round of the term before                                               *)
(* ======================================================================== *)

(* Inlining the calls of known code. *)

(* The conjuncts of the tests among the hypotheses, each a hypothesis
   of its own. *)
Ltac split_tests :=
  repeat
    match goal with
    | H : _ && _ = true |- _ =>
      let H' := fresh "Htest" in
      apply andb_true_iff in H; destruct H as [H H']
    end.

(* The body of code in place of a call of it keeps the scope of the
   call: the test says that the free variables and continuations of the
   body are bound by the code. *)
Lemma inline_apply_scoped (kept : list code_id)
    (known : list (code_id * code)) (ap : apply_expr) :
  scoped (Apply ap) (inline_apply kept known ap).
Proof.
  unfold inline_apply.
  destruct (ap_call_kind ap) as [called | ]; [ | apply scoped_refl ].
  destruct (lookup called known) as [c | ]; [ | apply scoped_refl ].
  match goal with
  | |- context [if ?test then _ else _] =>
    destruct test eqn:Hinline; [ | apply scoped_refl ]
  end.
  unfold inlinable_b in Hinline. split_tests.
  match goal with
  | H : expr_in_scope _ _ _ = true |- _ => rename H into Hscope
  end.
  match goal with
  | H : negb (binds_statics _) = true |- _ => rename H into Hstatics
  end.
  match goal with
  | H : Nat.eqb (length (code_params _)) _ = true |- _ =>
    rename H into Hlength
  end.
  match goal with
  | H : negb (Pos.eqb (code_return_continuation _) _) = true |- _ =>
    rename H into Hcode
  end.
  match goal with
  | H : negb (Pos.eqb (ap_continuation _) _) = true |- _ =>
    rename H into Hcall
  end.
  apply negb_true_iff in Hstatics, Hcall, Hcode.
  apply Pos.eqb_neq in Hcall, Hcode. apply Nat.eqb_eq in Hlength.
  pose proof (binds_statics_code_closed (code_body c) Hstatics) as Hclosed.
  rewrite (expr_in_scope_agrees _ _ _ Hclosed) in Hscope.
  apply andb_true_iff in Hscope. destruct Hscope as [Hscope_v Hscope_k].
  destruct
    (inline_renaming_spec (code_return_continuation c)
       (code_exn_continuation c) (ap_continuation ap)
       (ap_exn_continuation ap) Hcode Hcall)
    as (Hfixes & Hret & Hexn).
  set (r :=
    inline_renaming (code_return_continuation c) (code_exn_continuation c)
      (ap_continuation ap) (ap_exn_continuation ap))
    in *.
  intros _. unfold inlined_body. scope.
  rewrite let_params_code_closed, code_closed_renamed.
  split; [ exact Hclosed | split ].
  - intros x Hx. cbn [free_variables_of_named] in Hx.
    unfold free_variables_of_apply. apply in_or_app.
    apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [ left; exact Hx | ].
    right. apply in_or_app. left.
    apply in_without in Hx. destruct Hx as [Hx Hclosure].
    apply let_params_free_variables in Hx; [ | exact Hlength ].
    destruct Hx as [Hx | [Hx Hparams]]; [ exact Hx | ].
    rewrite free_variables_of_expr_renamed in Hx. apply in_map_iff in Hx.
    destruct Hx as (y & Hy & Hin). rewrite Hfixes in Hy. subst y.
    destruct (all_among_In _ _ x Hscope_v Hin) as [Heq | Hin'];
      [ destruct Hclosure; left; exact Heq | contradiction ].
  - intros k Hk. rewrite let_params_free_continuations in Hk.
    rewrite free_continuations_of_expr_renamed in Hk. apply in_map_iff in Hk.
    destruct Hk as (j & Hj & Hin).
    destruct (all_among_In _ _ j Hscope_k Hin) as [Heq | [Heq | []]];
      subst j; [ left | right; left ]; congruence.
Qed.

Fixpoint inline_calls_scoped (e : expr) :
  ∀ (kept : list code_id) (known : list (code_id * code)),
    scoped e (inline_calls kept known e)
with inline_calls_in_handler_scoped (h : continuation_handler) :
  ∀ (kept : list code_id) (known : list (code_id * code)),
    scoped_handler h (inline_calls_in_handler kept known h)
with inline_calls_in_code_scoped (c : code) :
  ∀ (kept : list code_id) (known : list (code_id * code)),
    scoped_code c (inline_calls_in_code kept known c).
Proof.
  - destruct e
      as [x kind d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      intros kept known;
      cbn [inline_calls inline_calls_in_handler inline_calls_in_binding
           inline_calls_in_code].
    + apply scoped_let; [ apply incl_refl | apply inline_calls_scoped ].
    + apply scoped_let_static; [ | apply inline_calls_scoped ].
      induction bindings as [ | binding bindings IH]; cbn [map];
        [ apply scoped_bindings_nil | ].
      destruct binding as [id c | id | sym const];
        cbn [inline_calls inline_calls_in_handler inline_calls_in_binding
             inline_calls_in_code];
        [ apply scoped_bindings_cons_code;
          [ apply inline_calls_in_code_scoped | exact IH ]
        | apply scoped_bindings_cons_same, IH
        | apply scoped_bindings_cons_same, IH ].
    + apply scoped_let_cont;
        [ apply inline_calls_in_handler_scoped | apply inline_calls_scoped ].
    + apply scoped_let_cont_recursive; [ | | apply inline_calls_scoped ].
      * rewrite map_map. apply map_ext. intros [k h]. reflexivity.
      * induction handlers as [ | [k h] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply inline_calls_in_handler_scoped | exact IH ].
    + apply inline_apply_scoped.
    + apply scoped_refl.
    + apply scoped_refl.
    + apply scoped_refl.
  - destruct h as [params metadata handler]. intros kept known.
    cbn [inline_calls inline_calls_in_handler inline_calls_in_binding
         inline_calls_in_code].
    apply scoped_handler_intro, inline_calls_scoped.
  - destruct c as [params my_closure ret exn metadata body].
    intros kept known.
    cbn [inline_calls inline_calls_in_handler inline_calls_in_binding
         inline_calls_in_code].
    apply scoped_code_intro, inline_calls_scoped.
Qed.

Theorem inline_calls_keeps_scope : inline_calls_keeps_scope_statement.
Proof.
  intros kept. apply keeps_scope_intro. intros e. apply inline_calls_scoped.
Qed.

(* Inlining the calls of the other code of a group. *)

(* The bindings of a group after others that are the same. *)
Lemma scoped_bindings_app_same (done : list static_binding) :
  ∀ bindings bindings' : list static_binding,
    scoped_bindings bindings bindings' ->
    scoped_bindings (done ++ bindings) (done ++ bindings').
Proof.
  induction done as [ | binding done IH]; intros bindings bindings' Hscoped;
    [ exact Hscoped | ].
  cbn [app]. apply scoped_bindings_cons_same, IH, Hscoped.
Qed.

(* One binding with calls inlined in the body of its code. *)
Lemma inline_calls_in_binding_scoped (kept : list code_id)
    (known : list (code_id * code)) (binding : static_binding)
    (bindings : list static_binding) :
  scoped_bindings (binding :: bindings)
    (inline_calls_in_binding kept known binding :: bindings).
Proof.
  destruct binding as [id c | id | sym const]; cbn [inline_calls_in_binding];
    [ | apply scoped_bindings_refl | apply scoped_bindings_refl ].
  apply scoped_bindings_cons_code;
    [ apply inline_calls_in_code_scoped | apply scoped_bindings_refl ].
Qed.

Lemma inline_in_group_scoped (kept : list code_id)
    (todo : list static_binding) :
  ∀ done : list static_binding,
    scoped_bindings (done ++ todo) (inline_in_group kept done todo).
Proof.
  induction todo as [ | binding todo IH]; intros done; cbn [inline_in_group].
  - rewrite app_nil_r. apply scoped_bindings_refl.
  - eapply scoped_bindings_trans; [ | apply IH ].
    rewrite <- app_assoc. cbn [app].
    apply scoped_bindings_app_same, inline_calls_in_binding_scoped.
Qed.

Fixpoint inline_sibling_calls_scoped (kept : list code_id) (e : expr) :
  scoped e (inline_sibling_calls kept e).
Proof.
  destruct e
    as [x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    cbn [inline_sibling_calls]; try apply scoped_refl.
  - apply scoped_let; [ apply incl_refl | apply inline_sibling_calls_scoped ].
  - apply scoped_let_static; [ | apply inline_sibling_calls_scoped ].
    exact (inline_in_group_scoped kept bindings []).
  - apply scoped_let_cont; [ | apply inline_sibling_calls_scoped ].
    apply scoped_handler_intro, inline_sibling_calls_scoped.
  - apply scoped_let_cont_recursive;
      [ reflexivity | apply scoped_handlers_refl
      | apply inline_sibling_calls_scoped ].
Qed.

Theorem inline_sibling_calls_keeps_scope :
  inline_sibling_calls_keeps_scope_statement.
Proof.
  intros kept. apply keeps_scope_intro. intros e.
  apply inline_sibling_calls_scoped.
Qed.

#[export] Hint Resolve inline_calls_scoped inline_sibling_calls_scoped
  : scoped.

(* The round once the calls are inlined, and the round as a whole. *)

Lemma normalise_before_inlined_scoped (e : expr) :
  scoped e (normalise_before_inlined e).
Proof. unfold normalise_before_inlined. scoped_chain. Qed.

#[export] Hint Resolve normalise_before_inlined_scoped : scoped.

Theorem normalise_before_inlined_keeps_scope :
  normalise_before_inlined_keeps_scope_statement.
Proof. apply keeps_scope_intro, normalise_before_inlined_scoped. Qed.

Lemma normalise_before_round_scoped (kept : list code_id) (e : expr) :
  scoped e (normalise_before_round kept e).
Proof. unfold normalise_before_round. scoped_chain. Qed.

#[export] Hint Resolve normalise_before_round_scoped : scoped.

(* ======================================================================== *)
(* A rewrite made to keep scope by a test                                   *)
(* ======================================================================== *)

Lemma scope_kept_scoped (e e' : expr) :
  scope_kept e e' = true -> scoped e e'.
Proof.
  unfold scope_kept. intros Hkept _.
  apply andb_true_iff in Hkept. destruct Hkept as [Hkept Hk].
  apply andb_true_iff in Hkept. destruct Hkept as [Hclosed Hv].
  split; [ exact Hclosed | ].
  split; intros name Hname;
    [ exact (all_among_In _ _ name Hv Hname)
    | exact (all_among_In _ _ name Hk Hname) ].
Qed.

Lemma scoped_scope_kept (e e' : expr) :
  code_closed e = true -> scoped e e' -> scope_kept e e' = true.
Proof.
  intros Hclosed Hscoped. destruct (Hscoped Hclosed) as (Hclosed' & Hv & Hk).
  unfold scope_kept. rewrite Hclosed'. cbn [andb].
  apply andb_true_iff.
  split; apply all_among_iff; intros name Hname; apply among_In;
    [ apply Hv | apply Hk ]; apply among_In; exact Hname.
Qed.

Lemma guard_scope_scoped (f : expr -> expr) (e : expr) :
  scoped e (guard_scope f e).
Proof.
  unfold guard_scope. cbv zeta. intros Hclosed. rewrite Hclosed.
  cbn [negb orb].
  destruct (scope_kept e (f e)) eqn:Hkept;
    [ exact (scope_kept_scoped e (f e) Hkept Hclosed)
    | exact (scoped_refl e Hclosed) ].
Qed.

#[export] Hint Resolve guard_scope_scoped : scoped.

Theorem guard_scope_keeps_scope : guard_scope_keeps_scope_statement.
Proof. intros f. apply keeps_scope_intro, guard_scope_scoped. Qed.

Theorem guard_scope_unchanged : guard_scope_unchanged_statement.
Proof.
  intros f Hf e. unfold guard_scope. cbv zeta.
  destruct (code_closed e) eqn:Hclosed; cbn [negb orb]; [ | reflexivity ].
  rewrite (scoped_scope_kept e (f e) Hclosed (keeps_scope_scoped f Hf e)).
  reflexivity.
Qed.

Lemma all_among_rename_variable (r : renaming) (xs ys : list variable) :
  FlambdaMapSpec.all_among (map (rename_variable r) xs)
    (map (rename_variable r) ys)
  = FlambdaMapSpec.all_among xs ys.
Proof.
  unfold FlambdaMapSpec.all_among.
  induction xs as [ | x xs IH]; [ reflexivity | ].
  cbn [map forallb]. rewrite among_rename_variable, IH. reflexivity.
Qed.

Lemma all_among_rename_continuation (r : renaming)
    (ks js : list continuation) :
  FlambdaMapSpec.all_among (map (rename_continuation r) ks)
    (map (rename_continuation r) js)
  = FlambdaMapSpec.all_among ks js.
Proof.
  unfold FlambdaMapSpec.all_among.
  induction ks as [ | k ks IH]; [ reflexivity | ].
  cbn [map forallb]. rewrite among_rename_continuation, IH. reflexivity.
Qed.

Lemma scope_kept_renamed (r : renaming) (e e' : expr) :
  scope_kept (rename_expr r e) (rename_expr r e') = scope_kept e e'.
Proof.
  unfold scope_kept.
  rewrite code_closed_renamed, !free_variables_of_expr_renamed,
    !free_continuations_of_expr_renamed, all_among_rename_variable,
    all_among_rename_continuation.
  reflexivity.
Qed.

Theorem guard_scope_equivariant : guard_scope_equivariant_statement.
Proof.
  intros f Hf r e. unfold guard_scope. cbv zeta.
  rewrite Hf, code_closed_renamed, scope_kept_renamed.
  destruct (negb (code_closed e) || scope_kept e (f e)); reflexivity.
Qed.
