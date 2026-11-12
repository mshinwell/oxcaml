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
  FlambdaBindersProofs FlambdaNominalSpec FlambdaAlphaProofs
  FlambdaEquivarianceProofs FlambdaFreeNamesProofs FlambdaGuardScopeSpec
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

Lemma drop_unused_params_scoped (e : expr) : scoped e (drop_unused_params e).
Proof. apply keeps_scope_scoped, drop_unused_params_keeps_scope. Qed.

(* The lemmas that say of a rewrite that its result keeps the scope of
   the term. A rewrite that takes another asks that the other keeps
   scope, which [keeps_scope_intro] makes of a lemma of this form. The
   hints go to the files that import this one, with the tactic. *)
Create HintDb scoped.

#[export] Hint Resolve keeps_scope_intro rename_apart_scoped
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
