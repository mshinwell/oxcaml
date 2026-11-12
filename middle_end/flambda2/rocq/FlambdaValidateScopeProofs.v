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
From OxCamlFlambda2 Require Import FlambdaModel FlambdaSemanticsSpec
  FlambdaNormaliseSpec FlambdaBlockLoadSpec FlambdaCseSpec
  FlambdaIdentitiesSpec FlambdaRenameApartSpec FlambdaUnboxSpec
  FlambdaUnusedContsSpec
  FlambdaLoopAliasesSpec FlambdaRecHandlersSpec FlambdaShortcutSpec
  FlambdaSinkContsSpec FlambdaUnusedParamsSpec FlambdaValidateSpec
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
