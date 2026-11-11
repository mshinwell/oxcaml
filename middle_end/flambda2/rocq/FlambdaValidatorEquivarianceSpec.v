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


(* The validator commutes with renaming: each of its rewrites and each of
   its checks.

   This file is to be reviewed: [rewrite_equivariant] and the statements.

   FlambdaEquivarianceSpec.v says that execution commutes with the
   renamings of FlambdaNominalSpec.v, and that two of the rewrites that
   the validation applies do ([fold_constants], [inline_calls]). Here are
   the statements for the others, in the forms that a function on terms
   owes (NAMES.md, section 7):
   - a rewrite that takes a term and nothing else gives, on the renamed
     term, the renamed result ([rewrite_equivariant]);
   - a rewrite that takes names too, or something keyed by names (the
     variables in scope, the code known), gives the renamed result when
     those are renamed with the term;
   - a check answers the same on the renamed term, the names it is given
     being renamed with it.
   Symbols, code ids and slots are not renamed, so what is keyed by them
   is as it was.

   So what the validation does to a term depends on the names of the
   term by their equality only: no rewrite and no check goes by the
   order or the number of a name, and none makes a name. The one place
   where names are made from others is the renaming that inlining
   builds from the four continuations of a call and of the code called
   (FlambdaNormaliseSpec.inline_renaming); it is made of swaps of those
   four, and commutes with a renaming of them.

   Every statement here is an equation, holds of every term, and has no
   premise: nothing is asked of the code, the binders or the scopes.

   Kinds, arities and the metadata of handlers and of code have no
   names in them: a renaming keeps them, and a check that reads them
   answers the same.

   The rewrites and checks of FlambdaNormaliseSpec.v:
   - the checks [expr_in_scope], [inlinable_b] and [var_free_b], and
     the two tests of whether a call is sure to agree with the code
     called ([simple_has_kind_b], [call_agrees_b]);
   - the rewrites [remove_unused_lets], [inline_tail_conts] (with
     [inline_cont_at_tail], which it is made of), [drop_deleted_code],
     [remove_unused_total_lets], [remove_unused_defined_lets],
     [inline_known_calls], [merge_statics], [collapse_switches] and
     [thread_switches];
   - [rewrite_code], which takes a rewrite into the bodies of code: it
     is equivariant when the rewrite it is given is.

   Nothing is trusted here. The proofs are in
   FlambdaValidatorEquivarianceProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaNominalSpec FlambdaNormaliseSpec.
Import ListNotations.

(* A rewrite of terms that takes nothing but the term commutes with
   renaming. *)
Definition rewrite_equivariant (f : expr -> expr) : Prop :=
  ∀ (r : renaming) (e : expr), f (rename_expr r e) = rename_expr r (f e).

(* ======================================================================== *)
(* The checks of FlambdaNormaliseSpec.v                                     *)
(* ======================================================================== *)

(* The names in scope are renamed with the term. *)
Definition expr_in_scope_equivariant_statement : Prop :=
  ∀ (r : renaming) (vs : list variable) (ks : list continuation) (e : expr),
    expr_in_scope (map (rename_variable r) vs)
      (map (rename_continuation r) ks) (rename_expr r e)
    = expr_in_scope vs ks e.

(* Whether a call may be inlined, the call and the code being renamed
   together. *)
Definition inlinable_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (ap : apply_expr) (c : code),
    inlinable_b (rename_apply r ap) (rename_code r c) = inlinable_b ap c.

Definition var_free_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (x : variable) (e : expr),
    var_free_b (rename_variable r x) (rename_expr r e) = var_free_b x e.

(* ======================================================================== *)
(* The rewrites of FlambdaNormaliseSpec.v                                   *)
(* ======================================================================== *)

Definition remove_unused_lets_equivariant_statement : Prop :=
  rewrite_equivariant remove_unused_lets.

(* The continuation, the parameters and the handler are renamed with the
   body; where there is no result for the one there is none for the
   other. The kinds of the parameters have no names in them and stay. *)
Definition inline_cont_at_tail_equivariant_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (params : list variable)
    (metadata : handler_metadata) (handler body : expr),
    inline_cont_at_tail (rename_continuation r k)
      (map (rename_variable r) params) metadata (rename_expr r handler)
      (rename_expr r body)
    = option_map (rename_expr r)
        (inline_cont_at_tail k params metadata handler body).

Definition inline_tail_conts_equivariant_statement : Prop :=
  rewrite_equivariant inline_tail_conts.

Definition drop_deleted_code_equivariant_statement : Prop :=
  rewrite_equivariant drop_deleted_code.

Definition remove_unused_total_lets_equivariant_statement : Prop :=
  rewrite_equivariant remove_unused_total_lets.

(* The variables in scope are renamed with the term. *)
Definition remove_unused_defined_lets_equivariant_statement : Prop :=
  ∀ (r : renaming) (vs : list variable) (e : expr),
    remove_unused_defined_lets (map (rename_variable r) vs) (rename_expr r e)
    = rename_expr r (remove_unused_defined_lets vs e).

(* The two tests that decide whether a call is sure to agree with the
   code called: of an argument, that it is sure to have a kind, and of
   the call. They read kinds and arities, which have no names in them,
   and of an argument only whether it is a variable. *)
Definition simple_has_kind_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (s : simple) (kind : flambda_kind),
    simple_has_kind_b (rename_simple r s) kind = simple_has_kind_b s kind.

Definition call_agrees_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (ap : apply_expr) (c : code),
    call_agrees_b (rename_apply r ap) (rename_code r c) = call_agrees_b ap c.

(* The code known is renamed with the term, as for [inline_calls]. What
   is known of the symbols holds no variable and no continuation. *)
Definition inline_known_calls_equivariant_statement : Prop :=
  ∀ (r : renaming) (known_code : list (code_id * code))
    (known_symbols : list (symbol * option code_id)) (e : expr),
    inline_known_calls (map_values (rename_code r) known_code) known_symbols
      (rename_expr r e)
    = rename_expr r (inline_known_calls known_code known_symbols e).

Definition merge_statics_equivariant_statement : Prop :=
  rewrite_equivariant merge_statics.

Definition collapse_switches_equivariant_statement : Prop :=
  rewrite_equivariant collapse_switches.

Definition thread_switches_equivariant_statement : Prop :=
  rewrite_equivariant thread_switches.

(* A rewrite taken into the bodies of code. *)
Definition rewrite_code_equivariant_statement : Prop :=
  ∀ f : expr -> expr,
    rewrite_equivariant f -> rewrite_equivariant (rewrite_code f).
