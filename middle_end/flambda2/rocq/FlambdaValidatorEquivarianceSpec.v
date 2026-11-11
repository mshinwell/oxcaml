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

   This file is to be reviewed: [rewrite_equivariant], the action of a
   renaming on what a pass carries (the definitions named [rename_...]),
   and the statements.

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

   Those of FlambdaUnusedContsSpec.v: the check [cont_free_b] and the
   rewrite [remove_unused_conts].

   Those of FlambdaUnusedStaticsSpec.v, where the names given are
   symbols and code ids: the checks [expr_avoids] and
   [binds_only_kept], the rewrite [erase_expr], and [drop_statics],
   which is the two together; and the condition on the environments
   under which that rewrite is sound ([envs_free_of]).

   Two passes go through a term carrying what they know of its names:
   FlambdaBlockLoadSpec.load_known_blocks, of the variables and symbols
   that are blocks, and FlambdaUnboxSpec.unbox_known_numbers, of those
   that are boxed or tagged numbers. What they carry holds variables,
   so a renaming acts on it ([rename_known_blocks],
   [rename_known_numbers], which are to be reviewed), and each pass
   commutes with renaming when what it knows is renamed with the term.
   As the validation runs them, with nothing known, they are rewrites
   that take a term and nothing else.

   Nothing is trusted here. The proofs are in
   FlambdaValidatorEquivarianceProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaNominalSpec FlambdaAlphaSpec
  FlambdaNormaliseSpec FlambdaEquivarianceSpec FlambdaUnusedContsSpec
  FlambdaUnusedStaticsSpec FlambdaBlockLoadSpec FlambdaUnboxSpec.
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

(* ======================================================================== *)
(* FlambdaUnusedContsSpec.v                                                 *)
(* ======================================================================== *)

Definition cont_free_b_equivariant_statement : Prop :=
  ∀ (r : renaming) (k : continuation) (e : expr),
    cont_free_b (rename_continuation r k) (rename_expr r e) = cont_free_b k e.

Definition remove_unused_conts_equivariant_statement : Prop :=
  rewrite_equivariant remove_unused_conts.

(* ======================================================================== *)
(* FlambdaUnusedStaticsSpec.v                                               *)
(* ======================================================================== *)

(* The names removed are symbols and code ids, which no renaming moves:
   the argument that holds them is as it was. *)
Definition expr_avoids_equivariant_statement : Prop :=
  ∀ (r : renaming) (D : dropped) (e : expr),
    expr_avoids D (rename_expr r e) = expr_avoids D e.

Definition erase_expr_equivariant_statement : Prop :=
  ∀ D : dropped, rewrite_equivariant (erase_expr D).

(* Where the names given may not be removed from the one term they may
   not be from the other. *)
Definition drop_statics_equivariant_statement : Prop :=
  ∀ (r : renaming) (D : dropped) (e : expr),
    drop_statics D (rename_expr r e)
    = option_map (rename_expr r) (drop_statics D e).

Definition binds_only_kept_equivariant_statement : Prop :=
  ∀ (r : renaming) (D : dropped) (e : expr),
    binds_only_kept D (rename_expr r e) = binds_only_kept D e.

(* The condition on the environments under which removing static
   bindings is sound (the premise of
   FlambdaUnusedStaticsSpec.drop_statics_refines_statement), with the
   action of FlambdaEquivarianceSpec.v on what a state holds. *)
Definition envs_free_of_equivariant_statement : Prop :=
  ∀ (r : renaming) (D : dropped) (vars : env) (conts : cont_env)
    (statics : static_env),
    envs_free_of D (rename_env r vars) (rename_cont_env r conts)
      (rename_static_env r statics)
    = envs_free_of D vars conts statics.

(* ======================================================================== *)
(* FlambdaBlockLoadSpec.v: what is known of blocks                          *)
(* ======================================================================== *)

(* The pass carries what is known of the blocks of the term, which holds
   variables: those that are known to be blocks, and those that the
   fields of a block are known to hold. A renaming acts on both. The
   symbols that are known to be blocks, the tags and the numbers of
   fields are as they were. *)
Definition rename_known_block (r : renaming) (block : known_block)
    : known_block :=
  (fst block, map (option_map (rename_simple r)) (snd block)).

Definition rename_known_blocks (r : renaming) (known : known_blocks)
    : known_blocks :=
  Known_blocks
    (map
       (fun entry =>
          (rename_variable r (fst entry), rename_known_block r (snd entry)))
       (known_vars known))
    (map_values (rename_known_block r) (known_symbols known)).

(* What is known is renamed with the term. *)
Definition load_blocks_knowing_equivariant_statement : Prop :=
  ∀ (r : renaming) (known : known_blocks) (e : expr),
    load_blocks_knowing (rename_known_blocks r known) (rename_expr r e)
    = rename_expr r (load_blocks_knowing known e).

(* The pass as the validation runs it, with nothing known. *)
Definition load_known_blocks_equivariant_statement : Prop :=
  rewrite_equivariant load_known_blocks.

(* ======================================================================== *)
(* FlambdaUnboxSpec.v: what is known of wrapped numbers                     *)
(* ======================================================================== *)

(* Likewise: the variables that are known to be wrapped numbers are
   renamed, and what each wraps. What is known of a symbol is a
   constant. *)
Definition rename_known_numbers (r : renaming) (known : known_numbers)
    : known_numbers :=
  Known_numbers
    (map
       (fun entry =>
          (rename_variable r (fst entry),
           (fst (snd entry), rename_simple r (snd (snd entry)))))
       (known_wrapped_vars known))
    (known_boxed_symbols known).

Definition unbox_numbers_knowing_equivariant_statement : Prop :=
  ∀ (r : renaming) (known : known_numbers) (e : expr),
    unbox_numbers_knowing (rename_known_numbers r known) (rename_expr r e)
    = rename_expr r (unbox_numbers_knowing known e).

Definition unbox_known_numbers_equivariant_statement : Prop :=
  rewrite_equivariant unbox_known_numbers.
