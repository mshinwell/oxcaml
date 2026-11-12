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

(* Proofs of the statements of FlambdaSinkUsesSpec.v. Nothing here needs
   review.

   Each move of a [Let_cont] is one of those of
   FlambdaSinkContsProofs.v: past a [Let], past a [Let_static], past
   another [Let_cont]. FlambdaContextProofs.plug_equivalent puts it
   where it is made. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaSemanticsProofs FlambdaNominalSpec
  FlambdaNominalProofs FlambdaContextSpec FlambdaContextProofs
  FlambdaNormaliseSpec FlambdaNormaliseProofs FlambdaUnusedContsSpec
  FlambdaUnusedContsProofs FlambdaSinkContsSpec FlambdaSinkContsProofs
  FlambdaSinkUsesSpec.
Import ListNotations.

(* A [Let_cont] moved is equivalent to the [Let_cont] where it was. *)
Fixpoint sink_to_use_equivalent (body : expr) {struct body} :
  ∀ (k : continuation) (h : continuation_handler) (sunk : expr),
    sink_to_use k h body = Some sunk ->
    expr_equivalent (Let_cont_non_recursive k h body) sunk.
Proof.
  destruct body
    as [ x kind d body | bindings body | k' [params' metadata' handler'] body
       | handlers body | ap | ac | scrutinee arms | ];
    intros k h sunk; simpl; try discriminate.
  - (* Let *)
    destruct (var_free_in_handler_b x h) eqn:Hfree; [ discriminate | ].
    destruct (sink_to_use k h body) as [sunk' | ] eqn:Hsink;
      [ | discriminate ].
    intros [= <-].
    apply (expr_equivalent_trans _
      (Let x kind d (Let_cont_non_recursive k h body))).
    + apply let_cont_past_let. intros Hx.
      apply var_free_in_handler_b_sound in Hx. congruence.
    + exact (plug_equivalent (Let_body x kind d Hole) _ _ (not_many _)
        (sink_to_use_equivalent body k h sunk' Hsink)).
  - (* Let_static *)
    destruct (sink_to_use k h body) as [sunk' | ] eqn:Hsink;
      [ | discriminate ].
    intros [= <-].
    apply (expr_equivalent_trans _
      (Let_static bindings (Let_cont_non_recursive k h body))).
    + apply let_cont_past_let_static.
    + exact (plug_equivalent (Let_static_body bindings Hole) _ _ (not_many _)
        (sink_to_use_equivalent body k h sunk' Hsink)).
  - (* past another Let_cont *)
    destruct
      (negb (Pos.eqb k k') && negb (cont_free_b k handler')
       && negb (cont_free_in_handler_b k' h))
      eqn:Hpast; [ | discriminate ].
    destruct (sink_to_use k h body) as [sunk' | ] eqn:Hsink;
      [ | discriminate ].
    intros [= <-].
    apply andb_true_iff in Hpast as [Hpast Hk'].
    apply andb_true_iff in Hpast as [Hne Hk].
    apply negb_true_iff in Hne, Hk, Hk'. apply Pos.eqb_neq in Hne.
    apply (expr_equivalent_trans _
      (Let_cont_non_recursive k' (Handler params' metadata' handler')
         (Let_cont_non_recursive k h body))).
    + apply let_cont_past_let_cont; [ exact Hne | | ].
      * intros Hfree. simpl in Hfree.
        apply cont_free_b_sound in Hfree. congruence.
      * intros Hfree. apply cont_free_in_handler_b_sound in Hfree.
        congruence.
    + exact (plug_equivalent
        (Let_cont_non_recursive_body k'
           (Handler params' metadata' handler') Hole)
        _ _ (not_many _)
        (sink_to_use_equivalent body k h sunk' Hsink)).
  - (* the call *)
    destruct
      (Pos.eqb k (ap_continuation ap) || Pos.eqb k (ap_exn_continuation ap));
      [ | discriminate ].
    intros [= <-] vars conts statics hp. apply equivalent_refl.
  - (* the test *)
    destruct (arms_apply k arms); [ | discriminate ].
    intros [= <-] vars conts statics hp. apply equivalent_refl.
Qed.

(* Each layer is a context around what the induction gives; then the
   [Let_cont] is moved. *)
Fixpoint sink_conts_to_uses_equivalent_aux (e : expr) :
  expr_equivalent e (sink_conts_to_uses e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    simpl; try (intros vars conts statics hp; apply equivalent_refl).
  - exact (plug_equivalent (Let_body x kind d Hole) _ _ (not_many _)
      (sink_conts_to_uses_equivalent_aux body)).
  - exact (plug_equivalent (Let_static_body bindings Hole) _ _ (not_many _)
      (sink_conts_to_uses_equivalent_aux body)).
  - assert (Hlayers :
      expr_equivalent
        (Let_cont_non_recursive k (Handler params metadata handler) body)
        (Let_cont_non_recursive k
           (Handler params metadata (sink_conts_to_uses handler))
           (sink_conts_to_uses body))).
    { apply (expr_equivalent_trans _
        (Let_cont_non_recursive k
           (Handler params metadata (sink_conts_to_uses handler)) body)).
      - exact (plug_equivalent
          (Let_cont_non_recursive_handler k params metadata Hole body) _ _
          (not_many _) (sink_conts_to_uses_equivalent_aux handler)).
      - exact (plug_equivalent
          (Let_cont_non_recursive_body k
             (Handler params metadata (sink_conts_to_uses handler)) Hole)
          _ _ (not_many _) (sink_conts_to_uses_equivalent_aux body)). }
    destruct
      (sink_to_use k
         (Handler params metadata (sink_conts_to_uses handler))
         (sink_conts_to_uses body))
      as [sunk | ] eqn:Hsink; [ | exact Hlayers ].
    exact (expr_equivalent_trans _ _ _ Hlayers
      (sink_to_use_equivalent _ _ _ _ Hsink)).
  - exact (plug_equivalent (Let_cont_recursive_body handlers Hole) _ _
      (not_many _) (sink_conts_to_uses_equivalent_aux body)).
Qed.

Theorem sink_conts_to_uses_equivalent :
  sink_conts_to_uses_equivalent_statement.
Proof. exact sink_conts_to_uses_equivalent_aux. Qed.
