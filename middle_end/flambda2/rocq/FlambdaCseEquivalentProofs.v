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

(* Proofs of the statement of FlambdaCseEquivalentSpec.v. Nothing here
   needs review.

   FlambdaCseProofs.v proves that the result of the pass refines the
   term, by recursion on the term, with what the pass knows holding
   where the term runs. The converse is by the same recursion, with
   the lemmas of that file that keep what is known: where what is
   known holds, a defining expression and what the pass makes of it
   have the same value or both have none ([share_named_same]). *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaKindModel FlambdaValueSpec FlambdaPrimitiveModel
  FlambdaPrimitiveSpec FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaContextProofs FlambdaWellFormedSpec FlambdaWellFormedProofs
  FlambdaNormaliseSpec FlambdaNormaliseProofs FlambdaCseSpec
  FlambdaCseProofs FlambdaCseEquivalentSpec.
Import ListNotations.

(* Where what is known holds, sharing does not change what a defining
   expression evaluates to. *)
Lemma share_named_same (known : computed) (vars : env)
    (statics : static_env) (d : named) :
  all_computed known vars statics ->
  eval_named statics vars (share_named known d) = eval_named statics vars d.
Proof.
  intros Hhold. unfold share_named.
  destruct d as [s | p args | code slots | fslot decls slots | slot closure
    | pfrom slot closure | move_from move_to closure];
    try reflexivity.
  destruct (computed_by known p args) as [x | ] eqn:Hcomputed;
    [ | reflexivity ].
  destruct (Hhold _ (computed_by_sound _ _ _ _ Hcomputed))
    as (vs & r & Hvs & Hprim & Hlookup).
  simpl in Hvs, Hprim, Hlookup. simpl. rewrite Hvs. simpl.
  rewrite Hprim. exact Hlookup.
Qed.

(* The term refines the result: FlambdaCseProofs.v has the converse. *)
Fixpoint share_primitives_knowing_refined (e : expr) :
  ∀ (known : computed) (vars : env) (conts : cont_env)
    (statics : static_env) (hp : heap),
    all_computed known vars statics ->
    refines (State (share_primitives_knowing known e) vars conts statics hp)
      (State e vars conts statics hp)
with share_primitives_in_handler_refined (h : continuation_handler) :
  ∀ (known : computed) (k : continuation) (body : expr) (vars : env)
    (conts : cont_env) (statics : static_env) (hp : heap),
    all_computed known vars statics ->
    refines
      (State
         (Let_cont_non_recursive k (share_primitives_in_handler known h)
            body)
         vars conts statics hp)
      (State (Let_cont_non_recursive k h body) vars conts statics hp).
Proof.
  - destruct e
      as [ x kind d body | bindings body | k h body | handlers body | ap
         | ac | scrutinee arms | ];
      intros known vars conts statics hp Hhold; simpl.
    + (* Let *)
      pose proof (share_named_same known vars statics d Hhold) as Hsame.
      destruct (eval_named statics vars d) as [v | ] eqn:Hd;
        [ destruct (kind_eqb (kind_of_value v) kind) eqn:Hkind | ].
      * eapply refines_step;
          [ rewrite step_let, Hsame, Hkind; reflexivity
          | rewrite step_let, Hd, Hkind; reflexivity
          | ].
        apply share_primitives_knowing_refined.
        exact (all_computed_under_let known x d vars statics v Hhold Hd).
      * apply step_undefined_refines. rewrite step_let, Hsame, Hkind.
        reflexivity.
      * apply step_undefined_refines. rewrite step_let, Hsame. reflexivity.
    + (* Let_static *)
      apply let_static_refines_step.
      destruct (eval_static_bindings vars bindings statics)
        as [extended | ] eqn:Hbindings; [ | exact I ].
      apply share_primitives_knowing_refined.
      exact (all_computed_extend known vars statics extended Hhold
        (eval_static_bindings_extend vars bindings _ _ Hbindings)).
    + (* Let_cont_non_recursive *)
      apply (refines_trans _
        (State
           (Let_cont_non_recursive k (share_primitives_in_handler known h)
              body)
           vars conts statics hp)).
      * apply let_cont_non_recursive_refines_step,
          share_primitives_knowing_refined, Hhold.
      * apply share_primitives_in_handler_refined, Hhold.
    + (* Let_cont_recursive *)
      apply let_cont_recursive_refines_step; [ reflexivity | intros _ ].
      apply share_primitives_knowing_refined, Hhold.
    + apply refines_refl.
    + apply refines_refl.
    + apply refines_refl.
    + apply refines_refl.
  - destruct h as [params metadata handler].
    intros known k body vars conts statics hp Hhold. simpl.
    apply (let_cont_handler_refines_where (statics_extend statics)
      (statics_extend_trans statics));
      [ apply statics_extend_refl | ].
    intros vs handler_vars conts' statics' hp' Hextend _ Hbind.
    apply share_primitives_knowing_refined.
    apply (all_computed_bind_params statics' params known vs vars
      handler_vars);
      [ exact (all_computed_extend known vars statics statics' Hhold
          Hextend)
      | exact Hbind ].
Qed.

Theorem share_known_primitives_equivalent :
  share_known_primitives_equivalent_statement.
Proof.
  intros e vars conts statics hp. apply refines_antisymmetric.
  - apply share_primitives_knowing_refines. intros entry [].
  - apply share_primitives_knowing_refined. intros entry [].
Qed.
