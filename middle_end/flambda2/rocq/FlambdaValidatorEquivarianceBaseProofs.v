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


(* Lemmas of FlambdaValidatorEquivarianceProofs.v that files below the
   validation import: the two tests of free names in a handler on
   renamed arguments. Moved here as they were; this file needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaNominalSpec
  FlambdaNominalProofs FlambdaAlphaSpec FlambdaAlphaProofs
  FlambdaNormaliseSpec FlambdaEquivarianceSpec FlambdaEquivarianceProofs
  FlambdaUnusedContsSpec.
Import ListNotations.

Lemma existsb_map_with {A B : Type} (f : B -> bool) (g : A -> B)
    (h : A -> bool) (l : list A) :
  (∀ a : A, f (g a) = h a) -> existsb f (map g l) = existsb h l.
Proof.
  intros Hfg. induction l as [ | a l IH]; simpl; [ reflexivity | ].
  rewrite Hfg, IH. reflexivity.
Qed.

(* Whether a continuation is among those that an [Apply_cont] names. *)
Lemma among_apply_cont_continuations_renamed (r : renaming)
    (k : continuation) (ac : apply_cont) :
  among (rename_continuation r k)
    (apply_cont_continuations (rename_apply_cont r ac))
  = among k (apply_cont_continuations ac).
Proof.
  rewrite apply_cont_continuations_renamed.
  apply among_rename_continuation.
Qed.

Lemma var_in_simple_equivariant (r : renaming) (x : variable) (s : simple) :
  var_in_simple (rename_variable r x) (rename_simple r s) = var_in_simple x s.
Proof. destruct s; simpl; [ apply rename_variable_eqb | | ]; reflexivity. Qed.

Lemma var_in_value_slots_equivariant (r : renaming) (x : variable)
    (slots : list (value_slot * simple)) :
  var_in_value_slots (rename_variable r x)
    (map (fun slot => (fst slot, rename_simple r (snd slot))) slots)
  = var_in_value_slots x slots.
Proof.
  unfold var_in_value_slots. apply existsb_map_with. intros slot.
  apply var_in_simple_equivariant.
Qed.

Lemma var_in_named_equivariant (r : renaming) (x : variable) (d : named) :
  var_in_named (rename_variable r x) (rename_named r d) = var_in_named x d.
Proof.
  destruct d; simpl;
    first
      [ apply var_in_simple_equivariant | apply var_in_simples_equivariant
      | apply var_in_value_slots_equivariant ].
Qed.

Lemma var_in_static_binding_equivariant (r : renaming) (x : variable)
    (binding : static_binding) :
  var_in_static_binding (rename_variable r x)
    (rename_static_binding r binding)
  = var_in_static_binding x binding.
Proof.
  destruct binding as [id c | id | sym const]; simpl; try reflexivity.
  destruct const; simpl;
    first
      [ reflexivity | apply var_in_value_slots_equivariant
      | apply var_in_simples_equivariant | apply var_in_simple_equivariant ].
Qed.

Fixpoint var_free_b_equivariant_aux (r : renaming) (x : variable) (e : expr) :
  var_free_b (rename_variable r x) (rename_expr r e) = var_free_b x e
with var_free_in_handler_b_equivariant (r : renaming) (x : variable)
    (h : continuation_handler) :
  var_free_in_handler_b (rename_variable r x) (rename_handler r h)
  = var_free_in_handler_b x h.
Proof.
  - destruct e
      as [ y d body | bindings body | k h body | handlers body | ap | ac
         | scrutinee arms | ];
      simpl.
    + rewrite var_in_named_equivariant, rename_variable_eqb,
        var_free_b_equivariant_aux.
      reflexivity.
    + rewrite var_free_b_equivariant_aux. f_equal.
      apply existsb_map_with. intros binding.
      apply var_in_static_binding_equivariant.
    + rewrite var_free_in_handler_b_equivariant, var_free_b_equivariant_aux.
      reflexivity.
    + rewrite var_free_b_equivariant_aux. f_equal.
      induction handlers as [ | [k h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (var_free_in_handler_b_equivariant r x h), IH. reflexivity.
    + rewrite exn_extra_simples_rename, var_in_simple_equivariant,
        !var_in_simples_equivariant.
      reflexivity.
    + apply var_in_simples_equivariant.
    + rewrite var_in_simple_equivariant. f_equal.
      apply existsb_map_with. intros arm. apply var_in_simples_equivariant.
    + reflexivity.
  - destruct h as [params metadata handler]. simpl.
    rewrite among_rename_variable, var_free_b_equivariant_aux. reflexivity.
Qed.

Fixpoint cont_free_b_equivariant_aux (r : renaming) (k : continuation)
    (e : expr) :
  cont_free_b (rename_continuation r k) (rename_expr r e) = cont_free_b k e
with cont_free_in_handler_b_equivariant (r : renaming) (k : continuation)
    (h : continuation_handler) :
  cont_free_in_handler_b (rename_continuation r k) (rename_handler r h)
  = cont_free_in_handler_b k h.
Proof.
  - destruct e
      as [ x kind d body | bindings body | bound h body | handlers body | ap
         | ac | scrutinee arms | ];
      simpl.
    + apply cont_free_b_equivariant_aux.
    + apply cont_free_b_equivariant_aux.
    + rewrite cont_free_in_handler_b_equivariant, rename_continuation_eqb,
        cont_free_b_equivariant_aux.
      reflexivity.
    + rewrite cont_free_b_equivariant_aux. f_equal.
      induction handlers as [ | [k' h] handlers IH]; simpl; [ reflexivity | ].
      rewrite (cont_free_in_handler_b_equivariant r k h), IH. reflexivity.
    + rewrite !rename_continuation_eqb. reflexivity.
    + exact (among_apply_cont_continuations_renamed r k ac).
    + apply existsb_map_with. intros arm.
      exact (among_apply_cont_continuations_renamed r k (snd arm)).
    + reflexivity.
  - destruct h as [params metadata handler]. simpl.
    apply cont_free_b_equivariant_aux.
Qed.
