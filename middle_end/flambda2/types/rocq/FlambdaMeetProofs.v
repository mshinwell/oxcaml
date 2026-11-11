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



(* Proofs of the statements of FlambdaMeetSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaEnvAliasesSpec
  FlambdaTypingEnv FlambdaTypingEnvSpec FlambdaTypingEnvProofs
  FlambdaExpandHead FlambdaMeetEnv FlambdaMeetSpec.
Import ListNotations.

(* ======================================================================== *)
(* What the contracts give                                                  *)
(* ======================================================================== *)

Theorem meet_answers_bottom : meet_answers_bottom_statement.
Proof.
  intros type_well_formed typing_env_well_formed meet Hsound statics
    valuation tenv t1 t2 v Hinputs Hsatisfied Hmeet [Ht1 Ht2].
  destruct
    (Hsound statics valuation tenv t1 t2 v _ Hinputs Hsatisfied Ht1 Ht2 Hmeet)
    as [t [tenv' [valuation' [Hresult _]]]].
  discriminate Hresult.
Qed.

Theorem add_equation_no_poison : add_equation_no_poison_statement.
Proof.
  intros type_well_formed typing_env_well_formed add_equation Hsound statics
    valuation tenv tenv' n ty v Hfits Hty Hsatisfied Hpoison Hvalue Hv Hadd.
  apply (Hsound statics valuation tenv tenv' n ty v Hfits Hty); try assumption.
  apply satisfied_no_poison_strictly; assumption.
Qed.

(* ======================================================================== *)
(* The step of the compiler's meet that is not sound                        *)
(* ======================================================================== *)

Theorem get_tag_reduction_unsound : get_tag_reduction_unsound_statement.
Proof.
  exists empty_static_env, [], (Value_const (Tagged_immediate 7)), 0%Z.
  split; [ | split ].
  - left. exists 7%Z. reflexivity.
  - intros [k Hpoison]. discriminate Hpoison.
  - intros Hblock.
    apply blocks_with_these_tags_satisfied in Hblock
      as [tag [fields [Hblock _]]].
    discriminate Hblock.
Qed.

Lemma lookup_among_unknown_cases {A : Type} (tag : Z) (tags : list Z) :
  tag ∈ tags ->
  Keyed.lookup Z.eqb tag (map (fun tag => (tag, @Or_unknown.Unknown A)) tags)
  = Some Or_unknown.Unknown.
Proof.
  induction tags as [ | tag' tags IH]; simpl; [ intros [] | ].
  intros [-> | Hin].
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb tag tag'); [ reflexivity | exact (IH Hin) ].
Qed.

Theorem get_tag_reduction_repaired : get_tag_reduction_repaired_statement.
Proof.
  intros statics vars w n tags alloc_mode Hrelation Hin Hnot_poison.
  unfold immediate_or_blocks_with_these_tags.
  apply (create_variant_satisfied statics vars w).
  destruct Hrelation as [[i ->] | [[fields Hblock] | Hpoison]];
    [ | | contradiction ].
  - left. exists i. split; [ reflexivity | ]. split; exact I.
  - right. exists n, fields. split; [ exact Hblock | ]. split; [ | exact I ].
    apply row_like_for_blocks_find.
    rewrite (lookup_among_unknown_cases n tags Hin). exact I.
Qed.
