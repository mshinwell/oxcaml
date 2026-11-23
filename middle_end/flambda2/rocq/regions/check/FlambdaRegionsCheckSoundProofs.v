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

(* Proofs of the eleven statements of FlambdaRegionsCheckSoundSpec.v. That
   where a run stops because [step] has no step the run of the term with
   its regions dropped goes wrong is C3's, of FlambdaRegionsNoStepProofs.v,
   whose last theorem has the text of the statement. That the check is
   sound follows: every state of the run of a term that passes the check
   has the property of states, which gives the two things that the first
   statement asks of the states of the run. The two statements about a run
   of Simplify of which [refines] is a premise are those of
   FlambdaRegionsCheckProofs.v, with the soundness of the check for their
   premise [regions_add_no_fault]. The two with less than [refines]
   for their premise are proved as those two are: the first from the
   soundness of the check, the second from it and from the two
   statements of the erasure about exits. [refines] gives their
   premises by its definition. The two of a unit with its imports
   and [unit_refines] of the two terms with their regions dropped are
   instances of the two with less than [refines], at the static
   environment of the imports: [unit_refines] there is [refines] of
   the first states, by computation. The two of a unit with
   its imports and a verdict follow from them: the theorem of the
   validation with imports gives [unit_refines] of the two terms that
   the validation is given, the comparison up to bound names is
   sound, and [refines] is transitive. Nothing here needs review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec FlambdaCompareSpec FlambdaImportsSpec
  FlambdaValidateSpec FlambdaValidateImportsSpec FlambdaRegionsSpec
  FlambdaRegionsErasureSpec FlambdaRegionsCheckSpec FlambdaRegionsCheckedSpec
  FlambdaRegionsCheckSoundSpec.
From OxCamlFlambda2 Require Import FlambdaSemanticsProofs FlambdaCompareProofs
  FlambdaValidateImportsProofs FlambdaRegionsErasureProofs
  FlambdaRegionsNoStepProofs.
From OxCamlFlambda2 Require Import FlambdaRegionsCheckedProofs
  FlambdaRegionsCheckProofs.
Import ListNotations.

(* The check is sound, given the statement about the erasure: every
   state of the run of a term that passes the check has the property
   of states, so what a step of it reads may be read and the regions
   of the handler that it applies are given; and the run stops
   without a step only where [step] has none. *)
Lemma region_check_sound_of_erased :
  no_plain_step_erased_statement -> region_check_sound_statement.
Proof.
  intros Herased cert statics base e Hcheck Hfresh Herasable fuel fault Hrun.
  pose proof (checked_initial cert statics base e Hcheck Hfresh) as Hinitial.
  pose proof (region_run_fault cert _ fuel _ fault Hinitial Hrun) as ->.
  apply (Herased e statics base fuel Hfresh Herasable); [ | exact Hrun ].
  intros fuel' rs Hrs.
  pose proof (region_run_keeps_checked cert _ fuel' _ rs Hinitial Hrs)
    as Hchecked.
  split.
  - exact (checked_reads_live cert _ rs Hchecked).
  - exact (checked_regions_given cert _ rs Hchecked).
Qed.

(* Where a run in every state of which what a step reads may be read
   and the regions of the handler that is applied are given stops
   because [step] has no step, the run of the term with its regions
   dropped goes wrong. *)
Theorem no_plain_step_erased : no_plain_step_erased_statement.
Proof. exact no_plain_step_erased_run. Qed.

(* The check is sound: the regions of a term that passes it add no
   fault to the term. *)
Theorem region_check_sound : region_check_sound_statement.
Proof. exact (region_check_sound_of_erased no_plain_step_erased). Qed.

(* ======================================================================== *)
(* A run of Simplify, with the check                                        *)
(* ======================================================================== *)

Theorem refined_and_checked_safe : refined_and_checked_safe_statement.
Proof.
  intros cert statics base before after Hrefines Hdefined Hcheck Hfresh
    Herasable.
  exact
    (checked_after_safe statics base before after Hrefines Hdefined
       (region_check_sound cert statics base after Hcheck Hfresh Herasable)).
Qed.

Theorem refined_and_checked_exits_agree :
  refined_and_checked_exits_agree_statement.
Proof.
  intros cert statics base before after Hfresh Hfresh' Herasable Herasable'
    Hrefines Hdefined Hcheck.
  exact
    (checked_exits_agree statics base before after Hfresh Hfresh' Herasable
       Herasable' Hrefines Hdefined
       (region_check_sound cert statics base after Hcheck Hfresh' Herasable')).
Qed.

(* ======================================================================== *)
(* The same, with less than a refinement                                    *)
(* ======================================================================== *)

Theorem refines_erased_related : refines_erased_related_statement.
Proof.
  intros statics before after [Hexits Hback].
  split.
  - intros Hwrong.
    assert (Hne : Goes_wrong <> Diverges) by discriminate.
    destruct (Hback Goes_wrong Hne Hwrong) as [H | H]; exact H.
  - intros k vs hp Hbehaves. exists vs, hp.
    split; [ exact (Hexits k vs hp Hbehaves) | split; reflexivity ].
Qed.

(* The check gives that the regions of the term after add no fault to
   it; so where its run stopped without a step, the term after, and
   then the term before, would go wrong with its regions dropped. *)
Theorem related_and_checked_safe : related_and_checked_safe_statement.
Proof.
  intros cert statics base before after Honly Hdefined Hcheck Hfresh
    Herasable fuel fault Hrun.
  exact
    (Hdefined
       (Honly
          (region_check_sound cert statics base after Hcheck Hfresh
             Herasable fuel fault Hrun))).
Qed.

(* The exit of the term before with its regions is erased to an exit
   of the term before with its regions dropped; the premise gives an
   exit of the term after with its regions dropped that is related to
   it; and where that term exits, the term after with its regions
   exits alike, as it never stops without a step. *)
Theorem related_and_checked_exits : related_and_checked_exits_statement.
Proof.
  intros R cert statics base before after Hfresh Hfresh' Herasable
    Herasable' Hexits Honly Hdefined Hcheck fuel k vs rs Hrun.
  pose proof
    (related_and_checked_safe cert statics base before after Honly Hdefined
       Hcheck Hfresh' Herasable')
    as Hsafe.
  destruct
    (erasure_exits before statics base fuel k vs rs Hfresh Herasable Hrun)
    as (us & hp & Hbehaves & Hvs).
  destruct (Hexits k us hp Hbehaves) as (us' & hp' & Hbehaves' & Hrelated).
  destruct
    (erasure_adds_no_exit after statics base k us' hp' Hfresh' Herasable'
       Hbehaves')
    as [fuel' [[fault Hfault] | (ws & rs' & Hrun' & Hws)]].
  - contradiction (Hsafe fuel' fault Hfault).
  - exists fuel', ws, rs', us, us', hp, hp'. auto 10.
Qed.

(* ======================================================================== *)
(* The same, of a unit with its imports and a refinement of the two terms   *)
(* with their regions dropped                                               *)
(* ======================================================================== *)

(* [unit_refines] of the two terms with their regions dropped is
   [refines] of the states from which the erasure runs them in the
   static environment of the imports: [erase_statics] leaves that
   static environment as it is, by computation. *)
Lemma unit_refines_erased (imports : list (symbol * import_class))
    (before after : expr) :
  unit_refines imports (erase [] before) (erase [] after) ->
  refines (erased_initial_state before (imports_statics imports))
    (erased_initial_state after (imports_statics imports)).
Proof. intros Hrefines. exact Hrefines. Qed.

Theorem unit_refined_and_checked_safe :
  unit_refined_and_checked_safe_statement.
Proof.
  intros imports cert base before after statics Hrefines Hdefined Hcheck
    Hfresh Herasable.
  destruct
    (refines_erased_related statics before after
       (unit_refines_erased imports before after Hrefines))
    as [Honly _].
  exact
    (related_and_checked_safe cert statics base before after Honly Hdefined
       Hcheck Hfresh Herasable).
Qed.

Theorem unit_refined_and_checked_exits_agree :
  unit_refined_and_checked_exits_agree_statement.
Proof.
  intros imports cert base before after statics Hfresh Hfresh' Herasable
    Herasable' Hrefines Hdefined Hcheck fuel k vs rs Hrun.
  destruct
    (refines_erased_related statics before after
       (unit_refines_erased imports before after Hrefines))
    as [Honly Hexits].
  destruct
    (related_and_checked_exits _ cert statics base before after Hfresh
       Hfresh' Herasable Herasable' Hexits Honly Hdefined Hcheck fuel k vs rs
       Hrun)
    as (fuel' & ws & rs' & us & us' & hp & hp' & Hrun' & _ & _ & Hvs & Hws
        & -> & _).
  exists fuel', ws, rs', us. auto.
Qed.

(* ======================================================================== *)
(* The same, of a unit with its imports and a verdict of the validation     *)
(* ======================================================================== *)

(* Two terms with their regions dropped by [erase] that are, up to
   bound names, two terms of which [unit_refines] holds: [refines]
   holds of their first states in the static environment of the
   imports, which [erase_statics] leaves as it is. *)
Lemma erased_refines_of_compared (imports : list (symbol * import_class))
    (before after validated_before validated_after : expr) :
  expr_eqb [] [] (erase [] before) validated_before = true ->
  expr_eqb [] [] (erase [] after) validated_after = true ->
  unit_refines imports validated_before validated_after ->
  refines (erased_initial_state before (imports_statics imports))
    (erased_initial_state after (imports_statics imports)).
Proof.
  intros Hbefore Hafter Hrefines.
  apply (refines_trans _
           (State validated_before [] [] (imports_statics imports)
              empty_heap no_reads)).
  { apply equivalent_refines. exact (expr_eqb_sound _ _ Hbefore _ _ _ _ rd_). }
  apply (refines_trans _
           (State validated_after [] [] (imports_statics imports)
              empty_heap no_reads)).
  { exact Hrefines. }
  apply equivalent_refines, equivalent_sym.
  exact (expr_eqb_sound _ _ Hafter _ _ _ _ rd_).
Qed.

Theorem validated_and_checked_safe : validated_and_checked_safe_statement.
Proof.
  intros imports rounds unused slots G Ls kept cert base before after
    validated_before validated_after statics Hverdict Hbefore Hafter
    Hdefined Hcheck Hfresh Herasable.
  exact
    (refined_and_checked_safe cert statics base before after
       (erased_refines_of_compared imports before after validated_before
          validated_after Hbefore Hafter
          (validate_unit_sound_verdict_imports imports rounds unused slots G
             Ls kept validated_before validated_after Hverdict))
       Hdefined Hcheck Hfresh Herasable).
Qed.

Theorem validated_and_checked_exits_agree :
  validated_and_checked_exits_agree_statement.
Proof.
  intros imports rounds unused slots G Ls kept cert base before after
    validated_before validated_after statics Hverdict Hbefore Hafter
    Hdefined Hcheck Hfresh Hfresh' Herasable Herasable'.
  exact
    (refined_and_checked_exits_agree cert statics base before after Hfresh
       Hfresh' Herasable Herasable'
       (erased_refines_of_compared imports before after validated_before
          validated_after Hbefore Hafter
          (validate_unit_sound_verdict_imports imports rounds unused slots G
             Ls kept validated_before validated_after Hverdict))
       Hdefined Hcheck).
Qed.
