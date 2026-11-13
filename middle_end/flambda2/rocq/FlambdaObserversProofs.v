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

(* Proofs of the statements of FlambdaObserversSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaValueSpec FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaBindersSpec FlambdaStaticsInScopeSpec
  FlambdaUnusedSlotsSpec FlambdaUnusedStaticsSpec FlambdaExitWorldSpec
  FlambdaExitWorldProofs FlambdaRunUnderSpec FlambdaRunUnderProofs
  FlambdaObserversSpec.
Import ListNotations.

(* ======================================================================== *)
(* What an exit is compared by                                              *)
(* ======================================================================== *)

Theorem same_scalars_refl : same_scalars_refl_statement.
Proof.
  intros vs. unfold same_scalars.
  induction vs as [ | v vs IH]; constructor; [ | exact IH ].
  intros _. reflexivity.
Qed.

Theorem same_scalars_trans : same_scalars_trans_statement.
Proof.
  intros vs vs' vs'' H1. revert vs''.
  induction H1 as [ | v v' vs vs' Hv _ IH]; intros vs'' H2;
    inversion H2 as [ | ? v'' ? vs3 Hv' Hrest]; subst; constructor;
    [ | exact (IH _ Hrest) ].
  intros [Hs | Hs].
  - pose proof (Hv (or_introl Hs)) as Heq. rewrite Heq in Hs |- *.
    exact (Hv' (or_introl Hs)).
  - pose proof (Hv' (or_intror Hs)) as Heq. rewrite <- Heq in Hs.
    rewrite <- Heq. exact (Hv (or_intror Hs)).
Qed.

Theorem observed_refines_refl : observed_refines_refl_statement.
Proof.
  intros result. split.
  - intros k vs hp H. exists vs, hp.
    split; [ exact H | ]. split; [ apply same_scalars_refl | reflexivity ].
  - intros b Hnot H.
    destruct b as [k vs hp | | ];
      [ right; exists k, vs, hp; exact H | left; exact H
      | contradiction Hnot; reflexivity ].
Qed.

Theorem observed_refines_trans : observed_refines_trans_statement.
Proof.
  intros r1 r2 r3 [Hexits1 Hends1] [Hexits2 Hends2]. split.
  - intros k vs hp H1.
    destruct (Hexits1 k vs hp H1) as (vs' & hp' & H2 & Hc1 & Hl1).
    destruct (Hexits2 k vs' hp' H2) as (vs'' & hp'' & H3 & Hc2 & Hl2).
    exists vs'', hp''. split; [ exact H3 | ].
    split; [ exact (same_scalars_trans _ _ _ Hc1 Hc2) | ].
    rewrite Hl1. exact Hl2.
  - intros b Hnot H3.
    destruct (Hends2 b Hnot H3) as [Hwrong | (k & vs & hp & H2)].
    + apply (Hends1 Goes_wrong); [ discriminate | exact Hwrong ].
    + apply (Hends1 (Exits k vs hp)); [ discriminate | exact H2 ].
Qed.

(* Two results with the same behaviours may stand for each other. *)
Lemma observed_refines_ext (r1 r1' r2 r2' : step_result) :
  (∀ b : behaviour,
    step_result_behaves r1' b <-> step_result_behaves r1 b) ->
  (∀ b : behaviour,
    step_result_behaves r2' b <-> step_result_behaves r2 b) ->
  observed_refines r1 r2 ->
  observed_refines r1' r2'.
Proof.
  intros H1 H2 [Hexits Hends]. split.
  - intros k vs hp H. apply (proj1 (H1 _)) in H.
    destruct (Hexits k vs hp H) as (vs' & hp' & H' & Hs & Hd).
    exists vs', hp'. split; [ exact (proj2 (H2 _) H') | ].
    split; assumption.
  - intros b Hnot H. apply (proj1 (H2 _)) in H.
    destruct (Hends b Hnot H) as [Hw | (k & vs & hp & He)].
    + left. exact (proj2 (H1 _) Hw).
    + right. exists k, vs, hp. exact (proj2 (H1 _) He).
Qed.

(* ======================================================================== *)
(* Observers                                                                *)
(* ======================================================================== *)

Theorem deleted_code_no_observer : deleted_code_no_observer_statement.
Proof. repeat split. Qed.

(* What a continuation stands for in an environment of observers. *)
Lemma observers_resolve (slots : list value_slot) (conts : cont_env)
    (k : continuation) :
  observers slots conts -> observer slots (resolve k conts).
Proof.
  intros Hconts. unfold resolve.
  destruct (lookup k conts) as [c | ] eqn:Hlookup; [ | exact I ].
  apply lookup_in in Hlookup. unfold observers in Hconts.
  rewrite Forall_forall in Hconts. exact (Hconts (k, c) Hlookup).
Qed.

Theorem worlds_observed_way_out : worlds_observed_way_out_statement.
Proof.
  intros slots w w' [Hk Hobservers]. split; [ exact Hk | ].
  destruct (Hobservers (Outer (exit_cont w)) I) as [Hexits _].
  destruct (Hexits (exit_cont w) (exit_values w) (exit_heap w) eq_refl)
    as (vs' & hp' & Hexit & Hscalars & Hdomain).
  simpl in Hexit. injection Hexit as <- <-.
  split; assumption.
Qed.

(* ======================================================================== *)
(* The form in which a pass proves it                                       *)
(* ======================================================================== *)

Theorem expr_refines_under_observers :
  expr_refines_under_observers_statement.
Proof.
  intros slots statics hp source target Hrefines conts _.
  destruct (Hrefines [] conts statics hp) as [Hexits Hends]. split.
  - intros k vs hp' Hsource. exists vs, hp'.
    split; [ exact (Hexits k vs hp' Hsource) | ].
    split; [ apply same_scalars_refl | reflexivity ].
  - intros b Hnot Htarget.
    destruct (Hends b Hnot Htarget) as [Hsource | Hwrong];
      [ | left; exact Hwrong ].
    destruct b as [k vs hp' | | ];
      [ right; exists k, vs, hp'; exact Hsource | left; exact Hsource
      | contradiction Hnot; reflexivity ].
Qed.

Theorem refines_under_observers_trans :
  refines_under_observers_trans_statement.
Proof.
  intros slots statics hp e1 e2 e3 H12 H23 conts Hconts.
  exact (observed_refines_trans _ _ _ (H12 conts Hconts) (H23 conts Hconts)).
Qed.

(* ======================================================================== *)
(* The two forms                                                            *)
(* ======================================================================== *)

(* The behaviours of a unit run from a continuation environment, by the
   world that the unit leaves on its own. *)
Lemma under_world (conts : cont_env) (e : expr) (statics : static_env)
    (hp : heap) (w : exit_world) (b : behaviour) :
  code_closed e = true ->
  static_code_closed statics ->
  exits_world (State e [] [] statics hp) w ->
  step_result_behaves (Step (State e [] conts statics hp)) b
  <-> step_result_behaves
        (apply_cont_value (resolve (exit_cont w) conts) (exit_values w)
           (exit_statics w) (exit_heap w))
        b.
Proof.
  intros Hcode Hstatics Hw.
  pose proof (behaves_under conts e [] statics hp Hcode Hstatics) as H.
  cbv zeta in H. destruct H as [H _]. exact (H w b Hw).
Qed.

Lemma under_wrong (conts : cont_env) (e : expr) (statics : static_env)
    (hp : heap) :
  code_closed e = true ->
  static_code_closed statics ->
  behaves (State e [] [] statics hp) Goes_wrong ->
  behaves (State e [] conts statics hp) Goes_wrong.
Proof.
  intros Hcode Hstatics.
  pose proof (behaves_under conts e [] statics hp Hcode Hstatics) as H.
  cbv zeta in H. destruct H as (_ & H & _). exact H.
Qed.

(* The run from a continuation environment ends only if the unit on its
   own exits or goes wrong. *)
Lemma under_ends (conts : cont_env) (e : expr) (statics : static_env)
    (hp : heap) (b : behaviour) :
  code_closed e = true ->
  static_code_closed statics ->
  b <> Diverges ->
  behaves (State e [] conts statics hp) b ->
  behaves (State e [] [] statics hp) Goes_wrong
  ∨ ∃ w : exit_world, exits_world (State e [] [] statics hp) w.
Proof.
  intros Hcode Hstatics Hnot Hb.
  destruct (behaves_ended _ b Hnot Hb) as [n Hended].
  destruct (run n (State e [] [] statics hp)) as [s | k vs hp' | ] eqn:Hrun.
  - destruct (run_under conts e [] statics hp n s Hcode Hstatics Hrun)
      as (s' & Hrun' & _).
    rewrite Hrun' in Hended. destruct b; contradiction.
  - right.
    destruct
      (proj1 (exits_world_behaves _ k vs hp') (ex_intro _ n Hrun))
      as [statics' Hw].
    exists (Exit_world k vs statics' hp'). exact Hw.
  - left. exists n. exact Hrun.
Qed.

(* Two units that leave worlds which no observer tells apart are
   related from every continuation environment of observers. *)
Lemma worlds_under (slots : list value_slot) (conts : cont_env)
    (statics : static_env) (hp : heap) (source target : expr)
    (w w' : exit_world) :
  code_closed source = true ->
  code_closed target = true ->
  static_code_closed statics ->
  observers slots conts ->
  exits_world (State source [] [] statics hp) w ->
  exits_world (State target [] [] statics hp) w' ->
  worlds_observed slots w w' ->
  observed_refines (Step (State source [] conts statics hp))
    (Step (State target [] conts statics hp)).
Proof.
  intros Hsource Htarget Hstatics Hconts Hw Hw' [Hk Hworlds].
  refine
    (observed_refines_ext _ _ _ _ _ _
       (Hworlds _ (observers_resolve slots conts (exit_cont w) Hconts))).
  - intros b. exact (under_world conts source statics hp w b Hsource
                       Hstatics Hw).
  - intros b. rewrite Hk.
    exact (under_world conts target statics hp w' b Htarget Hstatics Hw').
Qed.

Theorem under_observers_worlds : under_observers_worlds_statement.
Proof.
  intros slots statics hp source target Hsource Htarget Hstatics. split.
  - (* From every environment of observers to the worlds. *)
    intros Hunder.
    destruct (Hunder [] (Forall_nil _)) as [Hexits0 Hends0]. split.
    + intros w Hw.
      destruct (Hexits0 _ _ _ (exits_world_exits _ w Hw))
        as (vs' & hp' & Hexit' & _ & _).
      destruct (proj1 (exits_world_behaves _ _ _ _) Hexit')
        as [statics' Hw'].
      exists (Exit_world (exit_cont w) vs' statics' hp').
      split; [ exact Hw' | ]. split; [ reflexivity | ].
      intros c Hc.
      assert (Hconts : observers slots [(exit_cont w, c)])
        by (apply Forall_cons; [ exact Hc | apply Forall_nil ]).
      refine (observed_refines_ext _ _ _ _ _ _ (Hunder _ Hconts)).
      * intros b. symmetry.
        rewrite (under_world [(exit_cont w, c)] source statics hp w b
                   Hsource Hstatics Hw).
        rewrite resolve_head. reflexivity.
      * intros b. symmetry.
        rewrite (under_world [(exit_cont w, c)] target statics hp _ b
                   Htarget Hstatics Hw').
        cbn [exit_cont exit_values exit_statics exit_heap].
        rewrite resolve_head. reflexivity.
    + intros b Hnot Hb.
      destruct (Hends0 b Hnot Hb) as [Hwrong | (k & vs & hp' & Hexit)];
        [ left; exact Hwrong | right ].
      destruct (proj1 (exits_world_behaves _ _ _ _) Hexit) as [statics' Hw].
      exists (Exit_world k vs statics' hp'). exact Hw.
  - (* From the worlds to every environment of observers. *)
    intros [Hexits Hends] conts Hconts.
    assert (Hfrom :
      ∀ w : exit_world,
        exits_world (State source [] [] statics hp) w ->
        observed_refines (Step (State source [] conts statics hp))
          (Step (State target [] conts statics hp))).
    { intros w Hw. destruct (Hexits w Hw) as (w' & Hw' & Hworlds).
      exact (worlds_under slots conts statics hp source target w w' Hsource
               Htarget Hstatics Hconts Hw Hw' Hworlds). }
    split.
    + intros k vs hp' HS.
      destruct
        (under_ends conts source statics hp (Exits k vs hp') Hsource
           Hstatics ltac:(discriminate) HS)
        as [Hwrong | [w Hw]].
      * pose proof (under_wrong conts source statics hp Hsource Hstatics
                      Hwrong) as Hwrong'.
        pose proof (behaviour_unique _ _ _ HS Hwrong') as Habsurd.
        discriminate Habsurd.
      * exact (proj1 (Hfrom w Hw) k vs hp' HS).
    + intros b Hnot HT.
      assert (Halone :
        behaves (State source [] [] statics hp) Goes_wrong
        ∨ ∃ w : exit_world, exits_world (State source [] [] statics hp) w).
      { destruct
          (under_ends conts target statics hp b Htarget Hstatics Hnot HT)
          as [Hwrong | [w' Hw']].
        - exact (Hends Goes_wrong ltac:(discriminate) Hwrong).
        - exact (Hends
                   (Exits (exit_cont w') (exit_values w') (exit_heap w'))
                   ltac:(discriminate) (exits_world_exits _ w' Hw')). }
      destruct Halone as [Hwrong | [w Hw]].
      * left.
        exact (under_wrong conts source statics hp Hsource Hstatics Hwrong).
      * exact (proj2 (Hfrom w Hw) b Hnot HT).
Qed.
