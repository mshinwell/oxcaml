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

(* Proofs of the statements of FlambdaFreshQuantifierSpec.v. Nothing here
   needs review.

   Each law that needs no support is proved by putting two finite sets
   together, or by taking a name outside one with [fresh_name]. Each law
   that needs a support goes through the agreement of the three readings
   ([some_any]), whose proof is one swap: a name outside the support at
   which the predicate holds is exchanged for any other name outside
   it. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaMapSpec FlambdaMapProofs
  FlambdaNominalSpec FlambdaNameAbstractionSpec
  FlambdaNameAbstractionProofs FlambdaFreshQuantifierSpec.
Import ListNotations.
Import Nominal.

(* ======================================================================== *)
(* Names outside a list                                                     *)
(* ======================================================================== *)

Lemma among_app_false (name : positive) (names names' : list positive) :
  among name (names ++ names') = false
  <-> among name names = false ∧ among name names' = false.
Proof. rewrite among_app. apply orb_false_iff. Qed.

Lemma among_cons_false (name first : positive) (names : list positive) :
  among name (first :: names) = false
  <-> name <> first ∧ among name names = false.
Proof. rewrite among_cons, orb_false_iff, Pos.eqb_neq. reflexivity. Qed.

Lemma swap_second (a b : positive) : swap a b b = a.
Proof.
  unfold swap. destruct (Pos.eqb_spec b a) as [-> | _]; [ reflexivity | ].
  rewrite Pos.eqb_refl. reflexivity.
Qed.

(* A swap of two names outside a list moves none of its names. *)
Lemma fixes_swap (a b : positive) (names : list positive) :
  among a names = false -> among b names = false -> fixes [(a, b)] names.
Proof.
  intros Ha Hb name Hname. simpl. apply swap_other; intros ->; congruence.
Qed.

(* ======================================================================== *)
(* The quantifier                                                           *)
(* ======================================================================== *)

Theorem for_fresh_intro : for_fresh_intro_statement.
Proof. intros P avoid Hall. exists avoid. exact Hall. Qed.

Theorem for_fresh_elim : for_fresh_elim_statement.
Proof.
  intros P names [avoid Hall]. exists (fresh_name (avoid ++ names)).
  pose proof (fresh_name_fresh (avoid ++ names)) as Hfresh.
  apply among_app_false in Hfresh as [Havoid Hnames].
  split; [ exact Hnames | exact (Hall _ Havoid) ].
Qed.

Theorem for_fresh_mono : for_fresh_mono_statement.
Proof.
  intros P Q [avoid Himpl] [avoid' Hall]. exists (avoid ++ avoid').
  intros name Hname. apply among_app_false in Hname as [Hname Hname'].
  exact (Himpl name Hname (Hall name Hname')).
Qed.

(* The form in which monotonicity is used most. *)
Lemma for_fresh_weaken (P Q : positive -> Prop) :
  (∀ name : positive, P name -> Q name) ->
  (И name, P name) -> И name, Q name.
Proof.
  intros Himpl [avoid Hall]. exists avoid. intros name Hname.
  exact (Himpl name (Hall name Hname)).
Qed.

(* ======================================================================== *)
(* The connectives, for any predicate                                       *)
(* ======================================================================== *)

Theorem for_fresh_and : for_fresh_and_statement.
Proof.
  intros P Q. split.
  - intros Hboth.
    split; [ apply (for_fresh_weaken _ P) in Hboth
           | apply (for_fresh_weaken _ Q) in Hboth ];
      solve [ exact Hboth | intros name [HP HQ]; assumption ].
  - intros [[avoid HP] [avoid' HQ]]. exists (avoid ++ avoid').
    intros name Hname. apply among_app_false in Hname as [Hname Hname'].
    split; [ exact (HP name Hname) | exact (HQ name Hname') ].
Qed.

Theorem for_fresh_constant : for_fresh_constant_statement.
Proof.
  intros Q. split.
  - intros Hfresh.
    destruct (for_fresh_elim (fun _ => Q) [] Hfresh) as (_ & _ & HQ).
    exact HQ.
  - intros HQ. exists []. intros _ _. exact HQ.
Qed.

Theorem for_fresh_or_of_either : for_fresh_or_of_either_statement.
Proof.
  intros P Q [HP | HQ];
    [ apply (for_fresh_weaken P) | apply (for_fresh_weaken Q) ];
    auto.
Qed.

Theorem for_fresh_not_gives_not : for_fresh_not_gives_not_statement.
Proof.
  intros P Hnot HP. apply (for_fresh_constant False).
  apply (for_fresh_mono P); [ | exact HP ].
  apply (for_fresh_weaken (fun name => ~ P name)); [ | exact Hnot ].
  intros name HnotP HPname. exact (HnotP HPname).
Qed.

Theorem for_fresh_forall : for_fresh_forall_statement.
Proof.
  intros X P Hall x.
  apply (for_fresh_weaken (fun name => ∀ x : X, P name x)); [ | exact Hall ].
  intros name Hname. exact (Hname x).
Qed.

Theorem for_fresh_exists : for_fresh_exists_statement.
Proof.
  intros X P [x Hx].
  apply (for_fresh_weaken (fun name => P name x)); [ | exact Hx ].
  intros name Hname. exists x. exact Hname.
Qed.

Theorem for_fresh_avoids : for_fresh_avoids_statement.
Proof. intros names. exists names. intros name Hname. exact Hname. Qed.

Theorem for_fresh_distinct : for_fresh_distinct_statement.
Proof.
  exists []. intros a _. exists [a]. intros b Hb.
  apply among_cons_false in Hb as [Hb _]. intros ->. exact (Hb eq_refl).
Qed.

(* ======================================================================== *)
(* Predicates with a support                                                *)
(* ======================================================================== *)

(* A predicate that holds of one name outside its support holds of every
   other: exchange the two. *)
Lemma supported_some_any (support : list positive) (P : positive -> Prop)
    (a b : positive) :
  supports single_name support P ->
  among a support = false ->
  among b support = false ->
  P a -> P b.
Proof.
  intros Hsupports Ha Hb HP.
  pose proof (Hsupports [(a, b)] a (fixes_swap a b support Ha Hb) HP)
    as Hmoved.
  simpl in Hmoved. rewrite swap_first in Hmoved. exact Hmoved.
Qed.

Lemma supported_any (support : list positive) (P : positive -> Prop) :
  supports single_name support P ->
  (И name, P name) ->
  ∀ name : positive, among name support = false -> P name.
Proof.
  intros Hsupports Hfresh name Hname.
  destruct (for_fresh_elim P support Hfresh) as (witness & Hwitness & HP).
  exact (supported_some_any support P witness name Hsupports Hwitness Hname
           HP).
Qed.

Lemma supported_some (support : list positive) (P : positive -> Prop)
    (witness : positive) :
  supports single_name support P ->
  among witness support = false ->
  P witness ->
  И name, P name.
Proof.
  intros Hsupports Hwitness HP. exists support. intros name Hname.
  exact (supported_some_any support P witness name Hsupports Hwitness Hname
           HP).
Qed.

Theorem some_any : some_any_statement.
Proof.
  intros support P Hsupports. split; split.
  - apply supported_any, Hsupports.
  - intros Hall. exists support. exact Hall.
  - apply for_fresh_elim.
  - intros (witness & Hwitness & HP).
    exact (supported_some support P witness Hsupports Hwitness HP).
Qed.

Theorem for_fresh_or : for_fresh_or_statement.
Proof.
  intros support support' P Q HsupportsP HsupportsQ.
  split; [ | apply for_fresh_or_of_either ].
  intros Heither.
  destruct
    (for_fresh_elim (fun name => P name ∨ Q name) (support ++ support')
       Heither)
    as (witness & Hwitness & [HP | HQ]);
    apply among_app_false in Hwitness as [Hwitness Hwitness'].
  - left. exact (supported_some support P witness HsupportsP Hwitness HP).
  - right. exact (supported_some support' Q witness HsupportsQ Hwitness' HQ).
Qed.

Theorem for_fresh_not : for_fresh_not_statement.
Proof.
  intros support P Hsupports. split; [ apply for_fresh_not_gives_not | ].
  intros Hnot. exists support. intros name Hname HP. apply Hnot.
  exact (supported_some support P name Hsupports Hname HP).
Qed.

Theorem for_fresh_impl : for_fresh_impl_statement.
Proof.
  intros support support' P Q HsupportsP HsupportsQ.
  split; [ apply for_fresh_mono | ].
  intros Himpl. exists (support ++ support'). intros name Hname HP.
  apply among_app_false in Hname as [Hname Hname'].
  apply (supported_any support' Q HsupportsQ); [ | exact Hname' ].
  apply Himpl. exact (supported_some support P name HsupportsP Hname HP).
Qed.

(* Two fresh names at which the predicate holds are carried to any two
   different names outside the support by two swaps. *)
Lemma supported_two (support : list positive)
    (P : positive * positive -> Prop) :
  supports (pair_names single_name single_name) support P ->
  ((И a b, P (a, b))
   <-> (∀ a b : positive,
         among a support = false -> among b support = false -> a <> b ->
         P (a, b))).
Proof.
  intros Hsupports. split.
  - intros Hfresh a b Ha Hb Hdifferent.
    destruct
      (for_fresh_elim (fun a => И b, P (a, b)) (a :: b :: support) Hfresh)
      as (a' & Ha' & Hfresh').
    destruct
      (for_fresh_elim (fun b => P (a', b)) (a :: b :: a' :: support) Hfresh')
      as (b' & Hb' & HP).
    apply among_cons_false in Ha' as [Ha'_a Ha'].
    apply among_cons_false in Ha' as [Ha'_b Ha'].
    apply among_cons_false in Hb' as [Hb'_a Hb'].
    apply among_cons_false in Hb' as [Hb'_b Hb'].
    apply among_cons_false in Hb' as [Hb'_a' Hb'].
    assert (Hfixes : fixes [(a, a'); (b, b')] support).
    { intros name Hname. simpl.
      rewrite (swap_other b b'), (swap_other a a');
        solve [ reflexivity | intros ->; congruence ]. }
    pose proof (Hsupports _ _ Hfixes HP) as Hmoved. simpl in Hmoved.
    rewrite (swap_other b b' a'), (swap_second a a'), (swap_second b b'),
      (swap_other a a' b) in Hmoved;
      solve [ exact Hmoved | congruence ].
  - intros Hany. exists support. intros a Ha. exists (a :: support).
    intros b Hb. apply among_cons_false in Hb as [Hdifferent Hb].
    apply Hany; [ exact Ha | exact Hb | congruence ].
Qed.

Theorem for_fresh_two : for_fresh_two_statement.
Proof. exact supported_two. Qed.

Theorem for_fresh_swap : for_fresh_swap_statement.
Proof.
  intros support P Hsupports.
  rewrite (supported_two support P Hsupports).
  assert (Hsupports' :
    supports (pair_names single_name single_name) support
      (fun ba => P (snd ba, fst ba))).
  { intros p [b a] Hfixes HP. exact (Hsupports p (a, b) Hfixes HP). }
  pose proof (supported_two support _ Hsupports') as Hswapped.
  simpl in Hswapped. rewrite Hswapped. split.
  - intros Hany b a Hb Ha Hdifferent. apply Hany; congruence.
  - intros Hany a b Ha Hb Hdifferent. apply Hany; congruence.
Qed.

(* The names up to a given one, for the predicate that looks at their
   order. *)
Definition names_up_to (a : positive) : list positive :=
  map Pos.of_succ_nat (seq 0 (Pos.to_nat a)).

Lemma among_names_up_to (a b : positive) :
  (b <= a)%positive -> among b (names_up_to a) = true.
Proof.
  intros Hle. apply among_In. unfold names_up_to. apply in_map_iff.
  exists (Nat.pred (Pos.to_nat b)). split; [ | apply in_seq; lia ].
  rewrite <- (Pos2Nat.id b) at 2.
  destruct (Pos2Nat.is_succ b) as [n Hn]. rewrite Hn. cbn [Nat.pred].
  apply Pos.of_nat_succ.
Qed.

Theorem for_fresh_swap_needs_support : for_fresh_swap_needs_support_statement.
Proof.
  split.
  - exists []. intros a _. exists (names_up_to a). intros b Hb.
    destruct (Pos.ltb_spec a b) as [Hlt | Hle]; [ exact Hlt | ].
    rewrite (among_names_up_to a b Hle) in Hb. discriminate.
  - intros Hfresh.
    destruct (for_fresh_elim _ [] Hfresh) as (b & _ & Hfresh').
    destruct (for_fresh_elim _ (names_up_to b) Hfresh') as (a & Ha & Hlt).
    rewrite among_names_up_to in Ha; [ discriminate | lia ].
Qed.

(* ======================================================================== *)
(* Equivariant predicates                                                   *)
(* ======================================================================== *)

Theorem propositions_nominal : propositions_nominal_statement.
Proof.
  constructor; simpl; try reflexivity.
  - intros t t' Hequal. symmetry. exact Hequal.
  - intros t t' t'' Hequal Hequal'. rewrite Hequal. exact Hequal'.
  - intros p t t' Hequal. exact Hequal.
  - intros t t' _ name. reflexivity.
Qed.

(* Rename the name and the value together, then put the value back: it
   is equal to its renaming, since the permutation fixes its free
   names. *)
Theorem equivariant_supports : equivariant_supports_statement.
Proof.
  intros X N R x HN Hequivariant Hrespects p name Hfixes HR. simpl.
  apply (Hrespects (permute p name, apply_renaming N p x)).
  - split; [ reflexivity | ]. simpl.
    exact (apply_renaming_fixes N HN p x Hfixes).
  - apply (Hequivariant p (name, x)). exact HR.
Qed.

Theorem some_any_nominal : some_any_nominal_statement.
Proof.
  intros X N R x HN Hequivariant Hrespects.
  exact (some_any (free_names N x) (fun name => R (name, x))
           (equivariant_supports X N R x HN Hequivariant Hrespects)).
Qed.
