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

(* Lemmas about the finite maps and the sets of names of FlambdaMapSpec.v,
   and the proofs of its statements. Nothing here needs review.

   A lemma about [lookup], [among] or another operation of
   FlambdaMapSpec.v that does not mention the terms or the machine goes
   here, so that there is one place to look. *)

From Stdlib Require Import PArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaMapSpec.
Import ListNotations.

(* ======================================================================== *)
(* Sets of names                                                            *)
(* ======================================================================== *)

Lemma among_In (name : positive) (names : list positive) :
  among name names = true <-> name ∈ names.
Proof.
  unfold among. rewrite existsb_exists. split.
  - intros [x [Hin Heq]]. apply Pos.eqb_eq in Heq. subst x. exact Hin.
  - intros Hin. exists name. split; [ exact Hin | apply Pos.eqb_refl ].
Qed.

Lemma among_cons (name first : positive) (names : list positive) :
  among name (first :: names) = Pos.eqb name first || among name names.
Proof. reflexivity. Qed.

Lemma among_app (name : positive) (names names' : list positive) :
  among name (names ++ names') = among name names || among name names'.
Proof. apply existsb_app. Qed.

(* The names of a filtered list are those the filter keeps. *)
Lemma among_filter (keep : positive -> bool) (name : positive)
    (names : list positive) :
  among name (filter keep names) = among name names && keep name.
Proof.
  unfold among.
  induction names as [ | first names IH]; simpl; [ reflexivity | ].
  destruct (keep first) eqn:Hkeep; simpl; rewrite IH;
    destruct (Pos.eqb_spec name first) as [-> | _]; simpl;
    rewrite ?Hkeep, ?andb_false_r; reflexivity.
Qed.

Theorem among_without : among_without_statement.
Proof. intros name bound names. apply among_filter. Qed.

Theorem among_inter : among_inter_statement.
Proof. intros name names names'. apply among_filter. Qed.

Theorem all_among : all_among_statement.
Proof.
  intros names allowed. unfold FlambdaMapSpec.all_among.
  rewrite forallb_forall. split.
  - intros Hall name Hin. apply Hall, among_In, Hin.
  - intros Hall name Hin. apply Hall, among_In, Hin.
Qed.

Lemma distinct_NoDup (names : list positive) :
  distinct names = true <-> NoDup names.
Proof.
  induction names as [ | n names IH]; simpl.
  - split; [ intros _; apply NoDup_nil | reflexivity ].
  - rewrite andb_true_iff, negb_true_iff, IH. split.
    + intros [Hn Hd]. apply NoDup_cons; [ | exact Hd ].
      intros Hin. apply among_In in Hin. congruence.
    + intros H. inversion H as [ | ? ? Hn Hd]. subst.
      split; [ | exact Hd ].
      destruct (among n names) eqn:Hamong; [ | reflexivity ].
      apply among_In in Hamong. contradiction.
Qed.

(* Filtering keeps a list without repetition so. *)
Lemma distinct_filter (keep : positive -> bool) (names : list positive) :
  distinct names = true -> distinct (filter keep names) = true.
Proof.
  induction names as [ | first names IH]; simpl; [ reflexivity | ].
  intros Hdistinct. apply andb_true_iff in Hdistinct as [Hfirst Hrest].
  destruct (keep first); simpl; [ | exact (IH Hrest) ].
  rewrite among_filter, (IH Hrest).
  apply negb_true_iff in Hfirst. rewrite Hfirst. reflexivity.
Qed.

Theorem among_dedup : among_dedup_statement.
Proof.
  intros name names.
  induction names as [ | first names IH]; [ reflexivity | ].
  cbn [dedup]. rewrite !among_cons, among_without, IH.
  cbn [among existsb]. destruct (Pos.eqb name first); simpl;
    [ reflexivity | apply andb_true_r ].
Qed.

Theorem dedup_distinct : dedup_distinct_statement.
Proof.
  intros names. induction names as [ | first names IH]; [ reflexivity | ].
  cbn [dedup distinct]. rewrite among_without. cbn [among existsb].
  rewrite Pos.eqb_refl, andb_false_r. simpl.
  apply distinct_filter, IH.
Qed.

Lemma same_names_refl (names : list positive) : same_names names names.
Proof. intros name. reflexivity. Qed.

Lemma same_names_sym (names names' : list positive) :
  same_names names names' -> same_names names' names.
Proof. intros Hsame name. symmetry. apply Hsame. Qed.

Lemma same_names_trans (names names' names'' : list positive) :
  same_names names names' -> same_names names' names'' ->
  same_names names names''.
Proof. intros H H' name. rewrite (H name). apply H'. Qed.

Lemma dedup_same_names (names : list positive) :
  same_names (dedup names) names.
Proof. intros name. apply among_dedup. Qed.

(* ======================================================================== *)
(* Lookups                                                                  *)
(* ======================================================================== *)

Lemma lookup_cons {A : Type} (name bound : positive) (a : A)
    (bindings : list (positive * A)) :
  lookup name ((bound, a) :: bindings)
  = if Pos.eqb name bound then Some a else lookup name bindings.
Proof. reflexivity. Qed.

(* The binding just added is the one found. *)
Lemma lookup_head {A : Type} (name : positive) (a : A)
    (bindings : list (positive * A)) :
  lookup name ((name, a) :: bindings) = Some a.
Proof. simpl. rewrite Pos.eqb_refl. reflexivity. Qed.

(* A binding of another name changes nothing. *)
Lemma lookup_other {A : Type} (name bound : positive) (a : A)
    (bindings : list (positive * A)) :
  name <> bound -> lookup name ((bound, a) :: bindings) = lookup name bindings.
Proof.
  intros Hne. simpl.
  destruct (Pos.eqb_spec name bound); [ contradiction | reflexivity ].
Qed.

(* A binding added for a name that was not bound. *)
Lemma lookup_fresh {A : Type} (name fresh : positive) (a added : A)
    (bindings : list (positive * A)) :
  lookup fresh bindings = None ->
  lookup name bindings = Some a ->
  lookup name ((fresh, added) :: bindings) = Some a.
Proof.
  intros Hfresh Hname. simpl.
  destruct (Pos.eqb_spec name fresh) as [-> | _]; [ congruence | exact Hname ].
Qed.

Lemma lookup_app {A : Type} (name : positive)
    (bindings bindings' : list (positive * A)) :
  lookup name (bindings ++ bindings')
  = match lookup name bindings with
    | Some a => Some a
    | None => lookup name bindings'
    end.
Proof.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ reflexivity | ].
  destruct (Pos.eqb name bound); [ reflexivity | exact IH ].
Qed.

(* What is found is one of the bindings. *)
Lemma lookup_in {A : Type} (name : positive) (a : A)
    (bindings : list (positive * A)) :
  lookup name bindings = Some a -> (name, a) ∈ bindings.
Proof.
  induction bindings as [ | [bound b] bindings IH]; simpl; [ discriminate | ].
  destruct (Pos.eqb_spec name bound) as [-> | _].
  - intros [= ->]. left. reflexivity.
  - intros Hlookup. right. exact (IH Hlookup).
Qed.

Lemma lookup_none_not_in {A : Type} (name : positive)
    (bindings : list (positive * A)) :
  lookup name bindings = None -> name ∉ map fst bindings.
Proof.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ auto | ].
  destruct (Pos.eqb_spec name bound) as [-> | Hne]; [ discriminate | ].
  intros Hlookup [Heq | Hin]; [ congruence | exact (IH Hlookup Hin) ].
Qed.

(* What holds of every binding holds of the one found. *)
Lemma lookup_forallb {A : Type} (f : A -> bool) (name : positive) (a : A)
    (bindings : list (positive * A)) :
  forallb (fun '(_, a) => f a) bindings = true ->
  lookup name bindings = Some a -> f a = true.
Proof.
  induction bindings as [ | [bound b] bindings IH]; simpl; [ discriminate | ].
  intros Hall. apply andb_true_iff in Hall as [Hb Hrest].
  destruct (Pos.eqb name bound); [ intros [= <-]; exact Hb | exact (IH Hrest) ].
Qed.

(* A name is bound when it is among the names of the bindings. *)
Lemma is_bound_among {A : Type} (name : positive) (bindings : finite_map A) :
  is_bound name bindings = among name (map fst bindings).
Proof.
  unfold is_bound, among.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ reflexivity | ].
  destruct (Pos.eqb name bound); [ reflexivity | exact IH ].
Qed.

Lemma is_bound_lookup {A : Type} (name : positive) (bindings : finite_map A) :
  is_bound name bindings = true <-> ∃ a : A, lookup name bindings = Some a.
Proof.
  unfold is_bound. destruct (lookup name bindings) as [a | ]; split.
  - intros _. exists a. reflexivity.
  - reflexivity.
  - discriminate.
  - intros [a [=]].
Qed.

(* ======================================================================== *)
(* The operations on maps                                                   *)
(* ======================================================================== *)

Theorem lookup_unbind : lookup_unbind_statement.
Proof.
  intros A name removed bindings. unfold unbind.
  induction bindings as [ | [bound a] bindings IH]; simpl.
  - destruct (Pos.eqb name removed); reflexivity.
  - destruct (Pos.eqb_spec removed bound) as [<- | Hne]; simpl; rewrite IH.
    + destruct (Pos.eqb name removed); reflexivity.
    + destruct (Pos.eqb_spec name bound) as [-> | _]; [ | reflexivity ].
      destruct (Pos.eqb_spec bound removed); [ congruence | reflexivity ].
Qed.

Theorem lookup_map_values : lookup_map_values_statement.
Proof.
  intros A B f name bindings. unfold map_values.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ reflexivity | ].
  destruct (Pos.eqb name bound); [ reflexivity | exact IH ].
Qed.

Theorem among_domain : among_domain_statement.
Proof.
  intros A name bindings. unfold domain.
  rewrite among_dedup, is_bound_among. reflexivity.
Qed.

Theorem domain_distinct : domain_distinct_statement.
Proof. intros A bindings. apply dedup_distinct. Qed.

Theorem lookup_tabulate : lookup_tabulate_statement.
Proof.
  intros A f name names. unfold tabulate, among.
  induction names as [ | first names IH]; simpl; [ reflexivity | ].
  destruct (f first) as [a | ] eqn:Hfirst; simpl;
    destruct (Pos.eqb_spec name first) as [-> | _]; simpl;
    try exact IH.
  - symmetry. exact Hfirst.
  - rewrite IH, Hfirst.
    destruct (existsb (Pos.eqb first) names); reflexivity.
Qed.

(* The names a tabulated map binds are those of the list for which the
   function gives something, in the order of the list. *)
Lemma tabulate_names {A : Type} (f : positive -> option A)
    (names : list positive) :
  map fst (tabulate f names)
  = filter
      (fun name =>
         match f name with
         | Some _ => true
         | None => false
         end)
      names.
Proof.
  unfold tabulate.
  induction names as [ | first names IH]; simpl; [ reflexivity | ].
  destruct (f first); simpl; rewrite IH; reflexivity.
Qed.

Lemma tabulate_distinct {A : Type} (f : positive -> option A)
    (names : list positive) :
  distinct names = true -> distinct (map fst (tabulate f names)) = true.
Proof. rewrite tabulate_names. apply distinct_filter. Qed.

Theorem lookup_compact : lookup_compact_statement.
Proof.
  intros A name bindings. unfold compact.
  rewrite lookup_tabulate, among_domain. unfold is_bound.
  destruct (lookup name bindings); reflexivity.
Qed.

Theorem compact_distinct : compact_distinct_statement.
Proof.
  intros A bindings. apply tabulate_distinct, domain_distinct.
Qed.

(* The bindings of the compact map are the ones [lookup] finds. *)
Lemma in_compact {A : Type} (name : positive) (a : A)
    (bindings : finite_map A) :
  (name, a) ∈ compact bindings <-> lookup name bindings = Some a.
Proof.
  split.
  - unfold compact, tabulate. rewrite in_flat_map.
    intros (bound & _ & Hin).
    destruct (lookup bound bindings) as [b | ] eqn:Hlookup;
      [ | contradiction ].
    destruct Hin as [[= -> ->] | []]. exact Hlookup.
  - intros Hlookup. apply lookup_in. rewrite lookup_compact. exact Hlookup.
Qed.

Theorem lookup_filter_bindings : lookup_filter_bindings_statement.
Proof.
  intros A keep name bindings. unfold filter_bindings.
  rewrite lookup_tabulate, among_domain. unfold is_bound.
  destruct (lookup name bindings); reflexivity.
Qed.

Theorem lookup_merge : lookup_merge_statement.
Proof.
  intros A B C f name bindings bindings' Hnone. unfold merge.
  rewrite lookup_tabulate, among_dedup, among_app, <- !is_bound_among.
  unfold is_bound.
  destruct (lookup name bindings), (lookup name bindings'); simpl;
    try reflexivity.
  symmetry. exact Hnone.
Qed.

Theorem lookup_union_with : lookup_union_with_statement.
Proof.
  intros A f name bindings bindings'. unfold union_with.
  rewrite lookup_merge; reflexivity.
Qed.

Theorem lookup_inter_with : lookup_inter_with_statement.
Proof.
  intros A B C f name bindings bindings'. unfold inter_with.
  rewrite lookup_merge; reflexivity.
Qed.

(* ======================================================================== *)
(* Maps that are the same, and maps that are included                       *)
(* ======================================================================== *)

Lemma map_equal_refl {A : Type} (bindings : finite_map A) :
  map_equal bindings bindings.
Proof. intros name. reflexivity. Qed.

Lemma map_equal_sym {A : Type} (bindings bindings' : finite_map A) :
  map_equal bindings bindings' -> map_equal bindings' bindings.
Proof. intros Hequal name. symmetry. apply Hequal. Qed.

Lemma map_equal_trans {A : Type}
    (bindings bindings' bindings'' : finite_map A) :
  map_equal bindings bindings' -> map_equal bindings' bindings'' ->
  map_equal bindings bindings''.
Proof. intros H H' name. rewrite (H name). apply H'. Qed.

Lemma compact_map_equal {A : Type} (bindings : finite_map A) :
  map_equal (compact bindings) bindings.
Proof. intros name. apply lookup_compact. Qed.

Lemma map_included_refl {A : Type} (bindings : finite_map A) :
  map_included bindings bindings.
Proof. intros name a Hlookup. exact Hlookup. Qed.

Lemma map_included_trans {A : Type}
    (bindings bindings' bindings'' : finite_map A) :
  map_included bindings bindings' -> map_included bindings' bindings'' ->
  map_included bindings bindings''.
Proof. intros H H' name a Hlookup. apply H', H, Hlookup. Qed.

(* Two maps are the same when each is included in the other. *)
Lemma map_equal_included {A : Type} (bindings bindings' : finite_map A) :
  map_equal bindings bindings'
  <-> map_included bindings bindings' ∧ map_included bindings' bindings.
Proof.
  split.
  - intros Hequal. split; intros name a Hlookup.
    + rewrite <- (Hequal name). exact Hlookup.
    + rewrite (Hequal name). exact Hlookup.
  - intros [Hincluded Hincluded'] name.
    destruct (lookup name bindings) as [a | ] eqn:Hlookup.
    + symmetry. exact (Hincluded name a Hlookup).
    + destruct (lookup name bindings') as [a' | ] eqn:Hlookup';
        [ | reflexivity ].
      rewrite (Hincluded' name a' Hlookup') in Hlookup. discriminate.
Qed.

(* A binding added for a name that was not bound includes what was. *)
Lemma map_included_fresh {A : Type} (fresh : positive) (added : A)
    (bindings : finite_map A) :
  lookup fresh bindings = None ->
  map_included bindings ((fresh, added) :: bindings).
Proof.
  intros Hfresh name a Hlookup.
  exact (lookup_fresh name fresh a added bindings Hfresh Hlookup).
Qed.

(* The operations give the same map on maps that are the same. *)
Lemma unbind_map_equal {A : Type} (name : positive)
    (bindings bindings' : finite_map A) :
  map_equal bindings bindings' ->
  map_equal (unbind name bindings) (unbind name bindings').
Proof.
  intros Hequal other. rewrite !lookup_unbind, (Hequal other). reflexivity.
Qed.

Lemma map_values_map_equal {A B : Type} (f : A -> B)
    (bindings bindings' : finite_map A) :
  map_equal bindings bindings' ->
  map_equal (map_values f bindings) (map_values f bindings').
Proof.
  intros Hequal name. rewrite !lookup_map_values, (Hequal name). reflexivity.
Qed.

Lemma merge_map_equal {A B C : Type} (f : option A -> option B -> option C)
    (left left' : finite_map A) (right right' : finite_map B) :
  f None None = None ->
  map_equal left left' -> map_equal right right' ->
  map_equal (merge f left right) (merge f left' right').
Proof.
  intros Hnone Hleft Hright name.
  rewrite !lookup_merge, (Hleft name), (Hright name); auto.
Qed.
