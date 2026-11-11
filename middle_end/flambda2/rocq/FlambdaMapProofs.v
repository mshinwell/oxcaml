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

(* ======================================================================== *)
(* Keys of any type                                                         *)
(* ======================================================================== *)

(* What follows is what is above, for the module [Keyed] of
   FlambdaMapSpec.v: the equality test of the keys is an argument, and a
   lemma that depends on it takes a proof that it decides equality. A
   lemma here applies as it stands to a goal about the definitions on
   names, which are those of [Keyed] at [Pos.eqb] by computation
   ([names_are_keys]); give it [Pos.eqb_eq] where it asks for the
   proof, and [Z.eqb_eq] for integers. *)

From Stdlib Require Import ZArith.

Theorem pos_eqb_decides_equality : pos_eqb_decides_equality_statement.
Proof. exact Pos.eqb_eq. Qed.

Theorem z_eqb_decides_equality : z_eqb_decides_equality_statement.
Proof. exact Z.eqb_eq. Qed.

Theorem names_are_keys : names_are_keys_statement.
Proof. repeat split. Qed.

Lemma keyed_eqb_refl {K : Type} (eqb : K -> K -> bool) :
  decides_equality eqb -> ∀ key : K, eqb key key = true.
Proof. intros Heqb key. apply Heqb. reflexivity. Qed.

Lemma keyed_eqb_spec {K : Type} (eqb : K -> K -> bool) :
  decides_equality eqb ->
  ∀ key key' : K, reflect (key = key') (eqb key key').
Proof.
  intros Heqb key key'. destruct (eqb key key') eqn:Htest; constructor.
  - apply Heqb, Htest.
  - intros Heq. apply Heqb in Heq. congruence.
Qed.

(* ------------------------------------------------------------------------ *)
(* Sets of keys                                                             *)
(* ------------------------------------------------------------------------ *)

Theorem keyed_among_in : keyed_among_in_statement.
Proof.
  intros K eqb Heqb key keys. unfold Keyed.among.
  rewrite existsb_exists. split.
  - intros [x [Hin Heq]]. apply Heqb in Heq. subst x. exact Hin.
  - intros Hin. exists key.
    split; [ exact Hin | apply keyed_eqb_refl, Heqb ].
Qed.

Lemma keyed_among_cons {K : Type} (eqb : K -> K -> bool) (key first : K)
    (keys : list K) :
  Keyed.among eqb key (first :: keys)
  = eqb key first || Keyed.among eqb key keys.
Proof. reflexivity. Qed.

Theorem keyed_among_app : keyed_among_app_statement.
Proof. intros K eqb key keys keys'. apply existsb_app. Qed.

(* The keys of a filtered list are those the filter keeps. *)
Lemma keyed_among_filter {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) (keep : K -> bool) (key : K)
    (keys : list K) :
  Keyed.among eqb key (filter keep keys)
  = Keyed.among eqb key keys && keep key.
Proof.
  unfold Keyed.among.
  induction keys as [ | first keys IH]; simpl; [ reflexivity | ].
  destruct (keep first) eqn:Hkeep; simpl; rewrite IH;
    destruct (keyed_eqb_spec eqb Heqb key first) as [-> | _]; simpl;
    rewrite ?Hkeep, ?andb_false_r; reflexivity.
Qed.

Theorem keyed_among_without : keyed_among_without_statement.
Proof.
  intros K eqb Heqb key removed keys. apply (keyed_among_filter eqb Heqb).
Qed.

Theorem keyed_among_inter : keyed_among_inter_statement.
Proof.
  intros K eqb Heqb key keys keys'. apply (keyed_among_filter eqb Heqb).
Qed.

Theorem keyed_all_among : keyed_all_among_statement.
Proof.
  intros K eqb Heqb keys allowed. unfold Keyed.all_among.
  rewrite forallb_forall. split.
  - intros Hall key Hin. apply Hall, (keyed_among_in K eqb Heqb), Hin.
  - intros Hall key Hin. apply Hall, (keyed_among_in K eqb Heqb), Hin.
Qed.

Lemma keyed_distinct_NoDup {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) (keys : list K) :
  Keyed.distinct eqb keys = true <-> NoDup keys.
Proof.
  induction keys as [ | k keys IH]; simpl.
  - split; [ intros _; apply NoDup_nil | reflexivity ].
  - rewrite andb_true_iff, negb_true_iff, IH. split.
    + intros [Hk Hd]. apply NoDup_cons; [ | exact Hd ].
      intros Hin. apply (keyed_among_in K eqb Heqb) in Hin. congruence.
    + intros H. inversion H as [ | ? ? Hk Hd]. subst.
      split; [ | exact Hd ].
      destruct (Keyed.among eqb k keys) eqn:Hamong; [ | reflexivity ].
      apply (keyed_among_in K eqb Heqb) in Hamong. contradiction.
Qed.

(* Filtering keeps a list without repetition so. *)
Lemma keyed_distinct_filter {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) (keep : K -> bool) (keys : list K) :
  Keyed.distinct eqb keys = true ->
  Keyed.distinct eqb (filter keep keys) = true.
Proof.
  induction keys as [ | first keys IH]; simpl; [ reflexivity | ].
  intros Hdistinct. apply andb_true_iff in Hdistinct as [Hfirst Hrest].
  destruct (keep first); simpl; [ | exact (IH Hrest) ].
  rewrite (keyed_among_filter eqb Heqb), (IH Hrest).
  apply negb_true_iff in Hfirst. rewrite Hfirst. reflexivity.
Qed.

Theorem keyed_among_dedup : keyed_among_dedup_statement.
Proof.
  intros K eqb Heqb key keys.
  induction keys as [ | first keys IH]; [ reflexivity | ].
  cbn [Keyed.dedup]. rewrite !keyed_among_cons.
  rewrite (keyed_among_without K eqb Heqb), IH.
  cbn [Keyed.among existsb]. destruct (eqb key first); simpl;
    [ reflexivity | apply andb_true_r ].
Qed.

Theorem keyed_dedup_distinct : keyed_dedup_distinct_statement.
Proof.
  intros K eqb Heqb keys.
  induction keys as [ | first keys IH]; [ reflexivity | ].
  cbn [Keyed.dedup Keyed.distinct].
  rewrite (keyed_among_without K eqb Heqb). cbn [Keyed.among existsb].
  rewrite (keyed_eqb_refl eqb Heqb), andb_false_r. simpl.
  apply (keyed_distinct_filter eqb Heqb), IH.
Qed.

Lemma keyed_same_keys_refl {K : Type} (eqb : K -> K -> bool)
    (keys : list K) :
  Keyed.same_keys eqb keys keys.
Proof. intros key. reflexivity. Qed.

Lemma keyed_same_keys_sym {K : Type} (eqb : K -> K -> bool)
    (keys keys' : list K) :
  Keyed.same_keys eqb keys keys' -> Keyed.same_keys eqb keys' keys.
Proof. intros Hsame key. symmetry. apply Hsame. Qed.

Lemma keyed_same_keys_trans {K : Type} (eqb : K -> K -> bool)
    (keys keys' keys'' : list K) :
  Keyed.same_keys eqb keys keys' -> Keyed.same_keys eqb keys' keys'' ->
  Keyed.same_keys eqb keys keys''.
Proof. intros H H' key. rewrite (H key). apply H'. Qed.

Lemma keyed_dedup_same_keys {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) (keys : list K) :
  Keyed.same_keys eqb (Keyed.dedup eqb keys) keys.
Proof. intros key. apply (keyed_among_dedup K eqb Heqb). Qed.

Theorem keyed_same_keys_b : keyed_same_keys_b_statement.
Proof.
  intros K eqb Heqb keys keys'. unfold Keyed.same_keys_b.
  rewrite andb_true_iff, !(keyed_all_among K eqb Heqb). split.
  - intros [Hsub Hsub'] key.
    destruct (Keyed.among eqb key keys) eqn:Hkey.
    + symmetry. apply Hsub, Hkey.
    + destruct (Keyed.among eqb key keys') eqn:Hkey'; [ | reflexivity ].
      rewrite (Hsub' key Hkey') in Hkey. discriminate.
  - intros Hsame. split; intros key Hkey.
    + rewrite <- (Hsame key). exact Hkey.
    + rewrite (Hsame key). exact Hkey.
Qed.

Theorem keyed_is_empty_among : keyed_is_empty_among_statement.
Proof.
  intros K eqb Heqb [ | first keys]; split; try reflexivity.
  - discriminate.
  - intros Hnone. specialize (Hnone first).
    rewrite keyed_among_cons, (keyed_eqb_refl eqb Heqb) in Hnone.
    discriminate.
Qed.

Theorem keyed_get_singleton : keyed_get_singleton_statement.
Proof.
  intros K eqb Heqb key keys. unfold Keyed.get_singleton.
  pose proof (keyed_dedup_distinct K eqb Heqb keys) as Hdistinct.
  assert (Hsame :
    ∀ key' : K,
      Keyed.among eqb key' keys
      = Keyed.among eqb key' (Keyed.dedup eqb keys)).
  { intros key'. symmetry. apply (keyed_among_dedup K eqb Heqb). }
  destruct (Keyed.dedup eqb keys) as [ | first [ | second rest]].
  - split; [ discriminate | ]. intros Hkeys. specialize (Hkeys key).
    rewrite Hsame, (keyed_eqb_refl eqb Heqb) in Hkeys. discriminate.
  - split.
    + intros [= ->] key'. rewrite Hsame. simpl. apply orb_false_r.
    + intros Hkeys. specialize (Hkeys first).
      rewrite Hsame, keyed_among_cons, (keyed_eqb_refl eqb Heqb) in Hkeys.
      symmetry in Hkeys. apply Heqb in Hkeys. congruence.
  - split; [ discriminate | ]. intros Hkeys. exfalso.
    assert (Hfirst : first = key).
    { apply Heqb. rewrite <- Hkeys, Hsame, keyed_among_cons.
      rewrite (keyed_eqb_refl eqb Heqb). reflexivity. }
    assert (Hsecond : second = key).
    { apply Heqb. rewrite <- Hkeys, Hsame, !keyed_among_cons.
      rewrite (keyed_eqb_refl eqb Heqb). apply orb_true_r. }
    subst first second. simpl in Hdistinct.
    rewrite (keyed_eqb_refl eqb Heqb) in Hdistinct. discriminate.
Qed.

(* ------------------------------------------------------------------------ *)
(* Lookups                                                                  *)
(* ------------------------------------------------------------------------ *)

Lemma keyed_lookup_cons {K : Type} (eqb : K -> K -> bool) {A : Type}
    (key bound : K) (a : A) (bindings : list (K * A)) :
  Keyed.lookup eqb key ((bound, a) :: bindings)
  = if eqb key bound then Some a else Keyed.lookup eqb key bindings.
Proof. reflexivity. Qed.

(* The binding just added is the one found. *)
Lemma keyed_lookup_head {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (key : K) (a : A)
    (bindings : list (K * A)) :
  Keyed.lookup eqb key ((key, a) :: bindings) = Some a.
Proof. simpl. rewrite (keyed_eqb_refl eqb Heqb). reflexivity. Qed.

(* A binding of another key changes nothing. *)
Lemma keyed_lookup_other {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (key bound : K) (a : A)
    (bindings : list (K * A)) :
  key <> bound ->
  Keyed.lookup eqb key ((bound, a) :: bindings)
  = Keyed.lookup eqb key bindings.
Proof.
  intros Hne. simpl.
  destruct (keyed_eqb_spec eqb Heqb key bound);
    [ contradiction | reflexivity ].
Qed.

(* A binding added for a key that was not bound. *)
Lemma keyed_lookup_fresh {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (key fresh : K) (a added : A)
    (bindings : list (K * A)) :
  Keyed.lookup eqb fresh bindings = None ->
  Keyed.lookup eqb key bindings = Some a ->
  Keyed.lookup eqb key ((fresh, added) :: bindings) = Some a.
Proof.
  intros Hfresh Hkey. simpl.
  destruct (keyed_eqb_spec eqb Heqb key fresh) as [-> | _];
    [ congruence | exact Hkey ].
Qed.

Lemma keyed_lookup_app {K : Type} (eqb : K -> K -> bool) {A : Type}
    (key : K) (bindings bindings' : list (K * A)) :
  Keyed.lookup eqb key (bindings ++ bindings')
  = match Keyed.lookup eqb key bindings with
    | Some a => Some a
    | None => Keyed.lookup eqb key bindings'
    end.
Proof.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ reflexivity | ].
  destruct (eqb key bound); [ reflexivity | exact IH ].
Qed.

(* What is found is bound by one of the pairs, whatever the test. *)
Lemma keyed_lookup_snd_in {K : Type} (eqb : K -> K -> bool) {A : Type}
    (key : K) (a : A) (bindings : list (K * A)) :
  Keyed.lookup eqb key bindings = Some a ->
  ∃ bound : K, (bound, a) ∈ bindings ∧ eqb key bound = true.
Proof.
  induction bindings as [ | [bound b] bindings IH]; simpl; [ discriminate | ].
  destruct (eqb key bound) eqn:Htest.
  - intros [= ->]. exists bound. split; [ left; reflexivity | exact Htest ].
  - intros Hlookup. destruct (IH Hlookup) as (bound' & Hin & Htest').
    exists bound'. split; [ right; exact Hin | exact Htest' ].
Qed.

(* What is found is one of the bindings. *)
Lemma keyed_lookup_in {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (key : K) (a : A)
    (bindings : list (K * A)) :
  Keyed.lookup eqb key bindings = Some a -> (key, a) ∈ bindings.
Proof.
  intros Hlookup.
  destruct (keyed_lookup_snd_in eqb key a bindings Hlookup)
    as (bound & Hin & Htest).
  apply Heqb in Htest. subst bound. exact Hin.
Qed.

Lemma keyed_lookup_none_not_in {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (key : K)
    (bindings : list (K * A)) :
  Keyed.lookup eqb key bindings = None -> key ∉ map fst bindings.
Proof.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ auto | ].
  destruct (keyed_eqb_spec eqb Heqb key bound) as [-> | Hne];
    [ discriminate | ].
  intros Hlookup [Heq | Hin]; [ congruence | exact (IH Hlookup Hin) ].
Qed.

(* What holds of every binding holds of the one found. *)
Lemma keyed_lookup_forallb {K : Type} (eqb : K -> K -> bool) {A : Type}
    (f : A -> bool) (key : K) (a : A) (bindings : list (K * A)) :
  forallb (fun '(_, a) => f a) bindings = true ->
  Keyed.lookup eqb key bindings = Some a -> f a = true.
Proof.
  induction bindings as [ | [bound b] bindings IH]; simpl; [ discriminate | ].
  intros Hall. apply andb_true_iff in Hall as [Hb Hrest].
  destruct (eqb key bound); [ intros [= <-]; exact Hb | exact (IH Hrest) ].
Qed.

(* A key is bound when it is among the keys of the bindings. *)
Lemma keyed_is_bound_among {K : Type} (eqb : K -> K -> bool) {A : Type}
    (key : K) (bindings : Keyed.finite_map K A) :
  Keyed.is_bound eqb key bindings = Keyed.among eqb key (map fst bindings).
Proof.
  unfold Keyed.is_bound, Keyed.among.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ reflexivity | ].
  destruct (eqb key bound); [ reflexivity | exact IH ].
Qed.

Lemma keyed_is_bound_lookup {K : Type} (eqb : K -> K -> bool) {A : Type}
    (key : K) (bindings : Keyed.finite_map K A) :
  Keyed.is_bound eqb key bindings = true
  <-> ∃ a : A, Keyed.lookup eqb key bindings = Some a.
Proof.
  unfold Keyed.is_bound.
  destruct (Keyed.lookup eqb key bindings) as [a | ]; split.
  - intros _. exists a. reflexivity.
  - reflexivity.
  - discriminate.
  - intros [a [=]].
Qed.

(* ------------------------------------------------------------------------ *)
(* The operations on maps                                                   *)
(* ------------------------------------------------------------------------ *)

Theorem keyed_lookup_unbind : keyed_lookup_unbind_statement.
Proof.
  intros K eqb Heqb A key removed bindings. unfold Keyed.unbind.
  induction bindings as [ | [bound a] bindings IH]; simpl.
  - destruct (eqb key removed); reflexivity.
  - destruct (keyed_eqb_spec eqb Heqb removed bound) as [<- | Hne]; simpl;
      rewrite IH.
    + destruct (eqb key removed); reflexivity.
    + destruct (keyed_eqb_spec eqb Heqb key bound) as [-> | _];
        [ | reflexivity ].
      destruct (keyed_eqb_spec eqb Heqb bound removed);
        [ congruence | reflexivity ].
Qed.

Theorem keyed_lookup_map_values : keyed_lookup_map_values_statement.
Proof.
  intros K eqb A B f key bindings. unfold Keyed.map_values.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ reflexivity | ].
  destruct (eqb key bound); [ reflexivity | exact IH ].
Qed.

Theorem keyed_among_domain : keyed_among_domain_statement.
Proof.
  intros K eqb Heqb A key bindings. unfold Keyed.domain.
  rewrite (keyed_among_dedup K eqb Heqb), keyed_is_bound_among.
  reflexivity.
Qed.

Theorem keyed_domain_distinct : keyed_domain_distinct_statement.
Proof.
  intros K eqb Heqb A bindings. apply (keyed_dedup_distinct K eqb Heqb).
Qed.

Theorem keyed_lookup_tabulate : keyed_lookup_tabulate_statement.
Proof.
  intros K eqb Heqb A f key keys. unfold Keyed.tabulate, Keyed.among.
  induction keys as [ | first keys IH]; simpl; [ reflexivity | ].
  destruct (f first) as [a | ] eqn:Hfirst; simpl;
    destruct (keyed_eqb_spec eqb Heqb key first) as [-> | _]; simpl;
    try exact IH.
  - symmetry. exact Hfirst.
  - rewrite IH, Hfirst.
    destruct (existsb (eqb first) keys); reflexivity.
Qed.

(* The keys a tabulated map binds are those of the list for which the
   function gives something, in the order of the list. *)
Lemma keyed_tabulate_keys {K A : Type} (f : K -> option A) (keys : list K) :
  map fst (Keyed.tabulate f keys)
  = filter
      (fun key =>
         match f key with
         | Some _ => true
         | None => false
         end)
      keys.
Proof.
  unfold Keyed.tabulate.
  induction keys as [ | first keys IH]; simpl; [ reflexivity | ].
  destruct (f first); simpl; rewrite IH; reflexivity.
Qed.

Lemma keyed_tabulate_distinct {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (f : K -> option A)
    (keys : list K) :
  Keyed.distinct eqb keys = true ->
  Keyed.distinct eqb (map fst (Keyed.tabulate f keys)) = true.
Proof.
  rewrite keyed_tabulate_keys. apply (keyed_distinct_filter eqb Heqb).
Qed.

Theorem keyed_lookup_compact : keyed_lookup_compact_statement.
Proof.
  intros K eqb Heqb A key bindings. unfold Keyed.compact.
  rewrite (keyed_lookup_tabulate K eqb Heqb).
  rewrite (keyed_among_domain K eqb Heqb). unfold Keyed.is_bound.
  destruct (Keyed.lookup eqb key bindings); reflexivity.
Qed.

Theorem keyed_compact_distinct : keyed_compact_distinct_statement.
Proof.
  intros K eqb Heqb A bindings.
  apply (keyed_tabulate_distinct eqb Heqb).
  apply (keyed_domain_distinct K eqb Heqb).
Qed.

(* The bindings of the compact map are the ones [lookup] finds. *)
Lemma keyed_in_compact {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (key : K) (a : A)
    (bindings : Keyed.finite_map K A) :
  (key, a) ∈ Keyed.compact eqb bindings
  <-> Keyed.lookup eqb key bindings = Some a.
Proof.
  split.
  - unfold Keyed.compact, Keyed.tabulate. rewrite in_flat_map.
    intros (bound & _ & Hin).
    destruct (Keyed.lookup eqb bound bindings) as [b | ] eqn:Hlookup;
      [ | contradiction ].
    destruct Hin as [[= -> ->] | []]. exact Hlookup.
  - intros Hlookup. apply (keyed_lookup_in eqb Heqb).
    rewrite (keyed_lookup_compact K eqb Heqb). exact Hlookup.
Qed.

Theorem keyed_lookup_filter_bindings :
  keyed_lookup_filter_bindings_statement.
Proof.
  intros K eqb Heqb A keep key bindings. unfold Keyed.filter_bindings.
  rewrite (keyed_lookup_tabulate K eqb Heqb).
  rewrite (keyed_among_domain K eqb Heqb). unfold Keyed.is_bound.
  destruct (Keyed.lookup eqb key bindings); reflexivity.
Qed.

Theorem keyed_lookup_merge : keyed_lookup_merge_statement.
Proof.
  intros K eqb Heqb A B C f key bindings bindings' Hnone.
  unfold Keyed.merge.
  rewrite (keyed_lookup_tabulate K eqb Heqb).
  rewrite (keyed_among_dedup K eqb Heqb), keyed_among_app.
  rewrite <- !keyed_is_bound_among. unfold Keyed.is_bound.
  destruct (Keyed.lookup eqb key bindings),
    (Keyed.lookup eqb key bindings'); simpl; try reflexivity.
  symmetry. exact Hnone.
Qed.

Theorem keyed_lookup_union_with : keyed_lookup_union_with_statement.
Proof.
  intros K eqb Heqb A f key bindings bindings'. unfold Keyed.union_with.
  rewrite (keyed_lookup_merge K eqb Heqb); reflexivity.
Qed.

Theorem keyed_lookup_inter_with : keyed_lookup_inter_with_statement.
Proof.
  intros K eqb Heqb A B C f key bindings bindings'.
  unfold Keyed.inter_with.
  rewrite (keyed_lookup_merge K eqb Heqb); reflexivity.
Qed.

Theorem keyed_is_empty_lookup : keyed_is_empty_lookup_statement.
Proof.
  intros K eqb Heqb A [ | [bound a] bindings]; simpl; split;
    try reflexivity.
  - discriminate.
  - intros Hnone. specialize (Hnone bound).
    rewrite (keyed_eqb_refl eqb Heqb) in Hnone. discriminate.
Qed.

Theorem keyed_get_singleton_binding : keyed_get_singleton_binding_statement.
Proof.
  intros K eqb Heqb A key a bindings. unfold Keyed.get_singleton_binding.
  pose proof (keyed_compact_distinct K eqb Heqb A bindings) as Hdistinct.
  assert (Hsame :
    ∀ key' : K,
      Keyed.lookup eqb key' bindings
      = Keyed.lookup eqb key' (Keyed.compact eqb bindings)).
  { intros key'. symmetry. apply (keyed_lookup_compact K eqb Heqb). }
  destruct (Keyed.compact eqb bindings)
    as [ | [first b] [ | [second b'] rest]].
  - split; [ discriminate | ]. intros Hmap. specialize (Hmap key).
    rewrite Hsame, (keyed_eqb_refl eqb Heqb) in Hmap. discriminate.
  - split.
    + intros [= -> ->] key'. rewrite Hsame. reflexivity.
    + intros Hmap. specialize (Hmap first).
      rewrite Hsame, keyed_lookup_cons, (keyed_eqb_refl eqb Heqb) in Hmap.
      destruct (keyed_eqb_spec eqb Heqb first key) as [-> | _];
        [ | discriminate ].
      injection Hmap as ->. reflexivity.
  - split; [ discriminate | ]. intros Hmap. exfalso.
    assert (Hfirst : first = key).
    { pose proof (Hmap first) as Hat.
      rewrite Hsame, keyed_lookup_cons, (keyed_eqb_refl eqb Heqb) in Hat.
      destruct (keyed_eqb_spec eqb Heqb first key);
        [ assumption | discriminate ]. }
    assert (Hsecond : second = key).
    { pose proof (Hmap second) as Hat.
      rewrite Hsame, !keyed_lookup_cons, (keyed_eqb_refl eqb Heqb) in Hat.
      destruct (keyed_eqb_spec eqb Heqb second key); [ assumption | ].
      destruct (eqb second first); discriminate. }
    subst first second. simpl in Hdistinct.
    rewrite (keyed_eqb_refl eqb Heqb) in Hdistinct. discriminate.
Qed.

(* ------------------------------------------------------------------------ *)
(* Maps that are the same, and maps that are included                       *)
(* ------------------------------------------------------------------------ *)

Lemma keyed_map_equal_refl {K : Type} (eqb : K -> K -> bool) {A : Type}
    (bindings : Keyed.finite_map K A) :
  Keyed.map_equal eqb bindings bindings.
Proof. intros key. reflexivity. Qed.

Lemma keyed_map_equal_sym {K : Type} (eqb : K -> K -> bool) {A : Type}
    (bindings bindings' : Keyed.finite_map K A) :
  Keyed.map_equal eqb bindings bindings' ->
  Keyed.map_equal eqb bindings' bindings.
Proof. intros Hequal key. symmetry. apply Hequal. Qed.

Lemma keyed_map_equal_trans {K : Type} (eqb : K -> K -> bool) {A : Type}
    (bindings bindings' bindings'' : Keyed.finite_map K A) :
  Keyed.map_equal eqb bindings bindings' ->
  Keyed.map_equal eqb bindings' bindings'' ->
  Keyed.map_equal eqb bindings bindings''.
Proof. intros H H' key. rewrite (H key). apply H'. Qed.

Lemma keyed_compact_map_equal {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type}
    (bindings : Keyed.finite_map K A) :
  Keyed.map_equal eqb (Keyed.compact eqb bindings) bindings.
Proof. intros key. apply (keyed_lookup_compact K eqb Heqb). Qed.

Lemma keyed_map_included_refl {K : Type} (eqb : K -> K -> bool) {A : Type}
    (bindings : Keyed.finite_map K A) :
  Keyed.map_included eqb bindings bindings.
Proof. intros key a Hlookup. exact Hlookup. Qed.

Lemma keyed_map_included_trans {K : Type} (eqb : K -> K -> bool) {A : Type}
    (bindings bindings' bindings'' : Keyed.finite_map K A) :
  Keyed.map_included eqb bindings bindings' ->
  Keyed.map_included eqb bindings' bindings'' ->
  Keyed.map_included eqb bindings bindings''.
Proof. intros H H' key a Hlookup. apply H', H, Hlookup. Qed.

(* Two maps are the same when each is included in the other. *)
Lemma keyed_map_equal_included {K : Type} (eqb : K -> K -> bool) {A : Type}
    (bindings bindings' : Keyed.finite_map K A) :
  Keyed.map_equal eqb bindings bindings'
  <-> Keyed.map_included eqb bindings bindings'
      ∧ Keyed.map_included eqb bindings' bindings.
Proof.
  split.
  - intros Hequal. split; intros key a Hlookup.
    + rewrite <- (Hequal key). exact Hlookup.
    + rewrite (Hequal key). exact Hlookup.
  - intros [Hincluded Hincluded'] key.
    destruct (Keyed.lookup eqb key bindings) as [a | ] eqn:Hlookup.
    + symmetry. exact (Hincluded key a Hlookup).
    + destruct (Keyed.lookup eqb key bindings') as [a' | ] eqn:Hlookup';
        [ | reflexivity ].
      rewrite (Hincluded' key a' Hlookup') in Hlookup. discriminate.
Qed.

(* A binding added for a key that was not bound includes what was. *)
Lemma keyed_map_included_fresh {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (fresh : K) (added : A)
    (bindings : Keyed.finite_map K A) :
  Keyed.lookup eqb fresh bindings = None ->
  Keyed.map_included eqb bindings ((fresh, added) :: bindings).
Proof.
  intros Hfresh key a Hlookup.
  exact (keyed_lookup_fresh eqb Heqb key fresh a added bindings Hfresh
           Hlookup).
Qed.

(* The operations give the same map on maps that are the same. *)
Lemma keyed_unbind_map_equal {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (key : K)
    (bindings bindings' : Keyed.finite_map K A) :
  Keyed.map_equal eqb bindings bindings' ->
  Keyed.map_equal eqb (Keyed.unbind eqb key bindings)
    (Keyed.unbind eqb key bindings').
Proof.
  intros Hequal other.
  rewrite !(keyed_lookup_unbind K eqb Heqb), (Hequal other). reflexivity.
Qed.

Lemma keyed_map_values_map_equal {K : Type} (eqb : K -> K -> bool)
    {A B : Type} (f : A -> B) (bindings bindings' : Keyed.finite_map K A) :
  Keyed.map_equal eqb bindings bindings' ->
  Keyed.map_equal eqb (Keyed.map_values f bindings)
    (Keyed.map_values f bindings').
Proof.
  intros Hequal key.
  rewrite !keyed_lookup_map_values, (Hequal key). reflexivity.
Qed.

Lemma keyed_merge_map_equal {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A B C : Type}
    (f : option A -> option B -> option C)
    (left left' : Keyed.finite_map K A)
    (right right' : Keyed.finite_map K B) :
  f None None = None ->
  Keyed.map_equal eqb left left' -> Keyed.map_equal eqb right right' ->
  Keyed.map_equal eqb (Keyed.merge eqb f left right)
    (Keyed.merge eqb f left' right').
Proof.
  intros Hnone Hleft Hright key.
  rewrite !(keyed_lookup_merge K eqb Heqb), (Hleft key), (Hright key);
    auto.
Qed.

(* ------------------------------------------------------------------------ *)
(* Going through a list or a map                                            *)
(* ------------------------------------------------------------------------ *)

Theorem every_in : every_in_statement.
Proof.
  intros A P l. induction l as [ | first l IH]; simpl.
  - split; [ intros _ a [] | intros _; exact I ].
  - rewrite IH. split.
    + intros [Hfirst Hrest] a [<- | Hin];
        [ exact Hfirst | exact (Hrest a Hin) ].
    + intros Hall. split.
      * apply Hall. left. reflexivity.
      * intros a Hin. apply Hall. right. exact Hin.
Qed.

(* What follows from [P] on the elements of the list holds of every one
   if [P] does. *)
Lemma every_impl {A : Type} (P Q : A -> Prop) (l : list A) :
  (∀ a : A, a ∈ l -> P a -> Q a) -> every P l -> every Q l.
Proof.
  rewrite !(every_in A). intros Himpl HP a Hin.
  exact (Himpl a Hin (HP a Hin)).
Qed.

Theorem every_b_every : every_b_every_statement.
Proof.
  intros A p l. induction l as [ | first l IH]; simpl.
  - split; [ intros _; exact I | reflexivity ].
  - rewrite andb_true_iff, IH. reflexivity.
Qed.

(* A test that agrees with [P] on the elements of the list. *)
Lemma every_b_reflects {A : Type} (P : A -> Prop) (p : A -> bool)
    (l : list A) :
  (∀ a : A, a ∈ l -> (p a = true <-> P a)) ->
  (every_b p l = true <-> every P l).
Proof.
  intros Hreflects. rewrite (every_b_every A), !(every_in A). split.
  - intros Hall a Hin. apply (Hreflects a Hin), Hall, Hin.
  - intros Hall a Hin. apply (Hreflects a Hin), Hall, Hin.
Qed.

Theorem keyed_for_all_bindings_lookup :
  keyed_for_all_bindings_lookup_statement.
Proof.
  intros K eqb Heqb A P bindings. unfold Keyed.for_all_bindings.
  rewrite (every_in (K * A)%type). split.
  - intros Hall key a Hlookup.
    exact (Hall (key, a) (keyed_lookup_in eqb Heqb key a bindings Hlookup)
             Hlookup).
  - intros Hall [key a] _ Hlookup. exact (Hall key a Hlookup).
Qed.

Theorem keyed_at_binding_lookup : keyed_at_binding_lookup_statement.
Proof.
  intros K eqb A P key bindings. unfold Keyed.at_binding.
  rewrite (every_in (K * A)%type). split.
  - intros Hall a Hlookup.
    destruct (keyed_lookup_snd_in eqb key a bindings Hlookup)
      as (bound & Hin & _).
    exact (Hall (bound, a) Hin Hlookup).
  - intros Hall [bound a] _ Hlookup. exact (Hall a Hlookup).
Qed.

Theorem for_all_bindings_lookup : for_all_bindings_lookup_statement.
Proof.
  intros A P m. apply (keyed_for_all_bindings_lookup positive Pos.eqb).
  exact Pos.eqb_eq.
Qed.

Theorem at_binding_lookup : at_binding_lookup_statement.
Proof.
  intros A P name m. apply (keyed_at_binding_lookup positive Pos.eqb).
Qed.

(* What follows from [P] on the bindings that count holds of every one if
   [P] does. *)
Lemma keyed_for_all_bindings_impl {K : Type} (eqb : K -> K -> bool)
    {A : Type} (P Q : K -> A -> Prop) (bindings : Keyed.finite_map K A) :
  (∀ (key : K) (a : A),
     Keyed.lookup eqb key bindings = Some a -> P key a -> Q key a) ->
  Keyed.for_all_bindings eqb P bindings ->
  Keyed.for_all_bindings eqb Q bindings.
Proof.
  intros Himpl. unfold Keyed.for_all_bindings. apply every_impl.
  intros [key a] _ HP Hlookup. exact (Himpl key a Hlookup (HP Hlookup)).
Qed.

Lemma keyed_at_binding_impl {K : Type} (eqb : K -> K -> bool) {A : Type}
    (P Q : A -> Prop) (key : K) (bindings : Keyed.finite_map K A) :
  (∀ a : A, Keyed.lookup eqb key bindings = Some a -> P a -> Q a) ->
  Keyed.at_binding eqb P key bindings ->
  Keyed.at_binding eqb Q key bindings.
Proof.
  intros Himpl. unfold Keyed.at_binding. apply every_impl.
  intros [bound a] _ HP Hlookup. exact (Himpl a Hlookup (HP Hlookup)).
Qed.

(* The two say the same of maps that are the same. *)
Lemma keyed_for_all_bindings_map_equal {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (P : K -> A -> Prop)
    (bindings bindings' : Keyed.finite_map K A) :
  Keyed.map_equal eqb bindings bindings' ->
  (Keyed.for_all_bindings eqb P bindings
   <-> Keyed.for_all_bindings eqb P bindings').
Proof.
  intros Hequal. rewrite !(keyed_for_all_bindings_lookup K eqb Heqb).
  split; intros Hall key a Hlookup; apply Hall.
  - rewrite (Hequal key). exact Hlookup.
  - rewrite <- (Hequal key). exact Hlookup.
Qed.

Lemma keyed_at_binding_map_equal {K : Type} (eqb : K -> K -> bool)
    {A : Type} (P : A -> Prop) (key : K)
    (bindings bindings' : Keyed.finite_map K A) :
  Keyed.map_equal eqb bindings bindings' ->
  (Keyed.at_binding eqb P key bindings
   <-> Keyed.at_binding eqb P key bindings').
Proof.
  intros Hequal. rewrite !(keyed_at_binding_lookup K eqb), (Hequal key).
  reflexivity.
Qed.

(* The test of the binding of a key is the test of what [lookup] finds. *)
Lemma keyed_at_binding_b_lookup {K : Type} (eqb : K -> K -> bool)
    {A : Type} (p : A -> bool) (key : K)
    (bindings : Keyed.finite_map K A) :
  Keyed.at_binding_b eqb p key bindings
  = match Keyed.lookup eqb key bindings with
    | Some a => p a
    | None => true
    end.
Proof.
  induction bindings as [ | [bound a] bindings IH]; simpl; [ reflexivity | ].
  destruct (eqb key bound); [ reflexivity | exact IH ].
Qed.

Theorem keyed_at_binding_b : keyed_at_binding_b_statement.
Proof.
  intros K eqb A p key bindings.
  rewrite (keyed_at_binding_lookup K eqb), keyed_at_binding_b_lookup.
  destruct (Keyed.lookup eqb key bindings) as [a | ]; split.
  - intros Hp b [= <-]. exact Hp.
  - intros Hall. apply Hall. reflexivity.
  - intros _ b [=].
  - reflexivity.
Qed.

Theorem keyed_for_all_bindings_b : keyed_for_all_bindings_b_statement.
Proof.
  intros K eqb Heqb A p bindings.
  rewrite (keyed_for_all_bindings_lookup K eqb Heqb).
  unfold Keyed.for_all_bindings_b.
  match goal with
  | |- ?go [] bindings = true <-> _ =>
    assert (Hgo :
      ∀ (bindings : list (K * A)) (seen : list K),
        go seen bindings = true
        <-> (∀ (key : K) (a : A),
              Keyed.lookup eqb key bindings = Some a ->
              Keyed.among eqb key seen = false -> p key a = true))
  end.
  { clear bindings.
    induction bindings as [ | [bound b] bindings IH]; intros seen; simpl.
    - split; [ intros _ key a [=] | reflexivity ].
    - rewrite andb_true_iff, orb_true_iff, IH. split.
      + intros [Hbound Hrest] key a.
        destruct (keyed_eqb_spec eqb Heqb key bound) as [-> | Hne].
        * intros [= <-] Hunseen. destruct Hbound; congruence.
        * intros Hlookup Hunseen. apply (Hrest key a Hlookup).
          rewrite keyed_among_cons, Hunseen.
          destruct (keyed_eqb_spec eqb Heqb key bound);
            [ contradiction | reflexivity ].
      + intros Hall. split.
        * destruct (Keyed.among eqb bound seen) eqn:Hseen;
            [ left; reflexivity | right ].
          apply Hall; [ | exact Hseen ].
          rewrite (keyed_eqb_refl eqb Heqb). reflexivity.
        * intros key a Hlookup Hunseen.
          rewrite keyed_among_cons in Hunseen.
          apply orb_false_iff in Hunseen as [Hne Hunseen].
          apply Hall; [ | exact Hunseen ]. rewrite Hne. exact Hlookup. }
  rewrite Hgo. split.
  - intros Hall key a Hlookup. apply (Hall key a Hlookup). reflexivity.
  - intros Hall key a Hlookup _. exact (Hall key a Hlookup).
Qed.

(* A test that agrees with [P] on the bindings that count. *)
Lemma keyed_for_all_bindings_b_reflects {K : Type} (eqb : K -> K -> bool)
    (Heqb : decides_equality eqb) {A : Type} (P : K -> A -> Prop)
    (p : K -> A -> bool) (bindings : Keyed.finite_map K A) :
  (∀ (key : K) (a : A),
     Keyed.lookup eqb key bindings = Some a -> (p key a = true <-> P key a)) ->
  (Keyed.for_all_bindings_b eqb p bindings = true
   <-> Keyed.for_all_bindings eqb P bindings).
Proof.
  intros Hreflects. rewrite (keyed_for_all_bindings_b K eqb Heqb).
  split; apply keyed_for_all_bindings_impl; intros key a Hlookup;
    apply (Hreflects key a Hlookup).
Qed.

Lemma keyed_at_binding_b_reflects {K : Type} (eqb : K -> K -> bool)
    {A : Type} (P : A -> Prop) (p : A -> bool) (key : K)
    (bindings : Keyed.finite_map K A) :
  (∀ a : A, Keyed.lookup eqb key bindings = Some a -> (p a = true <-> P a)) ->
  (Keyed.at_binding_b eqb p key bindings = true
   <-> Keyed.at_binding eqb P key bindings).
Proof.
  intros Hreflects. rewrite (keyed_at_binding_b K eqb).
  split; apply keyed_at_binding_impl; intros a Hlookup;
    apply (Hreflects a Hlookup).
Qed.
