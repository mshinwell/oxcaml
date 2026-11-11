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

(* Proofs of the statements of FlambdaEnvAliasesSpec.v, and examples.
   Nothing here needs review. The examples are in the module [Examples]
   at the end: structures made by [Aliases.add], the environments that
   do and do not respect them, and what the queries answer. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec FlambdaMapProofs
  FlambdaSemanticsSpec.
From OxCamlFlambda2 Require FlambdaCompareSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaEnvAliasesSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* Names, constants and simples                                             *)
(* ======================================================================== *)

Lemma name_eqb_refl (n : name) : name_eqb n n = true.
Proof. apply (keyed_eqb_refl name_eqb name_eqb_eq). Qed.

Lemma const_eqb_eq : decides_equality const_eqb.
Proof.
  intros c c'. unfold FlambdaCompareSpec.const_eqb.
  destruct (FlambdaCompareSpec.const_eq_dec c c') as [Heq | Hne].
  - split; [ intros _; exact Heq | reflexivity ].
  - split; [ discriminate | intros Heq; contradiction ].
Qed.

Lemma name_mode_equal_eq : decides_equality Name_mode.equal.
Proof.
  intros [ | | ] [ | | ]; simpl; split;
    solve [ reflexivity | discriminate ].
Qed.

Lemma simple_of_name_inj (n n' : name) :
  simple_of_name n = simple_of_name n' -> n = n'.
Proof. destruct n, n'; simpl; intros [=]; subst; reflexivity. Qed.

Lemma name_of_simple_of_name (n : name) :
  name_of_simple (simple_of_name n) = Some n.
Proof. destruct n; reflexivity. Qed.

Lemma name_of_simple_some (s : simple) (n : name) :
  name_of_simple s = Some n -> s = simple_of_name n.
Proof. destruct s; simpl; intros [= <-]; reflexivity. Qed.

Lemma name_of_simple_none (s : simple) :
  name_of_simple s = None -> ∃ c : const, s = Const c.
Proof.
  destruct s; simpl; try discriminate. intros _. eexists. reflexivity.
Qed.

Lemma simple_equal_spec (s s' : simple) :
  reflect (s = s') (simple_equal s s').
Proof.
  destruct s as [x | sym | c], s' as [x' | sym' | c']; simpl;
    try (constructor; discriminate).
  - destruct (Pos.eqb_spec x x') as [-> | Hne]; constructor;
      [ reflexivity | intros [= Heq]; contradiction ].
  - destruct (Pos.eqb_spec sym sym') as [-> | Hne]; constructor;
      [ reflexivity | intros [= Heq]; contradiction ].
  - destruct (keyed_eqb_spec const_eqb const_eqb_eq c c') as [-> | Hne];
      constructor; [ reflexivity | intros [= Heq]; contradiction ].
Qed.

(* The proof to give with [simple_equal] wherever [Keyed] asks for one. *)
Lemma simple_equal_eq : decides_equality simple_equal.
Proof.
  intros s s'. destruct (simple_equal_spec s s') as [Heq | Hne].
  - split; [ intros _; exact Heq | reflexivity ].
  - split; [ discriminate | intros Heq; contradiction ].
Qed.

Theorem simple_equal_decides_equality :
  simple_equal_decides_equality_statement.
Proof. exact simple_equal_eq. Qed.

(* ======================================================================== *)
(* The classes                                                              *)
(* ======================================================================== *)

Lemma canonical_of_name (t : Aliases.t) (n : name) :
  Aliases.canonical t (simple_of_name n)
  = match Keyed.lookup name_eqb n (Aliases.canonical_elements t) with
    | None => Aliases.Is_canonical
    | Some canonical_element => Aliases.Alias_of_canonical canonical_element
    end.
Proof.
  unfold Aliases.canonical. rewrite name_of_simple_of_name. reflexivity.
Qed.

(* A simple is canonical, or is a name that has been demoted. *)
Lemma canonical_cases (t : Aliases.t) (e : simple) :
  (is_canonical t e ∧ canonical_element_of t e = e)
  ∨ (∃ (n : name) (canonical_element : simple),
       e = simple_of_name n
       ∧ demoted_to t n canonical_element
       ∧ Aliases.canonical t e = Aliases.Alias_of_canonical canonical_element
       ∧ canonical_element_of t e = canonical_element).
Proof.
  unfold is_canonical, canonical_element_of, demoted_to, Aliases.canonical.
  destruct (name_of_simple e) as [n | ] eqn:Hname; [ | left; auto ].
  apply name_of_simple_some in Hname. subst e.
  destruct (Keyed.lookup name_eqb n (Aliases.canonical_elements t))
    as [canonical_element | ] eqn:Hlookup; [ | left; auto ].
  right. exists n, canonical_element. auto.
Qed.

Lemma canonical_element_of_demoted (t : Aliases.t) (n : name)
    (canonical_element : simple) :
  demoted_to t n canonical_element ->
  canonical_element_of t (simple_of_name n) = canonical_element.
Proof.
  unfold demoted_to, canonical_element_of. intros Hdemoted.
  rewrite canonical_of_name, Hdemoted. reflexivity.
Qed.

Lemma canonical_element_of_canonical (t : Aliases.t) (e : simple) :
  is_canonical t e -> canonical_element_of t e = e.
Proof.
  unfold is_canonical, canonical_element_of. intros ->. reflexivity.
Qed.

(* ======================================================================== *)
(* What the structure means                                                 *)
(* ======================================================================== *)

Theorem empty_respected : empty_respected_statement.
Proof.
  intros vars. split.
  - intros n canonical_element Hdemoted. discriminate Hdemoted.
  - intros canonical_element n Hlisted. unfold listed_alias in Hlisted.
    destruct canonical_element; discriminate Hlisted.
Qed.

(* The canonical element of a simple has its value. *)
Lemma respected_canonical_element_of (t : Aliases.t) (vars : env)
    (e : simple) :
  aliases_respected t vars ->
  eval_simple vars (canonical_element_of t e) = eval_simple vars e.
Proof.
  intros [Hcanonical _].
  destruct (canonical_cases t e)
    as [[_ ->] | (n & canonical_element & -> & Hdemoted & _ & ->)];
    [ reflexivity | ].
  symmetry. exact (Hcanonical n canonical_element Hdemoted).
Qed.

Theorem respected_aliased : respected_aliased_statement.
Proof.
  intros t vars e e' Hrespected Haliased.
  rewrite <- (respected_canonical_element_of t vars e Hrespected).
  rewrite <- (respected_canonical_element_of t vars e' Hrespected).
  rewrite Haliased. reflexivity.
Qed.

Theorem respected_canonical : respected_canonical_statement.
Proof.
  intros t vars n Hrespected.
  exact (respected_canonical_element_of t vars (simple_of_name n) Hrespected).
Qed.

(* ------------------------------------------------------------------------ *)
(* The aliases of one canonical element                                     *)
(* ------------------------------------------------------------------------ *)

(* The keys of a map are the names it binds. *)
Lemma in_keys_lookup {A : Type} (n : name)
    (bindings : Keyed.finite_map name A) :
  n ∈ map fst bindings <-> ∃ a : A, Keyed.lookup name_eqb n bindings = Some a.
Proof.
  rewrite <- (keyed_among_in name name_eqb name_eqb_eq).
  rewrite <- keyed_is_bound_among. apply keyed_is_bound_lookup.
Qed.

Lemma mem_lookup (aliases : Aliases.Aliases_of_canonical_element.t)
    (n : name) :
  Aliases.Aliases_of_canonical_element.mem aliases n = true
  <-> ∃ name_mode : Name_mode.t,
        Keyed.lookup name_eqb n aliases = Some name_mode.
Proof. apply keyed_is_bound_lookup. Qed.

(* The aliases at a name mode are the names recorded with it. *)
Lemma in_at_mode (aliases : Aliases.Aliases_of_canonical_element.t)
    (order : Name_mode.t) (n : name) :
  n ∈ Aliases.Aliases_of_canonical_element.at_mode aliases order
  <-> Keyed.lookup name_eqb n aliases = Some order.
Proof.
  unfold Aliases.Aliases_of_canonical_element.at_mode.
  rewrite in_keys_lookup. split.
  - intros [name_mode Hlookup].
    rewrite (keyed_lookup_filter_bindings name name_eqb name_eqb_eq)
      in Hlookup.
    destruct (Keyed.lookup name_eqb n aliases) as [recorded | ];
      [ | discriminate ].
    destruct (Name_mode.equal recorded order) eqn:Hequal; [ | discriminate ].
    apply name_mode_equal_eq in Hequal. subst recorded. reflexivity.
  - intros Hlookup. exists order.
    rewrite (keyed_lookup_filter_bindings name name_eqb name_eqb_eq).
    rewrite Hlookup, (keyed_eqb_refl Name_mode.equal name_mode_equal_eq).
    reflexivity.
Qed.

(* The test that [Aliases.get_canonical_element_exn] and
   [find_earliest_candidates] make of two name modes. *)
Definition name_mode_at_least_b (name_mode min_name_mode : Name_mode.t)
    : bool :=
  match Name_mode.compare_partial_order name_mode min_name_mode with
  | None => false
  | Some c => 0 <=? c
  end.

Lemma name_mode_at_least_b_iff (name_mode min_name_mode : Name_mode.t) :
  name_mode_at_least_b name_mode min_name_mode = true
  <-> name_mode_at_least name_mode min_name_mode.
Proof.
  unfold name_mode_at_least_b, name_mode_at_least.
  destruct (Name_mode.compare_partial_order name_mode min_name_mode)
    as [c | ]; split.
  - intros Hle. exists c. split; [ reflexivity | apply Z.leb_le, Hle ].
  - intros (c' & [= <-] & Hle). apply Z.leb_le, Hle.
  - discriminate.
  - intros (c' & [=] & _).
Qed.

(* Every name mode is at least [In_types], and only [In_types] is below
   every name mode. *)
Lemma name_mode_at_least_in_types (name_mode : Name_mode.t) :
  name_mode_at_least name_mode Name_mode.In_types.
Proof.
  apply name_mode_at_least_b_iff. destruct name_mode; reflexivity.
Qed.

Lemma in_types_at_least (min_name_mode : Name_mode.t) :
  name_mode_at_least Name_mode.In_types min_name_mode ->
  min_name_mode = Name_mode.In_types.
Proof.
  intros Hle. apply name_mode_at_least_b_iff in Hle.
  destruct min_name_mode; solve [ reflexivity | discriminate Hle ].
Qed.

(* What [find_earliest_candidates] answers is the aliases of one name
   mode that is at least the one asked for, and there is one. *)
Lemma find_earliest_candidates_some
    (aliases : Aliases.Aliases_of_canonical_element.t)
    (filter_by_scope : Name_mode.t -> list name -> list name)
    (min_name_mode : Name_mode.t) (candidates : list name) :
  Aliases.Aliases_of_canonical_element.find_earliest_candidates aliases
    filter_by_scope min_name_mode
  = Some candidates ->
  ∃ order : Name_mode.t,
    name_mode_at_least order min_name_mode
    ∧ candidates
      = filter_by_scope order
          (Aliases.Aliases_of_canonical_element.at_mode aliases order)
    ∧ candidates <> [].
Proof.
  unfold Aliases.Aliases_of_canonical_element.find_earliest_candidates.
  cbn [List.fold_left].
  assert (Hcase :
    ∀ order : Name_mode.t,
      name_mode_at_least_b order min_name_mode = true ->
      (if Keyed.is_empty
            (filter_by_scope order
               (Aliases.Aliases_of_canonical_element.at_mode aliases order))
       then None
       else
         Some
           (filter_by_scope order
              (Aliases.Aliases_of_canonical_element.at_mode aliases order)))
      = Some candidates ->
      ∃ order : Name_mode.t,
        name_mode_at_least order min_name_mode
        ∧ candidates
          = filter_by_scope order
              (Aliases.Aliases_of_canonical_element.at_mode aliases order)
        ∧ candidates <> []).
  { intros order Hle Hsome. exists order.
    split; [ apply name_mode_at_least_b_iff, Hle | ].
    destruct (filter_by_scope order
                (Aliases.Aliases_of_canonical_element.at_mode aliases order))
      as [ | first rest ]; simpl in Hsome; [ discriminate | ].
    injection Hsome as <-. split; [ reflexivity | discriminate ]. }
  destruct min_name_mode; simpl Name_mode.compare_partial_order; cbv iota;
    simpl Z.leb; cbv iota.
  - (* Asked for [Normal]: the aliases at [Normal]. *)
    apply (Hcase Name_mode.Normal). reflexivity.
  - (* Asked for [Phantom]: the aliases at [Phantom], or at [Normal]. *)
    destruct (Keyed.is_empty
                (filter_by_scope Name_mode.Phantom
                   (Aliases.Aliases_of_canonical_element.at_mode aliases
                      Name_mode.Phantom))) eqn:Hphantom.
    + apply (Hcase Name_mode.Normal). reflexivity.
    + intros Hsome. apply (Hcase Name_mode.Phantom); [ reflexivity | ].
      rewrite Hphantom. exact Hsome.
  - (* Asked for [In_types]: the aliases at the first of the three name
       modes that has some. *)
    destruct (Keyed.is_empty
                (filter_by_scope Name_mode.In_types
                   (Aliases.Aliases_of_canonical_element.at_mode aliases
                      Name_mode.In_types))) eqn:Hin_types.
    + destruct (Keyed.is_empty
                  (filter_by_scope Name_mode.Phantom
                     (Aliases.Aliases_of_canonical_element.at_mode aliases
                        Name_mode.Phantom))) eqn:Hphantom.
      * apply (Hcase Name_mode.Normal). reflexivity.
      * intros Hsome. apply (Hcase Name_mode.Phantom); [ reflexivity | ].
        rewrite Hphantom. exact Hsome.
    + intros Hsome. apply (Hcase Name_mode.In_types); [ reflexivity | ].
      rewrite Hin_types. exact Hsome.
Qed.

(* The earliest of a list, as [find_earliest_alias] finds it, is one of
   the list. *)
Lemma fold_earliest_in (earlier : name -> name -> bool) (names : list name)
    (first : name) :
  List.fold_left
    (fun min_elt elt => if earlier elt min_elt then elt else min_elt)
    names first
  ∈ first :: names.
Proof.
  revert first. induction names as [ | n names IH]; intros first; simpl.
  - left. reflexivity.
  - destruct (earlier n first).
    + right. apply IH.
    + destruct (IH first) as [Heq | Hin]; [ left; exact Heq | ].
      right. right. exact Hin.
Qed.

(* What [find_earliest_alias] answers is an alias listed for the canonical
   element, recorded with a name mode that is at least the one asked
   for, and, unless that is [In_types], in scope with it. *)
Lemma find_earliest_alias_some {A : Type}
    (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (canonical_element : simple)
    (min_binding_time : Binding_time.t) (min_name_mode : Name_mode.t)
    (answer : simple) :
  Aliases.find_earliest_alias binding_time_resolver binding_times_and_modes
    t canonical_element min_binding_time min_name_mode
  = Some answer ->
  ∃ (n : name) (order : Name_mode.t),
    answer = simple_of_name n
    ∧ Keyed.lookup name_eqb n
        (Aliases.get_aliases_of_canonical_element t canonical_element)
      = Some order
    ∧ name_mode_at_least order min_name_mode
    ∧ (order = Name_mode.In_types
       ∨ Aliases.compute_name_mode binding_times_and_modes (simple_of_name n)
           min_binding_time
         = order).
Proof.
  unfold Aliases.find_earliest_alias.
  match goal with
  | |- match ?candidates with _ => _ end = _ -> _ =>
    destruct candidates as [at_earliest_mode | ] eqn:Hcandidates
  end; [ | discriminate ].
  destruct at_earliest_mode as [ | first rest ]; [ discriminate | ].
  intros [= <-].
  apply find_earliest_candidates_some in Hcandidates
    as (order & Hle & Hfiltered & _).
  eexists. exists order. split; [ reflexivity | ].
  match goal with
  | |- Keyed.lookup name_eqb ?earliest _ = _ ∧ _ =>
    assert (Hmember : earliest ∈ first :: rest);
      [ | revert Hmember; generalize earliest; intros n Hmember ]
  end.
  { destruct (fold_earliest_in
                (Aliases.name_defined_earlier binding_time_resolver
                   binding_times_and_modes)
                (first :: rest) first) as [Heq | Hin];
      [ left; exact Heq | exact Hin ]. }
  rewrite Hfiltered in Hmember.
  destruct (Name_mode.equal order Name_mode.in_types) eqn:Hin_types.
  - apply name_mode_equal_eq in Hin_types.
    apply in_at_mode in Hmember. auto.
  - apply filter_In in Hmember as [Hmember Hscoped].
    apply in_at_mode in Hmember. apply name_mode_equal_eq in Hscoped. auto.
Qed.

(* ------------------------------------------------------------------------ *)
(* The canonical element at a name mode, in one equation                    *)
(* ------------------------------------------------------------------------ *)

(* [Aliases.get_canonical_element_exn] answers the canonical element if
   its name mode is at least the one asked for, and otherwise what
   [find_earliest_alias] finds among its aliases. *)
Lemma get_canonical_element_exn_eq {A : Type}
    (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (element : simple)
    (elt_name_mode min_name_mode : Name_mode.t)
    (min_binding_time : Binding_time.t) :
  Aliases.get_canonical_element_exn binding_time_resolver
    binding_times_and_modes t element elt_name_mode min_name_mode
    min_binding_time
  = if name_mode_at_least_b
         (canonical_name_mode binding_times_and_modes t element elt_name_mode
            min_binding_time)
         min_name_mode
    then Some (canonical_element_of t element)
    else
      Aliases.find_earliest_alias binding_time_resolver
        binding_times_and_modes t (canonical_element_of t element)
        min_binding_time min_name_mode.
Proof.
  unfold Aliases.get_canonical_element_exn, canonical_name_mode,
    canonical_element_of.
  fold (name_mode_at_least_b elt_name_mode min_name_mode).
  destruct (Aliases.canonical t element) as [ | canonical_element ].
  - destruct (name_mode_at_least_b elt_name_mode min_name_mode) eqn:Hle;
      [ reflexivity | ].
    cbv beta iota zeta.
    fold (name_mode_at_least_b elt_name_mode min_name_mode).
    rewrite Hle. reflexivity.
  - cbv beta iota zeta.
    match goal with
    | |- (if ?test then _ else _) = _ =>
      change test
        with (name_mode_at_least_b
                (Aliases.compute_name_mode binding_times_and_modes
                   canonical_element min_binding_time)
                min_name_mode)
    end.
    destruct (name_mode_at_least_b elt_name_mode min_name_mode); reflexivity.
Qed.

Theorem respected_canonical_at_mode : respected_canonical_at_mode_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes t vars element
    elt_name_mode min_name_mode min_binding_time answer Hrespected Hanswer.
  rewrite get_canonical_element_exn_eq in Hanswer.
  rewrite <- (respected_canonical_element_of t vars element Hrespected).
  destruct (name_mode_at_least_b _ _).
  - injection Hanswer as <-. reflexivity.
  - apply find_earliest_alias_some in Hanswer
      as (n & order & -> & Hlookup & _ & _).
    destruct Hrespected as [_ Hlisted]. apply Hlisted.
    apply mem_lookup. exists order. exact Hlookup.
Qed.

Theorem respected_coincide : respected_coincide_statement.
Proof.
  intros t vars vars' Hsame [Hcanonical Hlisted].
  (* A canonical element has the same value in the two environments. *)
  assert (Hsimple :
    ∀ (n : name) (canonical_element : simple),
      demoted_to t n canonical_element ∨ listed_alias t canonical_element n ->
      eval_simple vars canonical_element
      = eval_simple vars' canonical_element).
  { intros n canonical_element Hmentioned.
    destruct (name_of_simple canonical_element) as [n' | ] eqn:Hname.
    - apply name_of_simple_some in Hname. subst canonical_element.
      apply (Hsame n').
      destruct Hmentioned as [Hdemoted | Hlisted'].
      + right. left. exists n. exact Hdemoted.
      + right. right. right. exists n. exact Hlisted'.
    - apply name_of_simple_none in Hname as [c ->]. reflexivity. }
  split.
  - intros n canonical_element Hdemoted.
    rewrite <- (Hsame n); [ | left; exists canonical_element; exact Hdemoted ].
    rewrite <- (Hsimple n canonical_element (or_introl Hdemoted)).
    exact (Hcanonical n canonical_element Hdemoted).
  - intros canonical_element n Hlisted'.
    rewrite <- (Hsame n);
      [ | right; right; left; exists canonical_element; exact Hlisted' ].
    rewrite <- (Hsimple n canonical_element (or_intror Hlisted')).
    exact (Hlisted canonical_element n Hlisted').
Qed.

Theorem respected_alias_type : respected_alias_type_statement.
Proof.
  intros t statics vars v k n Hrespected.
  rewrite !(alias_satisfied statics vars v).
  rewrite (respected_canonical t vars n Hrespected). reflexivity.
Qed.

(* ======================================================================== *)
(* The order                                                                *)
(* ======================================================================== *)

Theorem defined_earlier_names : defined_earlier_names_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes alias than.
  unfold Aliases.defined_earlier. rewrite !name_of_simple_of_name.
  reflexivity.
Qed.

Theorem constant_earliest : constant_earliest_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes c e n.
  unfold Aliases.defined_earlier. rewrite name_of_simple_of_name.
  split; reflexivity.
Qed.

Theorem symbol_earlier : symbol_earlier_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes s x n.
  split; [ reflexivity | ].
  unfold Aliases.name_defined_earlier. destruct n as [y | s']; simpl.
  - reflexivity.
  - rewrite orb_true_r. reflexivity.
Qed.

(* The order on two variables, written with the binding times of the
   statements. *)
Lemma name_defined_earlier_variables {A : Type}
    (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (x y : variable) :
  Aliases.name_defined_earlier binding_time_resolver binding_times_and_modes
    (Name_var x) (Name_var y)
  = if Pos.eqb x y
    then false
    else if binding_time_in binding_times_and_modes x
            <? binding_time_in binding_times_and_modes y
    then true
    else if negb
              (binding_time_in binding_times_and_modes x
               =? binding_time_in binding_times_and_modes y)
    then false
    else
      resolved_binding_time binding_time_resolver x
      <? resolved_binding_time binding_time_resolver y.
Proof.
  unfold Aliases.name_defined_earlier, binding_time_in,
    resolved_binding_time, Aliases.binding_time_and_name_mode,
    Binding_time.strictly_earlier, Binding_time.equal.
  simpl name_eqb. simpl name_is_symbol. rewrite orb_false_r.
  cbv beta iota zeta. simpl andb. cbv iota.
  destruct (Keyed.lookup name_eqb (Name_var x) binding_times_and_modes)
    as [[a time_and_mode] | ];
    destruct (Keyed.lookup name_eqb (Name_var y) binding_times_and_modes)
      as [[a' time_and_mode'] | ];
    reflexivity.
Qed.

Theorem variable_earlier : variable_earlier_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes x y.
  rewrite name_defined_earlier_variables.
  destruct (Pos.eqb_spec x y) as [-> | Hne].
  - split; [ discriminate | lia ].
  - destruct (Z.ltb_spec (binding_time_in binding_times_and_modes x)
                (binding_time_in binding_times_and_modes y)).
    + split; [ intros _; left; assumption | reflexivity ].
    + destruct (Z.eqb_spec (binding_time_in binding_times_and_modes x)
                  (binding_time_in binding_times_and_modes y)); simpl.
      * rewrite Z.ltb_lt. split; [ intros Hlt; right; auto | ].
        intros [Hlt | [_ Hlt]]; [ lia | exact Hlt ].
      * split; [ discriminate | lia ].
Qed.

Lemma name_defined_earlier_irreflexive {A : Type}
    (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (n : name) :
  Aliases.name_defined_earlier binding_time_resolver binding_times_and_modes
    n n
  = false.
Proof.
  unfold Aliases.name_defined_earlier. rewrite name_eqb_refl. reflexivity.
Qed.

Lemma name_defined_earlier_transitive {A : Type}
    (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (n n' n'' : name) :
  Aliases.name_defined_earlier binding_time_resolver binding_times_and_modes
    n n'
  = true ->
  Aliases.name_defined_earlier binding_time_resolver binding_times_and_modes
    n' n''
  = true ->
  Aliases.name_defined_earlier binding_time_resolver binding_times_and_modes
    n n''
  = true.
Proof.
  pose proof (symbol_earlier A binding_time_resolver binding_times_and_modes)
    as Hsymbol.
  destruct n as [x | s], n' as [y | s'], n'' as [z | s''];
    intros Hfirst Hsecond;
    try (rewrite (proj2 (Hsymbol _ 1%positive _)) in Hfirst;
         discriminate Hfirst);
    try (rewrite (proj2 (Hsymbol _ 1%positive _)) in Hsecond;
         discriminate Hsecond).
  - (* Three variables: the order of the binding times is transitive. *)
    apply variable_earlier in Hfirst, Hsecond. apply variable_earlier. lia.
  - exact (proj1 (Hsymbol s z (Name_var z))).
Qed.

Theorem defined_earlier_strict : defined_earlier_strict_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes e e' e''.
  unfold Aliases.defined_earlier. split.
  - destruct (name_of_simple e);
      [ apply name_defined_earlier_irreflexive | reflexivity ].
  - destruct (name_of_simple e'') as [n'' | ]; [ | intros _; discriminate ].
    destruct (name_of_simple e') as [n' | ]; [ | discriminate ].
    destruct (name_of_simple e) as [n | ]; [ | reflexivity ].
    apply name_defined_earlier_transitive.
Qed.

(* ======================================================================== *)
(* The canonical element                                                    *)
(* ======================================================================== *)

Theorem get_canonical_ignoring_name_mode :
  get_canonical_ignoring_name_mode_statement.
Proof. intros t n. reflexivity. Qed.

Theorem canonical_element_canonical : canonical_element_canonical_statement.
Proof.
  intros t e [Hcanonical _].
  destruct (canonical_cases t e)
    as [[Hself ->] | (n & canonical_element & _ & Hdemoted & _ & ->)].
  - exact Hself.
  - exact (Hcanonical n canonical_element Hdemoted).
Qed.

Theorem canonical_element_idempotent :
  canonical_element_idempotent_statement.
Proof.
  intros t e Hconsistent. apply canonical_element_of_canonical.
  apply canonical_element_canonical, Hconsistent.
Qed.

Theorem canonical_element_mentioned : canonical_element_mentioned_statement.
Proof.
  intros t n n' Hcanonical.
  change (canonical_element_of t (simple_of_name n) = simple_of_name n')
    in Hcanonical.
  destruct (canonical_cases t (simple_of_name n))
    as [[_ Hself] | (m & canonical_element & Hname & Hdemoted & _ & Hof)].
  - left. rewrite Hself in Hcanonical.
    symmetry. exact (simple_of_name_inj _ _ Hcanonical).
  - right. right. left. exists m.
    rewrite Hof in Hcanonical. rewrite <- Hcanonical. exact Hdemoted.
Qed.

Theorem canonical_element_earliest : canonical_element_earliest_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes t e Hearliest Hother.
  destruct (canonical_cases t e)
    as [[_ Hself] | (n & canonical_element & -> & Hdemoted & _ & ->)].
  - contradiction.
  - exact (Hearliest n canonical_element Hdemoted).
Qed.

Theorem canonical_element_constant : canonical_element_constant_statement.
Proof. intros t e c Haliased. exact Haliased. Qed.

Theorem canonical_element_symbol : canonical_element_symbol_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes t e s Hearliest
    Haliased.
  rewrite Haliased.
  destruct (canonical_cases t (Symbol s))
    as [[_ ->] | (n & canonical_element & Hname & Hdemoted & _ & ->)];
    [ left; reflexivity | ].
  right.
  change (Symbol s) with (simple_of_name (Name_symbol s)) in Hname.
  apply simple_of_name_inj in Hname. subst n.
  specialize (Hearliest (Name_symbol s) canonical_element Hdemoted).
  destruct (name_of_simple canonical_element) as [n | ] eqn:Hcanonical.
  - (* A name is not earlier than a symbol. *)
    apply name_of_simple_some in Hcanonical. subst canonical_element.
    rewrite defined_earlier_names in Hearliest.
    rewrite (proj2 (symbol_earlier A binding_time_resolver
                      binding_times_and_modes s 1%positive n)) in Hearliest.
    discriminate Hearliest.
  - exact (name_of_simple_none canonical_element Hcanonical).
Qed.

(* ======================================================================== *)
(* The canonical element at a name mode                                     *)
(* ======================================================================== *)

Theorem canonical_at_mode : canonical_at_mode_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes t element
    elt_name_mode min_name_mode min_binding_time Hle.
  rewrite get_canonical_element_exn_eq.
  apply name_mode_at_least_b_iff in Hle. rewrite Hle. reflexivity.
Qed.

Theorem canonical_at_mode_name_mode : canonical_at_mode_name_mode_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes t element
    elt_name_mode min_name_mode min_binding_time answer Hanswer.
  rewrite get_canonical_element_exn_eq in Hanswer.
  destruct (name_mode_at_least_b _ _) eqn:Hle.
  - (* The canonical element. *)
    injection Hanswer as <-. apply name_mode_at_least_b_iff in Hle.
    unfold canonical_name_mode in Hle.
    destruct (canonical_cases t element)
      as [[Hself ->] | (n & canonical_element & _ & _ & Hcanonical & ->)].
    + left. rewrite Hself in Hle. auto.
    + right. rewrite Hcanonical in Hle. exact Hle.
  - (* An alias: it is in scope with its name mode, or its name mode was
       [In_types], and then that is what was asked for. *)
    right.
    apply find_earliest_alias_some in Hanswer
      as (n & order & -> & _ & Horder & [-> | ->]).
    + apply in_types_at_least in Horder. subst min_name_mode.
      apply name_mode_at_least_in_types.
    + exact Horder.
Qed.

Theorem canonical_at_mode_aliased : canonical_at_mode_aliased_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes t element
    elt_name_mode min_name_mode min_binding_time answer Hconsistent Hanswer.
  rewrite get_canonical_element_exn_eq in Hanswer. unfold aliased.
  destruct (name_mode_at_least_b _ _).
  - injection Hanswer as <-. apply canonical_element_of_canonical.
    apply canonical_element_canonical, Hconsistent.
  - apply find_earliest_alias_some in Hanswer
      as (n & order & -> & Hlookup & _ & _).
    apply canonical_element_of_demoted. apply Hconsistent.
    apply mem_lookup. exists order. exact Hlookup.
Qed.

(* ------------------------------------------------------------------------ *)
(* Which alias is the answer                                                *)
(* ------------------------------------------------------------------------ *)

Lemma is_empty_nil {B : Type} (l : list B) :
  Keyed.is_empty l = true <-> l = [].
Proof. destruct l; simpl; split; solve [ reflexivity | discriminate ]. Qed.

(* Settles what is left of a case of [find_earliest_candidates_cases]: a
   comparison of two name modes, by computation, or a list of candidates
   that is empty and is not. *)
Ltac settle_name_modes :=
  first
    [ apply name_mode_at_least_b_iff; reflexivity
    | match goal with
      | Hle : name_mode_at_least _ _ |- _ =>
        apply name_mode_at_least_b_iff in Hle; discriminate Hle
      end
    | match goal with
      | Hne : ?c <> [], Hempty : Keyed.is_empty ?c = true |- _ =>
        exfalso; apply Hne, is_empty_nil, Hempty
      end
    | match goal with
      | Hempty : Keyed.is_empty ?c = true |- ?c = [] =>
        apply is_empty_nil, Hempty
      end ].

(* [find_earliest_candidates] in full: the answer is the candidates of the
   least name mode that is at least the one asked for and has some; there
   is none only if no such name mode has a candidate. *)
Lemma find_earliest_candidates_cases
    (aliases : Aliases.Aliases_of_canonical_element.t)
    (filter_by_scope : Name_mode.t -> list name -> list name)
    (min_name_mode : Name_mode.t) :
  match
    Aliases.Aliases_of_canonical_element.find_earliest_candidates aliases
      filter_by_scope min_name_mode
  with
  | Some candidates =>
    ∃ order : Name_mode.t,
      name_mode_at_least order min_name_mode
      ∧ candidates
        = filter_by_scope order
            (Aliases.Aliases_of_canonical_element.at_mode aliases order)
      ∧ candidates <> []
      ∧ ∀ order' : Name_mode.t,
          name_mode_at_least order' min_name_mode ->
          filter_by_scope order'
            (Aliases.Aliases_of_canonical_element.at_mode aliases order')
          <> [] ->
          name_mode_at_least order' order
  | None =>
    ∀ order : Name_mode.t,
      name_mode_at_least order min_name_mode ->
      filter_by_scope order
        (Aliases.Aliases_of_canonical_element.at_mode aliases order)
      = []
  end.
Proof.
  unfold Aliases.Aliases_of_canonical_element.find_earliest_candidates.
  cbn [List.fold_left].
  remember (filter_by_scope Name_mode.In_types
              (Aliases.Aliases_of_canonical_element.at_mode aliases
                 Name_mode.In_types)) as in_types eqn:Hin_types.
  remember (filter_by_scope Name_mode.Phantom
              (Aliases.Aliases_of_canonical_element.at_mode aliases
                 Name_mode.Phantom)) as phantom eqn:Hphantom.
  remember (filter_by_scope Name_mode.Normal
              (Aliases.Aliases_of_canonical_element.at_mode aliases
                 Name_mode.Normal)) as normal eqn:Hnormal.
  destruct (Keyed.is_empty in_types) eqn:Hempty_in_types;
    destruct (Keyed.is_empty phantom) eqn:Hempty_phantom;
    destruct (Keyed.is_empty normal) eqn:Hempty_normal;
    destruct min_name_mode; simpl;
    rewrite ?Hempty_in_types, ?Hempty_phantom, ?Hempty_normal;
    try (match goal with
         | Heq : ?c = filter_by_scope ?order _
           |- ∃ order' : Name_mode.t, _ ∧ ?c = _ ∧ _ =>
           exists order
         end;
         split; [ settle_name_modes | ];
         split; [ assumption | ];
         split;
           [ intros Hnil; apply is_empty_nil in Hnil; congruence | ];
         intros order' Hle Hne;
         destruct order';
         rewrite <- ?Hin_types, <- ?Hphantom, <- ?Hnormal in Hne;
         settle_name_modes);
    intros order Hle; destruct order;
    rewrite <- ?Hin_types, <- ?Hphantom, <- ?Hnormal;
    settle_name_modes.
Qed.

(* The earliest of a list, as [find_earliest_alias] finds it: it is the
   name it starts from or is earlier than it, and no name of the list is
   earlier than it. *)
Section Earliest.

Variable earlier : name -> name -> bool.

Hypothesis earlier_irreflexive : ∀ n : name, earlier n n = false.

Hypothesis earlier_transitive :
  ∀ n n' n'' : name,
    earlier n n' = true -> earlier n' n'' = true -> earlier n n'' = true.

Lemma fold_earliest_before (names : list name) (first : name) :
  let earliest :=
    List.fold_left
      (fun min_elt elt => if earlier elt min_elt then elt else min_elt)
      names first
  in
  earliest = first ∨ earlier earliest first = true.
Proof.
  revert first. induction names as [ | n names IH]; intros first; simpl.
  - left. reflexivity.
  - destruct (earlier n first) eqn:Hn.
    + right. destruct (IH n) as [-> | Hbefore]; [ exact Hn | ].
      exact (earlier_transitive _ _ _ Hbefore Hn).
    + apply IH.
Qed.

Lemma fold_earliest_minimal (names : list name) (first n : name) :
  n ∈ first :: names ->
  earlier n
    (List.fold_left
       (fun min_elt elt => if earlier elt min_elt then elt else min_elt)
       names first)
  = false.
Proof.
  revert first. induction names as [ | n' names IH]; intros first Hin.
  - destruct Hin as [<- | []]. apply earlier_irreflexive.
  - simpl. destruct (earlier n' first) eqn:Hn'.
    + (* [n'] is the earliest so far. *)
      destruct Hin as [<- | Hin]; [ | apply IH; exact Hin ].
      match goal with
      | |- ?test = false => destruct test eqn:Hfirst; [ | reflexivity ]
      end.
      exfalso.
      destruct (fold_earliest_before names n') as [Heq | Hbefore];
        simpl in *.
      * rewrite Heq in Hfirst.
        pose proof (earlier_transitive _ _ _ Hfirst Hn') as Hloop.
        rewrite earlier_irreflexive in Hloop. discriminate Hloop.
      * pose proof (earlier_transitive _ _ _ Hfirst Hbefore) as Hfirst'.
        pose proof (earlier_transitive _ _ _ Hfirst' Hn') as Hloop.
        rewrite earlier_irreflexive in Hloop. discriminate Hloop.
    + (* [first] still is. *)
      destruct Hin as [<- | [<- | Hin]];
        [ apply IH; left; reflexivity | | apply IH; right; exact Hin ].
      match goal with
      | |- ?test = false => destruct test eqn:Hearlier; [ | reflexivity ]
      end.
      exfalso.
      destruct (fold_earliest_before names first) as [Heq | Hbefore];
        simpl in *.
      * rewrite Heq in Hearlier. congruence.
      * pose proof (earlier_transitive _ _ _ Hearlier Hbefore) as Hn.
        congruence.
Qed.

End Earliest.

(* The filter that [find_earliest_alias] gives to
   [find_earliest_candidates]. *)
Definition filter_by_scope {A : Type}
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (min_binding_time : Binding_time.t) (name_mode : Name_mode.t)
    (names : list name) : list name :=
  if Name_mode.equal name_mode Name_mode.in_types
  then names
  else
    filter
      (fun name =>
         Name_mode.equal name_mode
           (Aliases.compute_name_mode binding_times_and_modes
              (simple_of_name name) min_binding_time))
      names.

(* What it keeps of the aliases recorded with a name mode is the
   candidates of the Spec. *)
Lemma in_filter_by_scope {A : Type}
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (canonical_element : simple)
    (min_binding_time : Binding_time.t) (order : Name_mode.t) (n : name) :
  n ∈ filter_by_scope binding_times_and_modes min_binding_time order
        (Aliases.Aliases_of_canonical_element.at_mode
           (Aliases.get_aliases_of_canonical_element t canonical_element)
           order)
  <-> alias_candidate binding_times_and_modes t canonical_element
        min_binding_time order n.
Proof.
  unfold filter_by_scope, alias_candidate.
  destruct (Name_mode.equal order Name_mode.in_types) eqn:Hin_types.
  - apply name_mode_equal_eq in Hin_types. rewrite in_at_mode.
    split; [ auto | intros [Hlookup _]; exact Hlookup ].
  - rewrite filter_In, in_at_mode. split; intros [Hlookup Hscoped].
    + apply name_mode_equal_eq in Hscoped. auto.
    + split; [ exact Hlookup | ]. apply name_mode_equal_eq.
      destruct Hscoped as [-> | Hscoped]; [ discriminate Hin_types | ].
      symmetry. exact Hscoped.
Qed.

Lemma find_earliest_alias_eq {A : Type}
    (binding_time_resolver : name -> Binding_time.With_name_mode.t)
    (binding_times_and_modes
      : Keyed.finite_map name (A * Binding_time.With_name_mode.t))
    (t : Aliases.t) (canonical_element : simple)
    (min_binding_time : Binding_time.t) (min_name_mode : Name_mode.t) :
  Aliases.find_earliest_alias binding_time_resolver binding_times_and_modes
    t canonical_element min_binding_time min_name_mode
  = match
      Aliases.Aliases_of_canonical_element.find_earliest_candidates
        (Aliases.get_aliases_of_canonical_element t canonical_element)
        (filter_by_scope binding_times_and_modes min_binding_time)
        min_name_mode
    with
    | Some [] | None => None
    | Some (first :: rest) =>
      Some
        (simple_of_name
           (List.fold_left
              (fun min_elt elt =>
                 if Aliases.name_defined_earlier binding_time_resolver
                      binding_times_and_modes elt min_elt
                 then elt
                 else min_elt)
              (first :: rest) first))
    end.
Proof.
  unfold Aliases.find_earliest_alias.
  fold (filter_by_scope binding_times_and_modes min_binding_time).
  destruct (Aliases.Aliases_of_canonical_element.find_earliest_candidates
              _ _ _) as [[ | first rest ] | ];
    reflexivity.
Qed.

Theorem earliest_alias : earliest_alias_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes t element
    elt_name_mode min_name_mode min_binding_time answer Hnot Hanswer.
  rewrite get_canonical_element_exn_eq in Hanswer.
  destruct (name_mode_at_least_b _ _) eqn:Hle;
    [ exfalso; apply Hnot, name_mode_at_least_b_iff, Hle | ].
  clear Hnot Hle. revert Hanswer.
  generalize (canonical_element_of t element). intros canonical_element.
  rewrite find_earliest_alias_eq.
  pose proof (find_earliest_candidates_cases
    (Aliases.get_aliases_of_canonical_element t canonical_element)
    (filter_by_scope binding_times_and_modes min_binding_time)
    min_name_mode) as Hcases.
  destruct (Aliases.Aliases_of_canonical_element.find_earliest_candidates
              _ _ _) as [candidates | ]; [ | discriminate ].
  destruct Hcases as (order & Hle & Hcandidates & _ & Hleast).
  destruct candidates as [ | first rest ]; [ discriminate | ].
  intros [= <-]. eexists. exists order.
  split; [ reflexivity | ]. split; [ exact Hle | ]. split.
  - (* The answer is a candidate. *)
    apply in_filter_by_scope. rewrite <- Hcandidates.
    destruct (fold_earliest_in
                (Aliases.name_defined_earlier binding_time_resolver
                   binding_times_and_modes)
                (first :: rest) first) as [Heq | Hin];
      [ left; exact Heq | exact Hin ].
  - intros n' order' Hle' Hcandidate. apply in_filter_by_scope in Hcandidate.
    split.
    + (* The name mode of any other candidate is at least its. *)
      apply Hleast; [ exact Hle' | ]. intros Hnil.
      rewrite Hnil in Hcandidate. exact Hcandidate.
    + (* No candidate of its name mode is earlier. *)
      intros ->. rewrite <- Hcandidates in Hcandidate.
      rewrite name_defined_earlier_irreflexive.
      apply fold_earliest_minimal.
      * apply name_defined_earlier_irreflexive.
      * apply name_defined_earlier_transitive.
      * exact Hcandidate.
Qed.

Theorem no_alias : no_alias_statement.
Proof.
  intros A binding_time_resolver binding_times_and_modes t element
    elt_name_mode min_name_mode min_binding_time Hnot.
  rewrite get_canonical_element_exn_eq.
  destruct (name_mode_at_least_b _ _) eqn:Hle;
    [ exfalso; apply Hnot, name_mode_at_least_b_iff, Hle | ].
  clear Hnot Hle.
  generalize (canonical_element_of t element). intros canonical_element.
  rewrite find_earliest_alias_eq.
  pose proof (find_earliest_candidates_cases
    (Aliases.get_aliases_of_canonical_element t canonical_element)
    (filter_by_scope binding_times_and_modes min_binding_time)
    min_name_mode) as Hcases.
  destruct (Aliases.Aliases_of_canonical_element.find_earliest_candidates
              _ _ _) as [candidates | ].
  - (* There are candidates: the first of them is one. *)
    destruct Hcases as (order & Hle & Hcandidates & Hne & _).
    destruct candidates as [ | first rest ]; [ contradiction | ].
    split; [ discriminate | ]. intros Hnone. exfalso.
    apply (Hnone first order Hle). apply in_filter_by_scope.
    rewrite <- Hcandidates. left. reflexivity.
  - split; [ | reflexivity ]. intros _ n order Hle Hcandidate.
    apply in_filter_by_scope in Hcandidate.
    rewrite (Hcases order Hle) in Hcandidate. exact Hcandidate.
Qed.

(* ======================================================================== *)
(* Examples                                                                 *)
(* ======================================================================== *)

(* Respect of a structure written out as its lists is a property of the
   pairs in them. *)
Lemma respected_of_pairs (t : Aliases.t) (vars : env) :
  (∀ (n : name) (canonical_element : simple),
    (n, canonical_element) ∈ Aliases.canonical_elements t ->
    value_of_name vars n = eval_simple vars canonical_element) ->
  (∀ (canonical_name : name)
     (aliases : Aliases.Aliases_of_canonical_element.t) (n : name)
     (name_mode : Name_mode.t),
    (canonical_name, aliases) ∈ Aliases.aliases_of_canonical_names t ->
    (n, name_mode) ∈ aliases ->
    value_of_name vars n = value_of_name vars canonical_name) ->
  (∀ (c : const) (aliases : Aliases.Aliases_of_canonical_element.t)
     (n : name) (name_mode : Name_mode.t),
    (c, aliases) ∈ Aliases.aliases_of_consts t ->
    (n, name_mode) ∈ aliases ->
    value_of_name vars n = Some (Value_const c)) ->
  aliases_respected t vars.
Proof.
  intros Hcanonical Hnames Hconsts. split.
  - intros n canonical_element Hdemoted. apply Hcanonical.
    exact (keyed_lookup_in name_eqb name_eqb_eq _ _ _ Hdemoted).
  - intros canonical_element n Hlisted. unfold listed_alias in Hlisted.
    apply mem_lookup in Hlisted as [name_mode Hlookup].
    apply (keyed_lookup_in name_eqb name_eqb_eq) in Hlookup.
    unfold Aliases.get_aliases_of_canonical_element in Hlookup.
    destruct canonical_element as [x | s | c].
    + destruct (Keyed.lookup name_eqb (Name_var x)
                  (Aliases.aliases_of_canonical_names t))
        as [aliases | ] eqn:Haliases; [ | contradiction ].
      apply (keyed_lookup_in name_eqb name_eqb_eq) in Haliases.
      exact (Hnames _ _ _ _ Haliases Hlookup).
    + destruct (Keyed.lookup name_eqb (Name_symbol s)
                  (Aliases.aliases_of_canonical_names t))
        as [aliases | ] eqn:Haliases; [ | contradiction ].
      apply (keyed_lookup_in name_eqb name_eqb_eq) in Haliases.
      exact (Hnames _ _ _ _ Haliases Hlookup).
    + destruct (Keyed.lookup const_eqb c (Aliases.aliases_of_consts t))
        as [aliases | ] eqn:Haliases; [ | contradiction ].
      apply (keyed_lookup_in const_eqb const_eqb_eq) in Haliases.
      exact (Hconsts _ _ _ _ Haliases Hlookup).
Qed.

(* Goes through the pairs of a structure written out as its lists. *)
Ltac respected_by_pairs :=
  apply respected_of_pairs; simpl; intros;
  repeat
    match goal with
    | H : _ ∨ _ |- _ => destruct H
    | H : False |- _ => contradiction
    | H : (_, _) = (_, _) |- _ => injection H as <- <-
    | H : _ ∈ _ |- _ => simpl in H
    end;
  subst; reflexivity.

Module Examples.

(* Three variables, a symbol and two constants. *)
Definition w : variable := 1%positive.
Definition x : variable := 2%positive.
Definition y : variable := 3%positive.
Definition s : symbol := 1%positive.
Definition s' : symbol := 2%positive.
Definition five : const := Tagged_immediate 5.
Definition six : const := Tagged_immediate 6.

Definition entry (time : Binding_time.t) (name_mode : Name_mode.t)
    : unit * Binding_time.With_name_mode.t :=
  (tt, Binding_time.With_name_mode.create time name_mode).

(* A typing environment that bound [w], then [x], then [y], all three with
   a value at run time. *)
Definition times
    : Keyed.finite_map name (unit * Binding_time.With_name_mode.t) :=
  [(Name_var w, entry 3 Name_mode.Normal);
   (Name_var x, entry 4 Name_mode.Normal);
   (Name_var y, entry 5 Name_mode.Normal)].

Definition resolver (n : name) : Binding_time.With_name_mode.t :=
  Binding_time.With_name_mode.imported_variables.

(* ------------------------------------------------------------------------ *)
(* Two variables                                                            *)
(* ------------------------------------------------------------------------ *)

(* [y] is demoted to [x], which was bound first. *)
Definition x_y : Aliases.t :=
  Aliases.make [(Name_var y, Var x)]
    [(Name_var x, [(Name_var y, Name_mode.Normal)])] [].

(* Whichever of the two is given first, the later is demoted to the
   earlier. *)
Example add_two_variables :
  Aliases.add resolver times Aliases.empty (Var y) (Var x)
  = Some (Or_bottom.Ok (Aliases.make_add_result x_y (Name_var y) (Var x)))
  ∧ Aliases.add resolver times Aliases.empty (Var x) (Var y)
    = Some (Or_bottom.Ok (Aliases.make_add_result x_y (Name_var y) (Var x))).
Proof. split; reflexivity. Qed.

Example canonical_of_two_variables :
  Aliases.get_canonical_ignoring_name_mode x_y (Name_var y) = Var x
  ∧ Aliases.get_canonical_ignoring_name_mode x_y (Name_var x) = Var x
  ∧ Aliases.get_canonical_ignoring_name_mode x_y (Name_var w) = Var w.
Proof. repeat split. Qed.

(* An environment in which the two have the same value respects the
   structure... *)
Example two_variables_respected :
  aliases_respected x_y [(x, Value_const five); (y, Value_const five)].
Proof. respected_by_pairs. Qed.

(* ... and one in which they have different values does not. *)
Example two_variables_not_respected :
  ~ aliases_respected x_y [(x, Value_const five); (y, Value_const six)].
Proof.
  intros [Hcanonical _].
  discriminate (Hcanonical (Name_var y) (Var x) eq_refl).
Qed.

(* An environment that binds neither respects the structure; one that
   binds only one of them does not. *)
Example two_unbound_variables_respected : aliases_respected x_y [].
Proof. respected_by_pairs. Qed.

Example one_unbound_variable_not_respected :
  ~ aliases_respected x_y [(x, Value_const five)].
Proof.
  intros [Hcanonical _].
  discriminate (Hcanonical (Name_var y) (Var x) eq_refl).
Qed.

(* The structure is well formed for that typing environment: the
   statements that ask for it are about something. *)
Example two_variables_well_formed : aliases_well_formed resolver times x_y.
Proof.
  (* What is demoted, and what is listed. *)
  assert (Hdemoted :
    ∀ (n : name) (canonical_element : simple),
      demoted_to x_y n canonical_element ->
      n = Name_var y ∧ canonical_element = Var x).
  { intros n canonical_element Hdemoted. unfold demoted_to in Hdemoted.
    cbn [x_y Aliases.canonical_elements Keyed.lookup] in Hdemoted.
    destruct (name_eqb n (Name_var y)) eqn:Hn; [ | discriminate Hdemoted ].
    apply name_eqb_eq in Hn. injection Hdemoted as <-. auto. }
  assert (Hlisted :
    ∀ (canonical_element : simple) (n : name) (name_mode : Name_mode.t),
      Keyed.lookup name_eqb n
        (Aliases.get_aliases_of_canonical_element x_y canonical_element)
      = Some name_mode ->
      n = Name_var y ∧ canonical_element = Var x
      ∧ name_mode = Name_mode.Normal).
  { intros canonical_element n name_mode Hlookup.
    assert (Hx : canonical_element = Var x).
    { destruct canonical_element as [v | sym | c];
        try discriminate Hlookup.
      unfold Aliases.get_aliases_of_canonical_element in Hlookup.
      cbn [x_y Aliases.aliases_of_canonical_names Keyed.lookup] in Hlookup.
      destruct (name_eqb (Name_var v) (Name_var x)) eqn:Hv;
        [ | discriminate Hlookup ].
      apply name_eqb_eq in Hv. injection Hv as ->. reflexivity. }
    subst canonical_element.
    change (Keyed.lookup name_eqb n [(Name_var y, Name_mode.Normal)]
            = Some name_mode) in Hlookup.
    cbn [Keyed.lookup] in Hlookup.
    destruct (name_eqb n (Name_var y)) eqn:Hn; [ | discriminate Hlookup ].
    apply name_eqb_eq in Hn. injection Hlookup as <-. auto. }
  split; [ split | split ].
  - intros n canonical_element Hd.
    destruct (Hdemoted n canonical_element Hd) as [-> ->]. reflexivity.
  - intros n canonical_element. split.
    + intros Hd. destruct (Hdemoted n canonical_element Hd) as [-> ->].
      reflexivity.
    + intros Hl. apply mem_lookup in Hl as [name_mode Hl].
      destruct (Hlisted canonical_element n name_mode Hl) as (-> & -> & _).
      reflexivity.
  - intros n canonical_element Hd.
    destruct (Hdemoted n canonical_element Hd) as [-> ->]. reflexivity.
  - intros canonical_element n name_mode Hl.
    destruct (Hlisted canonical_element n name_mode Hl) as (-> & -> & ->).
    reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(* A variable and a constant                                                *)
(* ------------------------------------------------------------------------ *)

(* The constant is the canonical element, whichever is given first. *)
Definition x_five : Aliases.t :=
  Aliases.make [(Name_var x, Const five)] []
    [(five, [(Name_var x, Name_mode.Normal)])].

Example add_variable_constant :
  Aliases.add resolver times Aliases.empty (Var x) (Const five)
  = Some
      (Or_bottom.Ok (Aliases.make_add_result x_five (Name_var x) (Const five)))
  ∧ Aliases.add resolver times Aliases.empty (Const five) (Var x)
    = Some
        (Or_bottom.Ok
           (Aliases.make_add_result x_five (Name_var x) (Const five))).
Proof. split; reflexivity. Qed.

(* The variable must hold the constant: not another, and not nothing. *)
Example constant_respected :
  aliases_respected x_five [(x, Value_const five)].
Proof. respected_by_pairs. Qed.

Example constant_not_respected :
  ~ aliases_respected x_five [(x, Value_const six)]
  ∧ ~ aliases_respected x_five [].
Proof.
  split; intros [Hcanonical _];
    discriminate (Hcanonical (Name_var x) (Const five) eq_refl).
Qed.

(* A class with a constant and two variables: [y] and [x] are aliases,
   then [x] is the constant. Both variables now have it as their
   canonical element. *)
Example add_constant_to_class :
  ∃ t : Aliases.t,
    Aliases.add resolver times x_y (Var x) (Const five)
    = Some (Or_bottom.Ok (Aliases.make_add_result t (Name_var x) (Const five)))
    ∧ Aliases.get_canonical_ignoring_name_mode t (Name_var y) = Const five
    ∧ Aliases.get_canonical_ignoring_name_mode t (Name_var x) = Const five.
Proof. eexists. repeat split. Qed.

(* Two different constants are never equal: bottom. *)
Example add_two_constants :
  Aliases.add resolver times Aliases.empty (Const five) (Const six)
  = Some Or_bottom.Bottom.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(* A variable and a symbol                                                  *)
(* ------------------------------------------------------------------------ *)

(* The symbol is the canonical element, whichever is given first. *)
Definition x_s : Aliases.t :=
  Aliases.make [(Name_var x, Symbol s)]
    [(Name_symbol s, [(Name_var x, Name_mode.Normal)])] [].

Example add_variable_symbol :
  Aliases.add resolver times Aliases.empty (Var x) (Symbol s)
  = Some (Or_bottom.Ok (Aliases.make_add_result x_s (Name_var x) (Symbol s)))
  ∧ Aliases.add resolver times Aliases.empty (Symbol s) (Var x)
    = Some
        (Or_bottom.Ok (Aliases.make_add_result x_s (Name_var x) (Symbol s))).
Proof. split; reflexivity. Qed.

(* The variable must hold the symbol itself, the pointer. A closure made
   by a [Let] is another value, whatever the symbol is bound to. *)
Example symbol_respected : aliases_respected x_s [(x, Value_symbol s)].
Proof. respected_by_pairs. Qed.

Example symbol_not_respected :
  ~ aliases_respected x_s [(x, Value_closure 1%positive [])].
Proof.
  intros [Hcanonical _].
  discriminate (Hcanonical (Name_var x) (Symbol s) eq_refl).
Qed.

(* Two symbols are not ordered. [add] demotes the first of the two it is
   given, and the result does not pass the check that the OCaml makes
   under its flag for invariants. *)
Example add_two_symbols :
  ∃ t : Aliases.t,
    Aliases.add resolver times Aliases.empty (Symbol s) (Symbol s')
    = Some
        (Or_bottom.Ok (Aliases.make_add_result t (Name_symbol s) (Symbol s')))
    ∧ Aliases.invariant resolver times t = false.
Proof. eexists. split; reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(* The canonical element at a name mode                                     *)
(* ------------------------------------------------------------------------ *)

(* A typing environment in which [w], bound first, exists only in types,
   and [x] and [y] have values at run time. *)
Definition times_in_types
    : Keyed.finite_map name (unit * Binding_time.With_name_mode.t) :=
  [(Name_var w, entry 3 Name_mode.In_types);
   (Name_var x, entry 4 Name_mode.Normal);
   (Name_var y, entry 5 Name_mode.Normal)].

(* [x] and [y] are demoted to [w]. *)
Definition w_x_y : Aliases.t :=
  Aliases.make [(Name_var y, Var w); (Name_var x, Var w)]
    [(Name_var w,
      [(Name_var y, Name_mode.Normal); (Name_var x, Name_mode.Normal)])]
    [].

Example add_in_types :
  ∃ t : Aliases.t,
    Aliases.add resolver times_in_types Aliases.empty (Var x) (Var w)
    = Some (Or_bottom.Ok (Aliases.make_add_result t (Name_var x) (Var w)))
    ∧ ∃ t' : Aliases.t,
        Aliases.add resolver times_in_types t (Var y) (Var w)
        = Some (Or_bottom.Ok (Aliases.make_add_result t' (Name_var y) (Var w)))
        ∧ ∀ n : name,
            Aliases.get_canonical_ignoring_name_mode t' n
            = Aliases.get_canonical_ignoring_name_mode w_x_y n.
Proof.
  eexists. split; [ reflexivity | ]. eexists. split; [ reflexivity | ].
  intros n. unfold Aliases.get_canonical_ignoring_name_mode.
  rewrite !canonical_of_name. simpl.
  destruct (name_eqb n (Name_var y)); reflexivity.
Qed.

(* The canonical element of [y] is [w], which has no value at run time.
   Asked for a name that has one, the answer is [x], the earliest alias
   that has; in a scope where [x] is not (only what was bound at time 5
   or later is), it is [y] itself. Asked for a name that may occur in
   types, the answer is [w]. *)
Example canonical_at_normal :
  Aliases.get_canonical_element_exn resolver times_in_types w_x_y (Var y)
    Name_mode.Normal Name_mode.Normal 3
  = Some (Var x)
  ∧ Aliases.get_canonical_element_exn resolver times_in_types w_x_y (Var y)
      Name_mode.Normal Name_mode.Normal 5
    = Some (Var y)
  ∧ Aliases.get_canonical_element_exn resolver times_in_types w_x_y (Var y)
      Name_mode.Normal Name_mode.In_types 3
    = Some (Var w).
Proof. repeat split. Qed.

(* Where no alias may be used, there is no answer: here nothing bound
   before time 6 is in scope. *)
Example canonical_at_normal_none :
  Aliases.get_canonical_element_exn resolver times_in_types w_x_y (Var y)
    Name_mode.Normal Name_mode.Normal 6
  = None.
Proof. reflexivity. Qed.

(* The same with [y] a name for debugging information. Asked for a name
   that may be used there, the answer for [x] is [y], recorded as
   [Phantom], though [x] itself, recorded as [Normal] and bound earlier,
   may be used there too: the aliases of the least name mode that will
   do come first. *)
Definition times_phantom
    : Keyed.finite_map name (unit * Binding_time.With_name_mode.t) :=
  [(Name_var w, entry 3 Name_mode.In_types);
   (Name_var x, entry 4 Name_mode.Normal);
   (Name_var y, entry 5 Name_mode.Phantom)].

Definition w_x_y_phantom : Aliases.t :=
  Aliases.make [(Name_var y, Var w); (Name_var x, Var w)]
    [(Name_var w,
      [(Name_var y, Name_mode.Phantom); (Name_var x, Name_mode.Normal)])]
    [].

Example canonical_at_phantom :
  Aliases.get_canonical_element_exn resolver times_phantom w_x_y_phantom
    (Var x) Name_mode.Normal Name_mode.Phantom 3
  = Some (Var y)
  ∧ Aliases.get_canonical_element_exn resolver times_phantom w_x_y_phantom
      (Var x) Name_mode.Normal Name_mode.Normal 3
    = Some (Var x).
Proof. split; reflexivity. Qed.

End Examples.
