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


(* Proofs of the statements of FlambdaJoinTypesSpec.v. Nothing here
   needs review. *)

From Stdlib Require Import ZArith List Bool PeanoNat Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaEnvAliases FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaJoinEnv FlambdaJoinTypes FlambdaJoinSpec FlambdaJoinProofs
  FlambdaJoinTypesSpec.
Import ListNotations.

(* ======================================================================== *)
(* Sets of numbers, and lists of contributors                               *)
(* ======================================================================== *)

Lemma numbers_union_in (n : Z) (numbers numbers' : list Z) :
  n ∈ numbers_union numbers numbers' <-> n ∈ numbers ∨ n ∈ numbers'.
Proof.
  unfold numbers_union.
  rewrite <- (keyed_among_in Z Z.eqb Z.eqb_eq n (Keyed.dedup Z.eqb _)).
  rewrite (keyed_among_dedup Z Z.eqb Z.eqb_eq).
  rewrite (keyed_among_in Z Z.eqb Z.eqb_eq).
  apply in_app_iff.
Qed.

(* What [known_contents] answers: the contents of the list, before what
   it was given to start with. *)
Lemma known_contents_spec {A : Type}
    (or_unknowns : list (Index.t * Or_unknown.t A)) :
  ∀ (acc contents : list (Index.t * A)),
    known_contents acc or_unknowns = Some contents ->
    map fst contents = rev (map fst or_unknowns) ++ map fst acc
    ∧ (∀ (index : Index.t) (a : A),
         In (index, a) contents ->
         In (index, a) acc ∨ In (index, Or_unknown.Known a) or_unknowns)
    ∧ (∀ (index : Index.t) (a : Or_unknown.t A),
         In (index, a) or_unknowns ->
         ∃ a' : A, a = Or_unknown.Known a' ∧ In (index, a') contents)
    ∧ ∀ (index : Index.t) (a : A), In (index, a) acc -> In (index, a) contents.
Proof.
  induction or_unknowns as [ | [id [a | ]] or_unknowns IH];
    intros acc contents Hcontents; simpl in Hcontents.
  - injection Hcontents as <-. simpl. repeat split; auto.
    intros index a [].
  - destruct (IH _ _ Hcontents) as (Hfst & Hfrom & Hto & Hacc).
    repeat split.
    + rewrite Hfst. simpl. rewrite <- app_assoc. reflexivity.
    + intros index a' Hin.
      destruct (Hfrom index a' Hin) as [[Heq | Hin'] | Hin'].
      * right. left. congruence.
      * left. exact Hin'.
      * right. right. exact Hin'.
    + intros index a' [Heq | Hin].
      * injection Heq as <- <-. exists a. split; [ reflexivity | ].
        apply Hacc. left. reflexivity.
      * exact (Hto index a' Hin).
    + intros index a' Hin. apply Hacc. right. exact Hin.
  - discriminate.
Qed.

(* A list made of another element by element, each with its index, or
   nothing if an element gives nothing: what the functions of the
   traversal that gather a list with an exception compute. *)
Fixpoint indexed_map_opt {A B : Type} (f : Index.t -> A -> option B)
    (l : list (Index.t * A)) : option (list (Index.t * B)) :=
  match l with
  | [] => Some []
  | (id, a) :: l =>
    match f id a, indexed_map_opt f l with
    | Some b, Some l' => Some ((id, b) :: l')
    | _, _ => None
    end
  end.

Lemma indexed_map_opt_spec {A B : Type} (f : Index.t -> A -> option B)
    (l : list (Index.t * A)) :
  ∀ l' : list (Index.t * B),
    indexed_map_opt f l = Some l' ->
    map fst l' = map fst l
    ∧ (∀ (index : Index.t) (a : A),
         In (index, a) l -> ∃ b : B, f index a = Some b ∧ In (index, b) l')
    ∧ ∀ (index : Index.t) (b : B),
        In (index, b) l' -> ∃ a : A, f index a = Some b ∧ In (index, a) l.
Proof.
  induction l as [ | [id a] l IH]; intros l' Hl'; simpl in Hl'.
  - injection Hl' as <-. split; [ reflexivity | ].
    split; [ intros ? ? [] | intros ? ? [] ].
  - destruct (f id a) as [b | ] eqn:Hb; [ | discriminate ].
    destruct (indexed_map_opt f l) as [rest | ]; [ | discriminate ].
    injection Hl' as <-.
    destruct (IH rest eq_refl) as (Hfst & Hto & Hfrom).
    split; [ simpl; rewrite Hfst; reflexivity | ].
    split.
    + intros index a' [[= <- <-] | Hin].
      * exists b. split; [ exact Hb | left; reflexivity ].
      * destruct (Hto index a' Hin) as (b' & Hb' & Hin').
        exists b'. split; [ exact Hb' | right; exact Hin' ].
    + intros index b' [[= <- <-] | Hin].
      * exists a. split; [ exact Hb | left; reflexivity ].
      * destruct (Hfrom index b' Hin) as (a' & Ha' & Hin').
        exists a'. split; [ exact Ha' | right; exact Hin' ].
Qed.

(* The lists that the traversal gathers, as such lists. *)
Lemma all_known_eq {A : Type} (l : list (Index.t * Or_unknown.t A)) :
  all_known l
  = indexed_map_opt
      (fun _ a =>
         match a with
         | Or_unknown.Known a => Some a
         | Or_unknown.Unknown => None
         end)
      l.
Proof.
  induction l as [ | [id [a | ]] l IH]; simpl; [ reflexivity | | reflexivity ].
  rewrite IH. destruct (indexed_map_opt _ l); reflexivity.
Qed.

Lemma alias_simples_eq (ts : list (Index.t * flambda_type)) :
  alias_simples ts = indexed_map_opt (fun _ ty => get_alias_opt ty) ts.
Proof.
  induction ts as [ | [id ty] ts IH]; simpl; [ reflexivity | ].
  rewrite IH. destruct (get_alias_opt ty); reflexivity.
Qed.

Lemma fields_at_eq (index : nat) (fields : list (Index.t * list flambda_type)) :
  fields_at index fields
  = indexed_map_opt (fun _ fields_of_id => nth_error fields_of_id index)
      fields.
Proof.
  induction fields as [ | [id fields_of_id] fields IH]; simpl;
    [ reflexivity | ].
  rewrite IH. destruct (nth_error fields_of_id index); reflexivity.
Qed.

(* ======================================================================== *)
(* The fold over a map that threads a state                                 *)
(* ======================================================================== *)

Section Fold.

Context {K : Type} (eqb : K -> K -> bool) (Heqb : decides_equality eqb).
Context {S : Type} (P : S -> Prop) (R : S -> S -> Prop).

Hypothesis R_refl : ∀ s : S, R s s.
Hypothesis R_trans : ∀ s1 s2 s3 : S, R s1 s2 -> R s2 s3 -> R s1 s3.

Lemma among_cons_other (key first : K) (keys : list K) :
  Keyed.among eqb first keys = false ->
  Keyed.among eqb key keys = true ->
  eqb key first = false.
Proof.
  intros Hfirst Hkey.
  destruct (keyed_eqb_spec eqb Heqb key first) as [-> | _];
    [ congruence | reflexivity ].
Qed.

(* What the fold answers, if each step keeps [P] and takes the state
   to one that [R] relates to it: the map answered has no key twice;
   what it binds a key to was answered by the step of that key, at a
   state between the first and the last; and a key that it does not
   bind had a step that answered nothing. *)
Lemma tabulate_fold_opt_spec {A : Type} (f : K -> S -> option (option A * S))
    (keys : list K) :
  Keyed.distinct eqb keys = true ->
  (∀ (key : K) (s : S) (a : option A) (s' : S),
     Keyed.among eqb key keys = true ->
     P s -> f key s = Some (a, s') -> P s' ∧ R s s') ->
  ∀ (s : S) (out : Keyed.finite_map K A) (s' : S),
    P s ->
    Keyed_fold.tabulate_fold_opt f keys s = Some (out, s') ->
    P s' ∧ R s s'
    ∧ (∀ (key : K) (a : A),
         In (key, a) out -> Keyed.lookup eqb key out = Some a)
    ∧ (∀ (key : K) (a : A),
         Keyed.lookup eqb key out = Some a ->
         Keyed.among eqb key keys = true
         ∧ ∃ s1 s2 : S,
             P s1 ∧ R s s1 ∧ f key s1 = Some (Some a, s2) ∧ R s2 s')
    ∧ ∀ key : K,
        Keyed.among eqb key keys = true ->
        (∃ a : A, Keyed.lookup eqb key out = Some a)
        ∨ ∃ s1 s2 : S, P s1 ∧ R s s1 ∧ f key s1 = Some (None, s2).
Proof.
  induction keys as [ | first keys IH]; intros Hdistinct Hstep s out s' HP
    Hfold; simpl in Hfold.
  - injection Hfold as <- <-.
    split; [ exact HP | ]. split; [ apply R_refl | ].
    split; [ intros ? ? [] | ].
    split; [ intros ? ? [=] | intros ? [=] ].
  - simpl in Hdistinct. apply andb_true_iff in Hdistinct as [Hfirst Hdistinct].
    apply negb_true_iff in Hfirst.
    destruct (f first s) as [[a s1] | ] eqn:Hf; [ | discriminate ].
    destruct (Keyed_fold.tabulate_fold_opt f keys s1) as [[rest s2] | ]
      eqn:Hrest; [ | discriminate ].
    injection Hfold as <- <-.
    assert (Hfirst_among : Keyed.among eqb first (first :: keys) = true).
    { rewrite keyed_among_cons, (keyed_eqb_refl eqb Heqb). reflexivity. }
    destruct (Hstep first s a s1 Hfirst_among HP Hf) as (HP1 & HR1).
    assert (Hstep' :
      ∀ (key : K) (s : S) (a : option A) (s' : S),
        Keyed.among eqb key keys = true ->
        P s -> f key s = Some (a, s') -> P s' ∧ R s s').
    { intros key s0 a0 s0' Hkey. apply Hstep.
      rewrite keyed_among_cons, Hkey. apply orb_true_r. }
    destruct (IH Hdistinct Hstep' s1 rest s2 HP1 Hrest)
      as (HP2 & HR2 & Hin & Hfound & Hall).
    split; [ exact HP2 | ]. split; [ exact (R_trans _ _ _ HR1 HR2) | ].
    (* A key of the rest is not the first. *)
    assert (Hother :
      ∀ (key : K) (b : A),
        Keyed.lookup eqb key rest = Some b -> eqb key first = false).
    { intros key b Hkey. destruct (Hfound key b Hkey) as (Hamong & _).
      exact (among_cons_other key first keys Hfirst Hamong). }
    split; [ | split ].
    + intros key b Hb. destruct a as [a | ].
      * destruct Hb as [[= <- <-] | Hb].
        -- apply (keyed_lookup_head eqb Heqb).
        -- pose proof (Hin key b Hb) as Hkey. simpl.
           rewrite (Hother key b Hkey). exact Hkey.
      * exact (Hin key b Hb).
    + intros key b Hkey.
      assert (Hrest_case :
        Keyed.lookup eqb key rest = Some b ->
        Keyed.among eqb key (first :: keys) = true
        ∧ ∃ s1' s2' : S,
            P s1' ∧ R s s1' ∧ f key s1' = Some (Some b, s2') ∧ R s2' s2).
      { intros Hkey'.
        destruct (Hfound key b Hkey') as (Hamong & s1' & s2' & HP' & HR' & Hf'
                                          & HR'').
        split; [ rewrite keyed_among_cons, Hamong; apply orb_true_r | ].
        exists s1', s2'. split; [ exact HP' | ].
        split; [ exact (R_trans _ _ _ HR1 HR') | ].
        split; [ exact Hf' | exact HR'' ]. }
      destruct a as [a | ]; [ | exact (Hrest_case Hkey) ].
      simpl in Hkey.
      destruct (keyed_eqb_spec eqb Heqb key first) as [-> | _];
        [ | exact (Hrest_case Hkey) ].
      injection Hkey as <-.
      split; [ exact Hfirst_among | ].
      exists s, s1. split; [ exact HP | ]. split; [ apply R_refl | ].
      split; [ exact Hf | exact HR2 ].
    + intros key Hkey. rewrite keyed_among_cons in Hkey.
      destruct (keyed_eqb_spec eqb Heqb key first) as [Heq | Hne].
      * subst key. destruct a as [a | ].
        -- left. exists a. apply (keyed_lookup_head eqb Heqb).
        -- right. exists s, s1. split; [ exact HP | ].
           split; [ apply R_refl | exact Hf ].
      * simpl in Hkey. destruct (Hall key Hkey) as [[b Hb] | Hnone].
        -- left. exists b. destruct a as [a | ]; [ | exact Hb ].
           simpl. rewrite (Hother key b Hb). exact Hb.
        -- right. destruct Hnone as (s1' & s2' & HP' & HR' & Hf').
           exists s1', s2'. split; [ exact HP' | ].
           split; [ exact (R_trans _ _ _ HR1 HR') | exact Hf' ].
Qed.

(* The same of the fold over the bindings of a map. *)
Lemma filter_map_fold_spec {A B : Type}
    (g : K -> B -> S -> option (option A * S)) (m : Keyed.finite_map K B) :
  (∀ (key : K) (b : B) (s : S) (a : option A) (s' : S),
     Keyed.lookup eqb key m = Some b ->
     P s -> g key b s = Some (a, s') -> P s' ∧ R s s') ->
  ∀ (s : S) (out : Keyed.finite_map K A) (s' : S),
    P s ->
    Keyed_fold.filter_map_fold eqb g m s = Some (out, s') ->
    P s' ∧ R s s'
    ∧ (∀ (key : K) (a : A),
         In (key, a) out -> Keyed.lookup eqb key out = Some a)
    ∧ (∀ (key : K) (a : A),
         Keyed.lookup eqb key out = Some a ->
         ∃ (b : B) (s1 s2 : S),
           Keyed.lookup eqb key m = Some b
           ∧ P s1 ∧ R s s1 ∧ g key b s1 = Some (Some a, s2) ∧ R s2 s')
    ∧ ∀ (key : K) (b : B),
        Keyed.lookup eqb key m = Some b ->
        (∃ a : A, Keyed.lookup eqb key out = Some a)
        ∨ ∃ s1 s2 : S, P s1 ∧ R s s1 ∧ g key b s1 = Some (None, s2).
Proof.
  intros Hstep s out s' HP Hfold.
  unfold Keyed_fold.filter_map_fold, Keyed_fold.filter_map_fold_on in Hfold.
  set (f :=
    fun (key : K) (s : S) =>
      match Keyed.lookup eqb key m with
      | Some b => g key b s
      | None => Some (None, s)
      end) in Hfold.
  assert (Hstep' :
    ∀ (key : K) (s : S) (a : option A) (s' : S),
      Keyed.among eqb key (Keyed.domain eqb m) = true ->
      P s -> f key s = Some (a, s') -> P s' ∧ R s s').
  { intros key s0 a s0' _ HP0 Hf. unfold f in Hf.
    destruct (Keyed.lookup eqb key m) as [b | ] eqn:Hb.
    - exact (Hstep key b s0 a s0' Hb HP0 Hf).
    - injection Hf as <- <-. split; [ exact HP0 | apply R_refl ]. }
  destruct
    (tabulate_fold_opt_spec f (Keyed.domain eqb m)
       (keyed_domain_distinct K eqb Heqb B m) Hstep' s out s' HP Hfold)
    as (HP' & HR & Hin & Hfound & Hall).
  split; [ exact HP' | ]. split; [ exact HR | ]. split; [ exact Hin | ].
  split.
  - intros key a Ha.
    destruct (Hfound key a Ha) as (_ & s1 & s2 & HP1 & HR1 & Hf & HR2).
    unfold f in Hf. destruct (Keyed.lookup eqb key m) as [b | ];
      [ | discriminate ].
    exists b, s1, s2. repeat split; assumption.
  - intros key b Hb.
    assert (Hamong : Keyed.among eqb key (Keyed.domain eqb m) = true).
    { rewrite (keyed_among_domain K eqb Heqb). unfold Keyed.is_bound.
      rewrite Hb. reflexivity. }
    destruct (Hall key Hamong) as [Ha | (s1 & s2 & HP1 & HR1 & Hf)];
      [ left; exact Ha | right ].
    unfold f in Hf. rewrite Hb in Hf. exists s1, s2. repeat split; assumption.
Qed.

End Fold.

(* ======================================================================== *)
(* The components of products, index by index                               *)
(* ======================================================================== *)

Lemma gather_components_fold {A : Type} (g : positive)
    (rest : list (Index.t * finite_map A)) :
  ∀ acc : finite_map (list (Index.t * A)),
    lookup g
      (List.fold_left
         (fun components_by_index indexed_product2 =>
            merge
              (fun vals_opt val2_opt =>
                 match vals_opt, val2_opt with
                 | None, _ | _, None => None
                 | Some vals, Some val2 =>
                   Some ((fst indexed_product2, val2) :: vals)
                 end)
              components_by_index (snd indexed_product2))
         rest acc)
    = match
        lookup g acc,
        indexed_map_opt (fun _ product => lookup g product) rest
      with
      | Some l, Some r => Some (rev r ++ l)
      | _, _ => None
      end.
Proof.
  induction rest as [ | [id2 p2] rest IH]; intros acc.
  - simpl. destruct (lookup g acc); reflexivity.
  - cbn [List.fold_left indexed_map_opt fst snd].
    rewrite IH, lookup_merge by reflexivity.
    destruct (lookup g acc) as [l | ], (lookup g p2) as [v | ],
      (indexed_map_opt (fun _ product => lookup g product) rest) as [r | ];
      try reflexivity.
    simpl. rewrite <- app_assoc. reflexivity.
Qed.

(* What the gathering binds an index to: the components of the
   products for it, the last product's first, if every product has
   one. *)
Lemma gather_components_spec {A : Type}
    (products : list (Index.t * finite_map A)) (g : positive)
    (components : list (Index.t * A)) :
  lookup g (gather_components products) = Some components ->
  map fst components = rev (map fst products)
  ∧ (∀ (index : Index.t) (product : finite_map A),
       In (index, product) products ->
       ∃ a : A, lookup g product = Some a ∧ In (index, a) components)
  ∧ ∀ (index : Index.t) (a : A),
      In (index, a) components ->
      ∃ product : finite_map A,
        lookup g product = Some a ∧ In (index, product) products.
Proof.
  destruct products as [ | [id1 p1] rest]; [ discriminate | ].
  unfold gather_components.
  rewrite gather_components_fold, lookup_map_values.
  intros Hcomponents.
  assert (Hall :
    ∃ l : list (Index.t * A),
      indexed_map_opt (fun _ product => lookup g product) ((id1, p1) :: rest)
      = Some l
      ∧ components = rev l).
  { cbn [indexed_map_opt].
    destruct (lookup g p1) as [v | ]; [ | discriminate ].
    destruct (indexed_map_opt (fun _ product => lookup g product) rest)
      as [r | ]; [ | discriminate ].
    injection Hcomponents as <-. exists ((id1, v) :: r).
    split; reflexivity. }
  destruct Hall as (l & Hl & ->).
  destruct (indexed_map_opt_spec _ _ l Hl) as (Hfst & Hto & Hfrom).
  split; [ rewrite map_rev, Hfst; reflexivity | ].
  split.
  - intros index product Hin.
    destruct (Hto index product Hin) as (a & Ha & Hin').
    exists a. split; [ exact Ha | apply in_rev in Hin'; exact Hin' ].
  - intros index a Hin. apply in_rev in Hin.
    destruct (Hfrom index a Hin) as (product & Ha & Hin').
    exists product. split; assumption.
Qed.

(* ======================================================================== *)
(* The cases of row-like structures, key by key                             *)
(* ======================================================================== *)

Section Gather_known.

Context {K value other : Type} (eqb : K -> K -> bool)
  (Heqb : decides_equality eqb) (of_other : other -> value).

Local Abbreviation input :=
  (Index.t * (Keyed.finite_map K value * Or_bottom.t other))%type.

(* What a row-like structure gives for a key: its case for the key, or
   failing one its case for the other keys. *)
Definition contribution (key : K) (i : input) : list (Index.t * value) :=
  match Keyed.lookup eqb key (fst (snd i)) with
  | Some v => [(fst i, v)]
  | None =>
    match snd (snd i) with
    | Or_bottom.Ok o => [(fst i, of_other o)]
    | Or_bottom.Bottom => []
    end
  end.

Definition other_of (i : input) : list (Index.t * value) :=
  match snd (snd i) with
  | Or_bottom.Ok o => [(fst i, of_other o)]
  | Or_bottom.Bottom => []
  end.

Definition bound_in_some (key : K) (inputs : list input) : bool :=
  existsb (fun i => Keyed.is_bound eqb key (fst (snd i))) inputs.

Lemma contributions_unbound (key : K) (inputs : list input) :
  bound_in_some key inputs = false ->
  flat_map (contribution key) inputs = flat_map other_of inputs.
Proof.
  induction inputs as [ | i inputs IH]; simpl; [ reflexivity | ].
  intros Hbound. apply orb_false_iff in Hbound as [Hi Hrest].
  rewrite (IH Hrest). f_equal. unfold contribution, Keyed.is_bound in *.
  destruct (Keyed.lookup eqb key (fst (snd i))); [ discriminate | reflexivity ].
Qed.

Lemma add_other_eq (acc : list (Index.t * value)) (i : input) :
  add_other of_other acc (fst i) (snd (snd i)) = rev (other_of i) ++ acc.
Proof.
  unfold add_other, other_of. destruct (snd (snd i)); reflexivity.
Qed.

Local Abbreviation gather_step :=
  (fun (acc :
          Keyed.finite_map K (list (Index.t * value))
          * list (Index.t * value)) (i : input) =>
     let id2 := fst i in
     let map2 := fst (snd i) in
     let other2 := snd (snd i) in
     (Keyed.merge eqb
        (fun vals_opt val2_opt =>
           match vals_opt, val2_opt with
           | None, None => None
           | None, Some val2 => Some ((id2, val2) :: snd acc)
           | Some vals, None => Some (add_other of_other vals id2 other2)
           | Some vals, Some val2 => Some ((id2, val2) :: vals)
           end)
        (fst acc) map2,
      add_other of_other (snd acc) id2 other2)).

Lemma gather_known_fold (rest : list input) :
  ∀ (done : list input)
    (acc :
       Keyed.finite_map K (list (Index.t * value)) * list (Index.t * value)),
    (∀ key : K,
       Keyed.lookup eqb key (fst acc)
       = if bound_in_some key done
         then Some (rev (flat_map (contribution key) done))
         else None) ->
    snd acc = rev (flat_map other_of done) ->
    ∀ key : K,
      Keyed.lookup eqb key (fst (List.fold_left gather_step rest acc))
      = if bound_in_some key (done ++ rest)
        then Some (rev (flat_map (contribution key) (done ++ rest)))
        else None.
Proof.
  induction rest as [ | i rest IH]; intros done acc Hmaps Hothers key.
  - rewrite app_nil_r. apply Hmaps.
  - cbn [List.fold_left].
    replace (done ++ i :: rest) with ((done ++ [i]) ++ rest)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
    + intros key'. cbn [fst snd].
      rewrite (keyed_lookup_merge K eqb Heqb) by reflexivity.
      rewrite Hmaps. unfold bound_in_some.
      rewrite existsb_app, flat_map_app, rev_app_distr. cbn [existsb flat_map].
      rewrite orb_false_r, app_nil_r.
      fold (bound_in_some key' done).
      destruct (bound_in_some key' done) eqn:Hdone.
      * cbn [orb]. unfold contribution.
        destruct (Keyed.lookup eqb key' (fst (snd i))) as [val2 | ];
          [ reflexivity | ].
        rewrite add_other_eq. reflexivity.
      * cbn [orb]. rewrite (contributions_unbound key' done Hdone), <- Hothers.
        unfold contribution, Keyed.is_bound.
        destruct (Keyed.lookup eqb key' (fst (snd i))) as [val2 | ];
          reflexivity.
    + cbn [fst snd]. rewrite add_other_eq, Hothers, flat_map_app, rev_app_distr.
      cbn [flat_map]. rewrite app_nil_r. reflexivity.
Qed.

(* What the gathering binds a key to: what each row-like structure
   gives for it, the last one's first, if one of them has a case for
   it. *)
Lemma gather_known_lookup (inputs : list input) (key : K) :
  Keyed.lookup eqb key (gather_known eqb of_other inputs)
  = if bound_in_some key inputs
    then Some (rev (flat_map (contribution key) inputs))
    else None.
Proof.
  destruct inputs as [ | i1 rest]; [ reflexivity | ].
  destruct i1 as [id1 [map1 other1]]. unfold gather_known.
  apply (gather_known_fold rest [(id1, (map1, other1))]).
  - intros key'. cbn [fst snd].
    rewrite keyed_lookup_map_values. unfold bound_in_some.
    cbn [existsb flat_map fst snd]. rewrite orb_false_r, app_nil_r.
    unfold contribution, Keyed.is_bound. cbn [fst snd].
    destruct (Keyed.lookup eqb key' map1); reflexivity.
  - cbn [fst snd flat_map]. rewrite app_nil_r.
    change (add_other of_other [] id1 other1)
      with (add_other of_other [] (fst (id1, (map1, other1)))
              (snd (snd (id1, (map1, other1))))).
    rewrite add_other_eq, app_nil_r. reflexivity.
Qed.

Lemma contribution_fst (key : K) (i : input) (index : Index.t) (v : value) :
  In (index, v) (contribution key i) -> index = fst i.
Proof.
  unfold contribution.
  destruct (Keyed.lookup eqb key (fst (snd i)));
    [ intros [[= <- _] | []]; reflexivity | ].
  destruct (snd (snd i)); [ | intros [] ].
  intros [[= <- _] | []]. reflexivity.
Qed.

Lemma contributions_distinct (key : K) (inputs : list input) :
  NoDup (map fst inputs) ->
  NoDup (map fst (flat_map (contribution key) inputs)).
Proof.
  induction inputs as [ | i inputs IH]; simpl; intros Hdistinct;
    [ apply NoDup_nil | ].
  inversion Hdistinct as [ | ? ? Hi Hrest]. subst.
  rewrite map_app.
  assert (Hfresh : ¬ In (fst i) (map fst (flat_map (contribution key) inputs))).
  { intros Hin. apply Hi. apply in_map_iff in Hin as ([index v] & Heq & Hin).
    simpl in Heq. subst index.
    apply in_flat_map in Hin as (i' & Hin' & Hv).
    apply contribution_fst in Hv. rewrite Hv. apply in_map. exact Hin'. }
  unfold contribution at 1.
  destruct (Keyed.lookup eqb key (fst (snd i))).
  - simpl. apply NoDup_cons; [ exact Hfresh | exact (IH Hrest) ].
  - destruct (snd (snd i)); simpl;
      [ apply NoDup_cons; [ exact Hfresh | exact (IH Hrest) ]
      | exact (IH Hrest) ].
Qed.

(* What the cases gathered for a key are, by membership. *)
Lemma gather_known_spec (inputs : list input) (key : K)
    (vals : list (Index.t * value)) :
  NoDup (map fst inputs) ->
  Keyed.lookup eqb key (gather_known eqb of_other inputs) = Some vals ->
  NoDup (map fst vals)
  ∧ (∀ (index : Index.t) (v : value),
       In (index, v) vals ->
       ∃ i : input,
         In i inputs ∧ fst i = index
         ∧ (Keyed.lookup eqb key (fst (snd i)) = Some v
            ∨ (Keyed.lookup eqb key (fst (snd i)) = None
               ∧ ∃ o : other,
                   snd (snd i) = Or_bottom.Ok o ∧ v = of_other o)))
  ∧ (∀ i : input,
       In i inputs ->
       (∀ v : value,
          Keyed.lookup eqb key (fst (snd i)) = Some v -> In (fst i, v) vals)
       ∧ (Keyed.lookup eqb key (fst (snd i)) = None ->
          ∀ o : other,
            snd (snd i) = Or_bottom.Ok o -> In (fst i, of_other o) vals))
  ∧ vals <> [].
Proof.
  intros Hdistinct. rewrite gather_known_lookup.
  destruct (bound_in_some key inputs) eqn:Hbound; [ | discriminate ].
  intros [= <-].
  split; [ rewrite map_rev; apply NoDup_rev, contributions_distinct;
           exact Hdistinct | ].
  assert (Hto :
    ∀ i : input,
      In i inputs ->
      (∀ v : value,
         Keyed.lookup eqb key (fst (snd i)) = Some v ->
         In (fst i, v) (rev (flat_map (contribution key) inputs)))
      ∧ (Keyed.lookup eqb key (fst (snd i)) = None ->
         ∀ o : other,
           snd (snd i) = Or_bottom.Ok o ->
           In (fst i, of_other o) (rev (flat_map (contribution key) inputs)))).
  { intros i Hin. split.
    - intros v Hv. rewrite <- in_rev. apply in_flat_map. exists i.
      split; [ exact Hin | ]. unfold contribution. rewrite Hv. left.
      reflexivity.
    - intros Hnone o Ho. rewrite <- in_rev. apply in_flat_map. exists i.
      split; [ exact Hin | ]. unfold contribution. rewrite Hnone, Ho. left.
      reflexivity. }
  split; [ | split; [ exact Hto | ] ].
  - intros index v Hin. apply in_rev in Hin.
    apply in_flat_map in Hin as (i & Hin & Hv). exists i.
    split; [ exact Hin | ].
    split; [ symmetry; exact (contribution_fst key i index v Hv) | ].
    unfold contribution in Hv.
    destruct (Keyed.lookup eqb key (fst (snd i))) as [v' | ].
    + destruct Hv as [[= _ <-] | []]. left. reflexivity.
    + right. split; [ reflexivity | ].
      destruct (snd (snd i)) as [o | ]; [ | destruct Hv ].
      destruct Hv as [[= _ <-] | []]. exists o. split; reflexivity.
  - unfold bound_in_some in Hbound.
    apply existsb_exists in Hbound as (i & Hin & Hi).
    apply (keyed_is_bound_lookup eqb key) in Hi as [v Hv].
    intros Hnil. pose proof (proj1 (Hto i Hin) v Hv) as Hin'.
    rewrite Hnil in Hin'. destruct Hin'.
Qed.

(* A key that the gathering does not bind has no case in any row-like
   structure. *)
Lemma gather_known_none (inputs : list input) (key : K) :
  Keyed.lookup eqb key (gather_known eqb of_other inputs) = None ->
  ∀ i : input, In i inputs -> Keyed.lookup eqb key (fst (snd i)) = None.
Proof.
  rewrite gather_known_lookup.
  destruct (bound_in_some key inputs) eqn:Hbound; [ discriminate | ].
  intros _ i Hin. unfold bound_in_some in Hbound.
  destruct (Keyed.lookup eqb key (fst (snd i))) as [v | ] eqn:Hv;
    [ | reflexivity ].
  assert (Htrue :
    existsb (fun i => Keyed.is_bound eqb key (fst (snd i))) inputs = true).
  { apply existsb_exists. exists i. split; [ exact Hin | ].
    unfold Keyed.is_bound. rewrite Hv. reflexivity. }
  congruence.
Qed.

End Gather_known.

(* ======================================================================== *)
(* Lists made of lists with indices                                         *)
(* ======================================================================== *)

(* A list made of at most one thing for each element of a list whose
   indices are distinct has distinct indices. *)
Lemma flat_map_indexed_distinct {A B : Type}
    (f : Index.t * A -> list (Index.t * B)) (l : list (Index.t * A)) :
  (∀ (i : Index.t * A) (index : Index.t) (b : B),
     In (index, b) (f i) -> index = fst i) ->
  (∀ i : Index.t * A, NoDup (map fst (f i))) ->
  NoDup (map fst l) -> NoDup (map fst (flat_map f l)).
Proof.
  intros Hfst Hone. induction l as [ | i l IH]; simpl; intros Hdistinct;
    [ apply NoDup_nil | ].
  inversion Hdistinct as [ | ? ? Hi Hrest]. subst.
  rewrite map_app. apply NoDup_app; [ apply Hone | exact (IH Hrest) | ].
  intros index Hin Hin'. apply Hi.
  apply in_map_iff in Hin as ([index1 b1] & Heq1 & Hin1). simpl in Heq1.
  subst index1. apply Hfst in Hin1.
  apply in_map_iff in Hin' as ([index2 b2] & Heq2 & Hin2). simpl in Heq2.
  subst index2. apply in_flat_map in Hin2 as (i' & Hi' & Hin2).
  apply Hfst in Hin2. rewrite <- Hin1, Hin2. apply in_map. exact Hi'.
Qed.

Lemma filter_indexed_distinct {A : Type} (keep : Index.t * A -> bool)
    (l : list (Index.t * A)) :
  NoDup (map fst l) -> NoDup (map fst (filter keep l)).
Proof.
  induction l as [ | i l IH]; simpl; intros Hdistinct; [ apply NoDup_nil | ].
  inversion Hdistinct as [ | ? ? Hi Hrest]. subst.
  destruct (keep i); [ | exact (IH Hrest) ].
  simpl. apply NoDup_cons; [ | exact (IH Hrest) ].
  intros Hin. apply Hi. apply in_map_iff in Hin as (i' & Heq & Hin).
  apply filter_In in Hin as [Hin _]. rewrite <- Heq. apply in_map. exact Hin.
Qed.

(* The things of a list that are not bottom. *)
Definition ok_of {A : Type} (x : Index.t * Or_bottom.t A)
    : list (Index.t * A) :=
  match snd x with
  | Or_bottom.Ok a => [(fst x, a)]
  | Or_bottom.Bottom => []
  end.

Lemma non_bottom_eq {A : Type} (l : list (Index.t * Or_bottom.t A)) :
  ∀ acc : list (Index.t * A), non_bottom acc l = rev (flat_map ok_of l) ++ acc.
Proof.
  induction l as [ | [id [a | ]] l IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH. unfold ok_of at 2. simpl. rewrite <- app_assoc. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma non_bottom_spec {A : Type} (l : list (Index.t * Or_bottom.t A)) :
  NoDup (map fst l) ->
  NoDup (map fst (non_bottom [] l))
  ∧ ∀ (index : Index.t) (a : A),
      In (index, a) (non_bottom [] l) <-> In (index, Or_bottom.Ok a) l.
Proof.
  intros Hdistinct. rewrite non_bottom_eq, app_nil_r.
  split.
  - rewrite map_rev. apply NoDup_rev.
    apply flat_map_indexed_distinct; [ | | exact Hdistinct ].
    + intros [id [a | ]] index b; unfold ok_of; simpl;
        [ intros [[= <- _] | []]; reflexivity | intros [] ].
    + intros [id [a | ]]; unfold ok_of; simpl;
        [ apply NoDup_cons; [ intros [] | apply NoDup_nil ] | apply NoDup_nil ].
  - intros index a. rewrite <- in_rev, in_flat_map. split.
    + intros ([id [a' | ]] & Hin & Hok); unfold ok_of in Hok; simpl in Hok;
        [ | destruct Hok ].
      destruct Hok as [[= <- <-] | []]. exact Hin.
    + intros Hin. exists (index, Or_bottom.Ok a).
      split; [ exact Hin | left; reflexivity ].
Qed.

(* ======================================================================== *)
(* The index of the join of cases                                           *)
(* ======================================================================== *)

Section Index.

(* What the index of a case admits is [W]: its domain admits it exactly
   or from below, and its shape admits it. *)
Context {lattice shape W : Type} (equal_index : lattice -> lattice -> bool)
  (inter_index : lattice -> lattice -> lattice)
  (n_way_join_shape : list shape -> or_unknown_or_bottom shape)
  (exact at_least : W -> lattice -> Prop) (shape_holds : W -> shape -> Prop).

Definition domain_holds (w : W) (domain : Row_like_index_domain.t lattice)
    : Prop :=
  match domain with
  | Row_like_index_domain.Known l => exact w l
  | Row_like_index_domain.At_least l => at_least w l
  end.

Hypothesis Hexact : ∀ (w : W) (l : lattice), exact w l -> at_least w l.
Hypothesis Hequal :
  ∀ (w : W) (l l' : lattice),
    equal_index l l' = true -> exact w l' -> exact w l.
Hypothesis Hinter_left :
  ∀ (w : W) (l l' : lattice), at_least w l -> at_least w (inter_index l l').
Hypothesis Hinter_right :
  ∀ (w : W) (l l' : lattice), at_least w l' -> at_least w (inter_index l l').
Hypothesis Hshapes :
  ∀ (shapes : list shape) (joined : shape),
    n_way_join_shape shapes = Ok joined ->
    ∀ shape' : shape,
      In shape' shapes ->
      ∀ w : W, shape_holds w shape' -> shape_holds w joined.
Hypothesis Hshapes_bottom :
  ∀ shapes : list shape, n_way_join_shape shapes = Bottom -> shapes = [].

Local Abbreviation inter_step :=
  (fun (i1' : lattice) (i2 : row_like_index lattice shape) =>
     match index_domain i2 with
     | Row_like_index_domain.At_least i2'
     | Row_like_index_domain.Known i2' => inter_index i1' i2'
     end).

Lemma fold_inter_holds (indexes : list (row_like_index lattice shape)) :
  ∀ (l : lattice) (w : W),
    at_least w l -> at_least w (List.fold_left inter_step indexes l).
Proof.
  induction indexes as [ | i indexes IH]; intros l w Hl; simpl;
    [ exact Hl | ].
  apply IH. destruct (index_domain i); apply Hinter_left; exact Hl.
Qed.

Lemma fold_inter_in (indexes : list (row_like_index lattice shape)) :
  ∀ (l : lattice) (w : W) (i : row_like_index lattice shape),
    In i indexes ->
    domain_holds w (index_domain i) ->
    at_least w (List.fold_left inter_step indexes l).
Proof.
  induction indexes as [ | i' indexes IH]; intros l w i Hin Hi; simpl;
    [ destruct Hin | ].
  destruct Hin as [-> | Hin]; [ | exact (IH _ w i Hin Hi) ].
  apply fold_inter_holds. unfold domain_holds in Hi.
  destruct (index_domain i);
    [ apply Hinter_right, Hexact; exact Hi | apply Hinter_right; exact Hi ].
Qed.

(* What the index of each case admits, the index of the join admits. *)
Lemma n_way_join_index_sound (indexes : list (row_like_index lattice shape))
    (index : row_like_index lattice shape) :
  n_way_join_index equal_index inter_index n_way_join_shape indexes
  = Ok index ->
  ∀ i : row_like_index lattice shape,
    In i indexes ->
    ∀ w : W,
      domain_holds w (index_domain i) ->
      shape_holds w (index_shape i) ->
      domain_holds w (index_domain index) ∧ shape_holds w (index_shape index).
Proof.
  unfold n_way_join_index. intros Hjoined i Hin w Hdomain Hshape.
  destruct (n_way_join_shape (map index_shape indexes)) as [ | joined | ]
    eqn:Hjoined_shape; try discriminate.
  assert (Hshape' : shape_holds w joined).
  { apply (Hshapes _ joined Hjoined_shape (index_shape i)); [ | exact Hshape ].
    apply in_map. exact Hin. }
  destruct indexes as [ | i1 rest]; [ discriminate | ].
  assert (Hat_least :
    ∀ i1' : lattice,
      (i = i1 -> at_least w i1') ->
      at_least w (List.fold_left inter_step rest i1')).
  { intros i1' Hfirst. destruct Hin as [<- | Hin].
    - apply fold_inter_holds, Hfirst. reflexivity.
    - exact (fold_inter_in rest i1' w i Hin Hdomain). }
  destruct (index_domain i1) as [i1' | i1'] eqn:Hdomain1.
  - destruct
      (forallb
         (fun i2 =>
            match index_domain i2 with
            | Row_like_index_domain.Known i2' => equal_index i1' i2'
            | Row_like_index_domain.At_least _ => false
            end)
         rest) eqn:Hall.
    + injection Hjoined as <-. simpl. split; [ | exact Hshape' ].
      destruct Hin as [<- | Hin].
      * rewrite Hdomain1 in Hdomain. exact Hdomain.
      * rewrite forallb_forall in Hall. specialize (Hall i Hin).
        unfold domain_holds in Hdomain.
        destruct (index_domain i) as [i2' | i2']; [ | discriminate ].
        exact (Hequal w i1' i2' Hall Hdomain).
    + injection Hjoined as <-. simpl. split; [ | exact Hshape' ].
      apply Hat_least. intros ->. rewrite Hdomain1 in Hdomain.
      apply Hexact. exact Hdomain.
  - injection Hjoined as <-. simpl. split; [ | exact Hshape' ].
    apply Hat_least. intros ->. rewrite Hdomain1 in Hdomain. exact Hdomain.
Qed.

(* The join of the indices of some cases is not bottom. *)
Lemma n_way_join_index_bottom (indexes : list (row_like_index lattice shape)) :
  n_way_join_index equal_index inter_index n_way_join_shape indexes = Bottom ->
  indexes = [].
Proof.
  unfold n_way_join_index. intros Hjoined.
  destruct (n_way_join_shape (map index_shape indexes)) as [ | joined | ]
    eqn:Hjoined_shape; try discriminate.
  - destruct indexes as [ | i1 rest]; [ reflexivity | ].
    destruct (index_domain i1); [ | discriminate ].
    destruct (forallb _ rest); discriminate.
  - apply Hshapes_bottom in Hjoined_shape.
    exact (map_eq_nil _ _ Hjoined_shape).
Qed.

End Index.

(* ======================================================================== *)
(* Fields                                                                   *)
(* ======================================================================== *)

Lemma free_variables_unknown (k : flambda_kind) :
  free_variables (unknown k) = [].
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma aliases_with_kinds_unknown (k : flambda_kind) :
  aliases_with_kinds (unknown k) = [].
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma free_variables_bottom (k : flambda_kind) :
  free_variables (bottom k) = [].
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma aliases_with_kinds_bottom (k : flambda_kind) :
  aliases_with_kinds (bottom k) = [].
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma free_variables_alias (k : flambda_kind) (s : simple) :
  free_variables (alias_type_of k s) = free_variables_of_simple s.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma aliases_with_kinds_alias (k : flambda_kind) (s : simple) :
  aliases_with_kinds (alias_type_of k s) = [(s, k)].
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma kind_unknown (k : flambda_kind) : kind (unknown k) = k.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma kind_bottom (k : flambda_kind) : kind (bottom k) = k.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

Lemma kind_alias (k : flambda_kind) (s : simple) : kind (alias_type_of k s) = k.
Proof. destruct k as [ | [] | | ]; reflexivity. Qed.

(* The field of a block of a shape, at an index, is of the kind that
   the shape gives the index. *)
Lemma block_shape_element_kind_of_field (shape : block_shape) (tag : Z)
    (fields : list value) (index : nat) (field : value) (kind : flambda_kind) :
  block_has_shape shape tag fields ->
  nth_error fields index = Some field ->
  block_shape_element_kind shape index = Some kind ->
  kind_of_value field = kind.
Proof.
  intros [_ Hkinds] Hfield Hkind.
  apply (map_nth_error kind_of_value) in Hfield. rewrite Hkinds in Hfield.
  destruct shape as [[ | prefix suffix] | ]; simpl in Hkind, Hfield.
  - injection Hkind as <-. apply nth_error_In, repeat_spec in Hfield.
    exact Hfield.
  - destruct (Nat.ltb index prefix) eqn:Hlt.
    + injection Hkind as <-. apply Nat.ltb_lt in Hlt.
      rewrite nth_error_app1 in Hfield by (rewrite repeat_length; exact Hlt).
      apply nth_error_In, repeat_spec in Hfield. exact Hfield.
    + apply Nat.ltb_ge in Hlt.
      rewrite nth_error_app2 in Hfield by (rewrite repeat_length; exact Hlt).
      rewrite repeat_length, nth_error_map in Hfield. congruence.
  - injection Hkind as <-. apply nth_error_In, repeat_spec in Hfield.
    exact Hfield.
Qed.

(* The least of the lengths of arrays of fields. *)
Lemma least_length_le (others : list (Index.t * list flambda_type)) :
  ∀ init : nat,
    List.fold_left
      (fun least_length other_fields =>
         Nat.min least_length (length (snd other_fields)))
      others init
    <= init
    ∧ ∀ (index : Index.t) (fields : list flambda_type),
        In (index, fields) others ->
        List.fold_left
          (fun least_length other_fields =>
             Nat.min least_length (length (snd other_fields)))
          others init
        <= length fields.
Proof.
  induction others as [ | [id fields'] others IH]; intros init; simpl.
  - split; [ lia | intros ? ? [] ].
  - destruct (IH (Nat.min init (length fields'))) as (Hinit & Hothers).
    split; [ lia | ].
    intros index fields [[= <- <-] | Hin]; [ lia | exact (Hothers _ _ Hin) ].
Qed.

(* ======================================================================== *)
(* What [deduce_is_int] and [deduce_get_tag] answer                         *)
(* ======================================================================== *)

Lemma block_not_immediate (statics : static_env) (i tag : Z)
    (fields : list value) :
  block_of statics (Value_const (Tagged_immediate i)) <> Some (tag, fields).
Proof. discriminate. Qed.

Theorem deduce_is_int_simple_is_sound : deduce_is_int_simple_sound.
Proof.
  intros statics vars v is_int immediates get_tag blocks extensions is_unique
    simple Hsatisfied Hsimple.
  rewrite variant_satisfied in Hsatisfied.
  unfold deduce_is_int_simple, deduce_is_int in Hsimple.
  destruct Hsatisfied
    as [(i & -> & His_int & Himmediates & _)
       | (tag & fields & Hblock & His_int & _ & Hblocks & _)].
  - (* An immediate. *)
    left. split; [ exists i; reflexivity | ].
    destruct blocks as [blocks | ].
    + destruct (row_like_for_blocks_is_bottom blocks).
      * injection Hsimple as <-. reflexivity.
      * destruct immediates as [immediates | ].
        -- destruct (is_obviously_bottom immediates) eqn:Hbottom.
           ++ exfalso.
              exact (is_obviously_bottom_satisfied _ _ _ _ Hbottom Himmediates).
           ++ destruct is_int as [is_int | ]; [ | discriminate ].
              injection Hsimple as <-. exact His_int.
        -- destruct is_int as [is_int | ]; [ | discriminate ].
           injection Hsimple as <-. exact His_int.
    + destruct immediates as [immediates | ].
      * destruct (is_obviously_bottom immediates) eqn:Hbottom.
        -- exfalso.
           exact (is_obviously_bottom_satisfied _ _ _ _ Hbottom Himmediates).
        -- destruct is_int as [is_int | ]; [ | discriminate ].
           injection Hsimple as <-. exact His_int.
      * destruct is_int as [is_int | ]; [ | discriminate ].
        injection Hsimple as <-. exact His_int.
  - (* A block. *)
    right. split; [ exists tag, fields; exact Hblock | ].
    destruct blocks as [blocks | ].
    + destruct (row_like_for_blocks_is_bottom blocks) eqn:Hbottom.
      * exfalso.
        exact (row_like_for_blocks_is_bottom_satisfied _ _ _ _ _ Hbottom
                 Hblocks).
      * destruct immediates as [immediates | ].
        -- destruct (is_obviously_bottom immediates).
           ++ injection Hsimple as <-. reflexivity.
           ++ destruct is_int as [is_int | ]; [ | discriminate ].
              injection Hsimple as <-. exact His_int.
        -- destruct is_int as [is_int | ]; [ | discriminate ].
           injection Hsimple as <-. exact His_int.
    + destruct immediates as [immediates | ].
      * destruct (is_obviously_bottom immediates).
        -- injection Hsimple as <-. reflexivity.
        -- destruct is_int as [is_int | ]; [ | discriminate ].
           injection Hsimple as <-. exact His_int.
      * destruct is_int as [is_int | ]; [ | discriminate ].
        injection Hsimple as <-. exact His_int.
Qed.

(* The tag of a block that a row-like structure with no other case
   admits is one of its known tags. *)
Lemma row_like_tag_among (statics : static_env) (vars : env) (tag : Z)
    (fields : list value)
    (known_tags : Keyed.finite_map Z (Or_unknown.t row_like_block_case))
    (alloc_mode : Alloc_mode.t) :
  row_like_for_blocks_satisfied statics vars tag fields
    (Row_like_for_blocks known_tags Or_bottom.Bottom alloc_mode) ->
  Keyed.among Z.eqb tag (Keyed.domain Z.eqb known_tags) = true.
Proof.
  rewrite row_like_for_blocks_find_iff,
    (keyed_among_domain Z Z.eqb Z.eqb_eq).
  unfold Keyed.is_bound.
  destruct (Keyed.lookup Z.eqb tag known_tags); [ reflexivity | intros [] ].
Qed.

Theorem deduce_get_tag_simple_is_sound : deduce_get_tag_simple_sound.
Proof.
  intros statics vars v is_int immediates get_tag blocks extensions is_unique
    tag fields Hsatisfied Hblock.
  rewrite variant_satisfied in Hsatisfied.
  destruct Hsatisfied
    as [(i & -> & _) | (tag' & fields' & Hblock' & _ & Hget_tag & Hblocks & _)];
    [ exfalso; exact (block_not_immediate _ _ _ _ Hblock) | ].
  rewrite Hblock in Hblock'. injection Hblock' as <- <-.
  assert (Hvar :
    match
      match get_tag with
      | Some var => Ok (Var var)
      | None => @Unknown simple
      end
    with
    | Bottom => False
    | Ok simple =>
      eval_simple vars simple = Some (Value_const (Naked_immediate tag))
    | Unknown => True
    end).
  { destruct get_tag as [var | ]; [ exact Hget_tag | exact I ]. }
  unfold deduce_get_tag_simple, deduce_get_tag.
  destruct blocks as [[known_tags [other | ] alloc_mode] | ];
    [ exact Hvar | | exact Hvar ].
  unfold row_like_for_blocks_all_tags. cbv beta iota.
  pose proof (row_like_tag_among _ _ _ _ _ _ Hblocks) as Hamong.
  unfold row_like_block_case in *.
  destruct (Keyed.is_empty (Keyed.domain Z.eqb known_tags)) eqn:Hempty.
  - apply (keyed_is_empty_among Z Z.eqb Z.eqb_eq) with (key := tag) in Hempty.
    exact (eq_true_false_abs _ Hamong Hempty).
  - destruct (Keyed.get_singleton Z.eqb (Keyed.domain Z.eqb known_tags))
      as [tag' | ] eqn:Hsingleton; [ | exact Hvar ].
    pose proof
      (proj1 (keyed_get_singleton Z Z.eqb Z.eqb_eq tag' _) Hsingleton tag)
      as Heq.
    rewrite Heq in Hamong. apply Z.eqb_eq in Hamong. subst tag'.
    reflexivity.
Qed.

(* ======================================================================== *)
(* The interface: what a growing state keeps                                *)
(* ======================================================================== *)

Section Traversal.

Context (typing_env_well_formed : Typing_env.t -> Prop).

Context {state : Type}
  (joined_env : state -> Index.t -> option Typing_env.t)
  (definitions_of_existentials :
     state -> finite_map (Simples_in_joined_envs.t * flambda_kind))
  (kind_in_target_env : state -> variable -> option flambda_kind)
  (state_valid : state -> Prop)
  (state_kinded : state -> Prop).

Local Abbreviation envs_well_formed :=
  (joined_envs_well_formed typing_env_well_formed joined_env).
Local Abbreviation envs_kinded := (joined_envs_kinded joined_env).
Local Abbreviation grows :=
  (state_grows joined_env definitions_of_existentials kind_in_target_env).
Local Abbreviation extends :=
  (extends_input joined_env definitions_of_existentials).
Local Abbreviation args_in_scope := (join_args_in_scope joined_env).
Local Abbreviation exists_in_target :=
  (exists_in_target_env kind_in_target_env).
Local Abbreviation in_target := (answer_in_target kind_in_target_env).
Local Abbreviation kinded_in_target :=
  (answer_kinded_in_target kind_in_target_env).
Local Abbreviation of_kind_in_target :=
  (simple_of_kind_in_target kind_in_target_env).
Local Abbreviation step_sound :=
  (join_step_sound typing_env_well_formed joined_env
     definitions_of_existentials kind_in_target_env state_valid state_kinded).

Lemma grows_refl (s : state) : grows s s.
Proof. repeat split; auto. Qed.

Lemma grows_trans (s s' s'' : state) :
  grows s s' -> grows s' s'' -> grows s s''.
Proof.
  intros (Henv & Hdefs & Hkinds) (Henv' & Hdefs' & Hkinds').
  repeat split.
  - intros index. rewrite Henv'. apply Henv.
  - intros x definition Hx. apply Hdefs', Hdefs, Hx.
  - intros x kind Hx. apply Hkinds', Hkinds, Hx.
Qed.

Lemma grows_joined_env (s s' : state) (index : Index.t) :
  grows s s' -> joined_env s' index = joined_env s index.
Proof. intros (Henv & _). apply Henv. Qed.

Lemma grows_well_formed (s s' : state) :
  grows s s' -> envs_well_formed s -> envs_well_formed s'.
Proof.
  intros (Henv & _) Hwf index use Huse. rewrite Henv in Huse.
  exact (Hwf index use Huse).
Qed.

Lemma grows_kinded (s s' : state) :
  grows s s' -> envs_kinded s -> envs_kinded s'.
Proof.
  intros (Henv & _) Hkinded index use Huse. rewrite Henv in Huse.
  exact (Hkinded index use Huse).
Qed.

Lemma grows_args_in_scope {X : Type} (P : Typing_env.t -> X -> Prop)
    (s s' : state) (args : list (Index.t * X)) :
  grows s s' -> args_in_scope P s args -> args_in_scope P s' args.
Proof.
  intros (Henv & _) Hargs index x Hin.
  destruct (Hargs index x Hin) as (use & Huse & HP).
  exists use. rewrite Henv. split; assumption.
Qed.

(* A valuation that extends an input at a later state extends it at an
   earlier one. *)
Lemma grows_extends (s s' : state) (index : Index.t)
    (valuation valuation' : env) :
  grows s s' ->
  extends s' index valuation valuation' ->
  extends s index valuation valuation'.
Proof.
  intros (Henv & Hdefs & _) (use & Huse & Hagrees & Hholds).
  exists use. rewrite <- Henv. split; [ exact Huse | ].
  split; [ exact Hagrees | ].
  intros x simples kind simple v Hx.
  apply (Hholds x simples kind simple v). apply Hdefs. exact Hx.
Qed.

Lemma grows_exists (s s' : state) (x : variable) :
  grows s s' -> exists_in_target s x = true -> exists_in_target s' x = true.
Proof.
  intros (_ & _ & Hkinds). unfold exists_in_target_env.
  destruct (kind_in_target_env s x) as [kind | ] eqn:Hkind; [ | discriminate ].
  rewrite (Hkinds x kind Hkind). reflexivity.
Qed.

Lemma grows_in_target {Y : Type} (variables_of : Y -> list variable)
    (s s' : state) (y : Y) :
  grows s s' -> in_target variables_of s y -> in_target variables_of s' y.
Proof.
  intros Hgrows Htarget x Hx. exact (grows_exists _ _ _ Hgrows (Htarget x Hx)).
Qed.

Lemma grows_of_kind_in_target (s s' : state) (simple : simple)
    (kind : flambda_kind) :
  grows s s' ->
  of_kind_in_target s simple kind -> of_kind_in_target s' simple kind.
Proof.
  intros (_ & _ & Hkinds). destruct simple as [x | sym | c]; simpl; auto.
Qed.

Lemma grows_kinded_in_target {Y : Type}
    (aliases_of : Y -> list (simple * flambda_kind)) (s s' : state) (y : Y) :
  grows s s' ->
  kinded_in_target aliases_of s y -> kinded_in_target aliases_of s' y.
Proof.
  intros Hgrows Hkinded simple kind Hin.
  exact (grows_of_kind_in_target _ _ _ _ Hgrows (Hkinded simple kind Hin)).
Qed.

(* ======================================================================== *)
(* Using a function that is sound in the middle of a run                    *)
(* ======================================================================== *)

Local Abbreviation arg_ok := arg_in_scope_and_kinded.

(* What a call that went from [s1] to [s2] gives at any later state:
   its answer is in the target, bounds each thing given, and is kinded
   if the state was. *)
Definition answer_holds_from {X Y : Type}
    (variables_of_answer : Y -> list variable)
    (aliases_of_answer : Y -> list (simple * flambda_kind))
    (bound : static_env -> env -> X -> env -> Y -> Prop) (s1 s2 : state)
    (args : list (Index.t * X)) (answer : Y) : Prop :=
  ∀ s' : state,
    grows s2 s' ->
    in_target variables_of_answer s' answer
    ∧ (∀ (index : Index.t) (x : X) (use : Typing_env.t)
         (statics : static_env) (valuation valuation' : env),
         In (index, x) args ->
         joined_env s' index = Some use ->
         typing_env_satisfied_strictly statics valuation use ->
         extends s' index valuation valuation' ->
         bound statics valuation x valuation' answer)
    ∧ (state_kinded s1 -> kinded_in_target aliases_of_answer s' answer).

(* A sound function called at a state [s1] that has grown from a state
   [s] at which its arguments were in scope. *)
Lemma step_sound_at {X Y : Type} (variables_of_arg : X -> list variable)
    (aliases_of_arg : X -> list (simple * flambda_kind))
    (variables_of_answer : Y -> list variable)
    (aliases_of_answer : Y -> list (simple * flambda_kind))
    (bound : static_env -> env -> X -> env -> Y -> Prop)
    (step : state -> list (Index.t * X) -> option (Y * state)) :
  step_sound variables_of_arg aliases_of_arg variables_of_answer
    aliases_of_answer bound step ->
  ∀ (s s1 s2 : state) (args : list (Index.t * X)) (answer : Y),
    envs_well_formed s -> envs_kinded s -> grows s s1 -> state_valid s1 ->
    join_args_distinct args ->
    args_in_scope (arg_ok variables_of_arg aliases_of_arg) s args ->
    step s1 args = Some (answer, s2) ->
    state_valid s2 ∧ grows s1 s2 ∧ (state_kinded s1 -> state_kinded s2)
    ∧ answer_holds_from variables_of_answer aliases_of_answer bound s1 s2 args
        answer.
Proof.
  intros Hsound s s1 s2 args answer Hwf Hkinded Hgrows Hvalid Hdistinct Hargs
    Hstep.
  destruct
    (Hsound s1 s2 args answer Hvalid (grows_well_formed _ _ Hgrows Hwf)
       (grows_kinded _ _ Hgrows Hkinded) Hdistinct
       (grows_args_in_scope _ _ _ _ Hgrows Hargs) Hstep)
    as (Hvalid2 & Hgrows2 & Htarget & Hbound & Hkinds).
  split; [ exact Hvalid2 | ]. split; [ exact Hgrows2 | ].
  split; [ intros Hk; apply Hkinds; exact Hk | ].
  intros s' Hgrows'.
  split; [ exact (grows_in_target _ _ _ _ Hgrows' Htarget) | ].
  split.
  - intros index x use statics valuation valuation' Hin Huse Hsatisfied
      Hextends.
    apply (Hbound index x use statics valuation valuation' Hin);
      [ | exact Hsatisfied | exact (grows_extends _ _ _ _ _ Hgrows' Hextends) ].
    rewrite <- (grows_joined_env _ _ index Hgrows'). exact Huse.
  - intros Hk.
    exact (grows_kinded_in_target _ _ _ _ Hgrows' (proj2 (Hkinds Hk))).
Qed.

(* Arguments made of parts of arguments that are in scope and kinded
   are in scope and kinded. *)
Lemma args_of_parts {X X' : Type} (variables_of : X -> list variable)
    (aliases_of : X -> list (simple * flambda_kind))
    (variables_of' : X' -> list variable)
    (aliases_of' : X' -> list (simple * flambda_kind)) (s : state)
    (args : list (Index.t * X)) (args' : list (Index.t * X')) :
  args_in_scope (arg_ok variables_of aliases_of) s args ->
  (∀ (index : Index.t) (x' : X'),
     In (index, x') args' ->
     ∃ x : X,
       In (index, x) args
       ∧ incl (variables_of' x') (variables_of x)
       ∧ incl (aliases_of' x') (aliases_of x)) ->
  args_in_scope (arg_ok variables_of' aliases_of') s args'.
Proof.
  intros Hargs Hparts index x' Hin.
  destruct (Hparts index x' Hin) as (x & Hin' & Hvariables & Haliases).
  destruct (Hargs index x Hin') as (use & Huse & Hknown & Hkinds).
  exists use. split; [ exact Huse | ].
  split.
  - intros y Hy. apply Hknown, Hvariables, Hy.
  - intros simple kind Hsimple. apply Hkinds, Haliases, Hsimple.
Qed.

(* A sound function is sound for a weaker bound. *)
Lemma step_sound_bound {X Y : Type} (variables_of_arg : X -> list variable)
    (aliases_of_arg : X -> list (simple * flambda_kind))
    (variables_of_answer : Y -> list variable)
    (aliases_of_answer : Y -> list (simple * flambda_kind))
    (bound bound' : static_env -> env -> X -> env -> Y -> Prop)
    (step : state -> list (Index.t * X) -> option (Y * state)) :
  (∀ (statics : static_env) (valuation : env) (x : X) (valuation' : env)
     (y : Y),
     bound statics valuation x valuation' y ->
     bound' statics valuation x valuation' y) ->
  step_sound variables_of_arg aliases_of_arg variables_of_answer
    aliases_of_answer bound step ->
  step_sound variables_of_arg aliases_of_arg variables_of_answer
    aliases_of_answer bound' step.
Proof.
  intros Himpl Hsound s s' args answer Hvalid Hwf Hkinded Hdistinct Hargs
    Hstep.
  destruct (Hsound s s' args answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep)
    as (Hvalid' & Hgrows & Htarget & Hbound & Hkinds).
  split; [ exact Hvalid' | ]. split; [ exact Hgrows | ].
  split; [ exact Htarget | ]. split; [ | exact Hkinds ].
  intros index x use statics valuation valuation' Hin Huse Hsatisfied
    Hextends.
  apply Himpl.
  exact
    (Hbound index x use statics valuation valuation' Hin Huse Hsatisfied
       Hextends).
Qed.

(* An answer that holds from a state holds from a later one. *)
Lemma answer_holds_from_later {X Y : Type}
    (variables_of_answer : Y -> list variable)
    (aliases_of_answer : Y -> list (simple * flambda_kind))
    (bound : static_env -> env -> X -> env -> Y -> Prop)
    (s0 s1 s2 s3 : state) (args : list (Index.t * X)) (answer : Y) :
  (state_kinded s0 -> state_kinded s1) ->
  grows s2 s3 ->
  answer_holds_from variables_of_answer aliases_of_answer bound s1 s2 args
    answer ->
  answer_holds_from variables_of_answer aliases_of_answer bound s0 s3 args
    answer.
Proof.
  intros Hk Hgrows Hholds s' Hgrows'.
  destruct (Hholds s' (grows_trans _ _ _ Hgrows Hgrows'))
    as (Htarget & Hbound & Hkinds).
  split; [ exact Htarget | ]. split; [ exact Hbound | ].
  intros Hk0. exact (Hkinds (Hk Hk0)).
Qed.

(* A join that may answer bottom: it answers bottom only of no thing,
   and otherwise as a sound function does, called at a state [s1] that
   has grown from a state [s] at which the things given were in scope
   and kinded. *)
Definition case_join_sound {X Y : Type} (variables_of_arg : X -> list variable)
    (aliases_of_arg : X -> list (simple * flambda_kind))
    (variables_of_answer : Y -> list variable)
    (aliases_of_answer : Y -> list (simple * flambda_kind))
    (bound : static_env -> env -> X -> env -> Y -> Prop)
    (join : state -> list (Index.t * X) -> option (Or_bottom.t (Y * state)))
    : Prop :=
  ∀ (s s1 : state) (args : list (Index.t * X))
    (result : Or_bottom.t (Y * state)),
    envs_well_formed s -> envs_kinded s -> grows s s1 -> state_valid s1 ->
    join_args_distinct args ->
    args_in_scope (arg_ok variables_of_arg aliases_of_arg) s args ->
    join s1 args = Some result ->
    match result with
    | Or_bottom.Bottom => args = []
    | Or_bottom.Ok (answer, s2) =>
      state_valid s2 ∧ grows s1 s2 ∧ (state_kinded s1 -> state_kinded s2)
      ∧ answer_holds_from variables_of_answer aliases_of_answer bound s1 s2
          args answer
    end.

(* ======================================================================== *)
(* [generic_merge_map_known]                                                *)
(* ======================================================================== *)

Section Merge_map_known.

Context {K value other : Type} (eqb : K -> K -> bool)
  (Heqb : decides_equality eqb) (of_other : other -> value)
  (variables_of : value -> list variable)
  (aliases_of : value -> list (simple * flambda_kind))
  (bound : static_env -> env -> value -> env -> value -> Prop)
  (join :
     state -> list (Index.t * value) -> option (Or_bottom.t (value * state))).

Hypothesis Hjoin :
  case_join_sound variables_of aliases_of variables_of aliases_of bound join.

(* The cases of a row-like structure are in scope and kinded in an
   environment. *)
Definition known_in_scope (use : Typing_env.t)
    (m : Keyed.finite_map K value * Or_bottom.t other) : Prop :=
  (∀ (key : K) (v : value),
     Keyed.lookup eqb key (fst m) = Some v ->
     arg_ok variables_of aliases_of use v)
  ∧ ∀ o : other,
      snd m = Or_bottom.Ok o -> arg_ok variables_of aliases_of use (of_other o).

(* The map answered has no key twice; what it binds a key to is the
   join of the cases gathered for the key; and it binds every key for
   which cases were gathered. *)
Lemma generic_merge_map_known_is_sound (s s1 s2 : state)
    (maps : list (Index.t * (Keyed.finite_map K value * Or_bottom.t other)))
    (joined : Keyed.finite_map K value) :
  envs_well_formed s -> envs_kinded s -> grows s s1 -> state_valid s1 ->
  join_args_distinct maps ->
  args_in_scope known_in_scope s maps ->
  generic_merge_map_known eqb of_other join s1 maps = Some (joined, s2) ->
  state_valid s2 ∧ grows s1 s2 ∧ (state_kinded s1 -> state_kinded s2)
  ∧ (∀ (key : K) (y : value),
       In (key, y) joined -> Keyed.lookup eqb key joined = Some y)
  ∧ (∀ (key : K) (y : value),
       Keyed.lookup eqb key joined = Some y ->
       ∃ vals : list (Index.t * value),
         Keyed.lookup eqb key (gather_known eqb of_other maps) = Some vals
         ∧ answer_holds_from variables_of aliases_of bound s1 s2 vals y)
  ∧ ∀ key : K,
      Keyed.lookup eqb key joined = None ->
      Keyed.lookup eqb key (gather_known eqb of_other maps) = None.
Proof.
  intros Hwf Hkinded Hgrows Hvalid Hdistinct Hargs Hmerge.
  unfold generic_merge_map_known in Hmerge.
  destruct maps as [ | first rest].
  { injection Hmerge as <- <-. split; [ exact Hvalid | ].
    split; [ apply grows_refl | ]. split; [ auto | ].
    split; [ intros ? ? [] | ]. split; [ intros ? ? [=] | reflexivity ]. }
  cbv beta iota in Hmerge.
  set (P := fun s' : state => state_valid s' ∧ grows s s').
  set (R :=
    fun s' s'' : state =>
      grows s' s'' ∧ (state_kinded s' -> state_kinded s'')).
  assert (Hrefl : ∀ s' : state, R s' s').
  { intros s'. split; [ apply grows_refl | auto ]. }
  assert (Htrans : ∀ a b c : state, R a b -> R b c -> R a c).
  { intros a b c [Hab Hkab] [Hbc Hkbc].
    split; [ exact (grows_trans _ _ _ Hab Hbc) | auto ]. }
  assert (Hvals :
    ∀ (key : K) (vals : list (Index.t * value)),
      Keyed.lookup eqb key (gather_known eqb of_other (first :: rest))
      = Some vals ->
      join_args_distinct vals
      ∧ args_in_scope (arg_ok variables_of aliases_of) s vals
      ∧ vals <> []).
  { intros key vals Hkey.
    destruct
      (gather_known_spec eqb Heqb of_other (first :: rest) key vals Hdistinct
         Hkey)
      as (Hd & Hfrom & _ & Hne).
    split; [ exact Hd | ]. split; [ | exact Hne ].
    intros index v Hin. destruct (Hfrom index v Hin) as (i & Hi & Hfst & Hv).
    destruct i as [index' m]. simpl in Hfst. subst index'.
    destruct (Hargs index m Hi) as (use & Huse & Hknown & Hother).
    exists use. split; [ exact Huse | ].
    destruct Hv as [Hv | (_ & o & Ho & ->)];
      [ exact (Hknown key v Hv) | exact (Hother o Ho) ]. }
  eapply (filter_map_fold_spec eqb Heqb P R Hrefl Htrans) in Hmerge.
  - destruct Hmerge
      as ((Hvalid2 & Hgrows02) & (Hgrows2 & Hk2) & Hin & Hfound & Hall).
    split; [ exact Hvalid2 | ]. split; [ exact Hgrows2 | ].
    split; [ exact Hk2 | ]. split; [ exact Hin | ].
    split.
    + intros key y Hy.
      destruct (Hfound key y Hy)
        as (vals & s1' & s2' & Hvals' & (Hvalid1' & Hgrows1')
            & (Hgrows11 & Hk11) & Hg & (Hgrows22 & _)).
      exists vals. split; [ exact Hvals' | ].
      destruct (Hvals key vals Hvals') as (Hd & Hscope & _).
      destruct (join s1' vals) as [[[y' s2''] | ] | ] eqn:Hj;
        try discriminate.
      injection Hg as -> ->.
      pose proof
        (Hjoin s s1' vals _ Hwf Hkinded Hgrows1' Hvalid1' Hd Hscope Hj)
        as (_ & _ & _ & Hholds).
      exact
        (answer_holds_from_later _ _ _ s1 s1' s2' s2 vals y Hk11 Hgrows22
           Hholds).
    + intros key Hnone.
      destruct
        (Keyed.lookup eqb key (gather_known eqb of_other (first :: rest)))
        as [vals | ] eqn:Hvals'; [ | reflexivity ].
      exfalso.
      destruct (Hall key vals Hvals')
        as [[y Hy] | (s1' & s2' & (Hvalid1' & Hgrows1') & _ & Hg)];
        [ congruence | ].
      destruct (Hvals key vals Hvals') as (Hd & Hscope & Hne).
      destruct (join s1' vals) as [[[y' s2''] | ] | ] eqn:Hj;
        try discriminate.
      exact
        (Hne (Hjoin s s1' vals _ Hwf Hkinded Hgrows1' Hvalid1' Hd Hscope Hj)).
  - intros key vals s1' a s2' Hvals' (Hvalid1' & Hgrows1') Hg.
    destruct (Hvals key vals Hvals') as (Hd & Hscope & _).
    destruct (join s1' vals) as [[[y' s2''] | ] | ] eqn:Hj; try discriminate.
    + injection Hg as <- <-.
      pose proof
        (Hjoin s s1' vals _ Hwf Hkinded Hgrows1' Hvalid1' Hd Hscope Hj)
        as (Hvalid2' & Hgrows2' & Hk2' & _).
      split;
        [ split;
          [ exact Hvalid2' | exact (grows_trans _ _ _ Hgrows1' Hgrows2') ]
        | split; assumption ].
    + injection Hg as <- <-. split; [ split; assumption | apply Hrefl ].
  - split; [ exact Hvalid | exact Hgrows ].
Qed.

End Merge_map_known.

(* The contract of the join of types is that of a sound function. *)
Definition type_bound :=
  known_bound (all_kept type_satisfied type_satisfied).

Lemma type_sound_step
    (n_way_join :
       state -> list (Index.t * flambda_type)
       -> option (Or_unknown.t flambda_type * state)) :
  n_way_join_type_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    n_way_join ->
  step_sound free_variables aliases_with_kinds (of_known free_variables)
    (of_known aliases_with_kinds) type_bound n_way_join.
Proof.
  intros Hsound s s' ts answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  assert (Hscope : args_in_scope type_in_scope s ts).
  { intros index t Hin. destruct (Hargs index t Hin) as (use & Huse & H & _).
    exists use. split; [ exact Huse | exact H ]. }
  assert (Hkinds : args_in_scope type_kinded s ts).
  { intros index t Hin. destruct (Hargs index t Hin) as (use & Huse & _ & H).
    exists use. split; [ exact Huse | exact H ]. }
  destruct
    (Hsound s s' ts answer Hvalid Hwf Hkinded Hdistinct Hscope Hkinds Hstep)
    as (Hvalid' & Hgrows & Hknown & Hkinded').
  split; [ exact Hvalid' | ]. split; [ exact Hgrows | ].
  split; [ | split ].
  - destruct answer as [ty | ]; [ | intros x [] ].
    exact (proj1 (Hknown ty eq_refl)).
  - intros index t use statics valuation valuation' Hin Huse Hsatisfied
      Hextends.
    destruct answer as [ty | ]; [ | exact I ].
    intros v Hv.
    exact
      (proj2 (proj2 (Hknown ty eq_refl)) index t use statics valuation
         valuation' v Hin Huse Hsatisfied Hextends Hv).
  - intros Hk. destruct (Hkinded' Hk) as (Hk' & Hty).
    split; [ exact Hk' | ].
    destruct answer as [ty | ]; [ | intros simple kind [] ].
    exact (Hty ty eq_refl).
Qed.

(* ======================================================================== *)
(* [n_way_join_unknown]                                                     *)
(* ======================================================================== *)

Theorem n_way_join_unknown_is_sound :
  n_way_join_unknown_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded.
Proof.
  intros A B variables_of_arg aliases_of_arg variables_of_answer
    aliases_of_answer bound n_way_join_contents Hcontents s s' args answer
    Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_unknown in Hstep.
  destruct (known_contents [] args) as [contents | ] eqn:Hknown.
  - destruct (known_contents_spec args [] contents Hknown)
      as (Hfst & Hfrom & Hto & _).
    assert (Hdistinct' : join_args_distinct contents).
    { unfold join_args_distinct. rewrite Hfst, app_nil_r.
      apply NoDup_rev. exact Hdistinct. }
    assert (Hargs' :
      args_in_scope (arg_in_scope_and_kinded variables_of_arg aliases_of_arg)
        s contents).
    { intros index a Hin. destruct (Hfrom index a Hin) as [[] | Hin'].
      exact (Hargs index (Or_unknown.Known a) Hin'). }
    destruct
      (Hcontents s s' contents answer Hvalid Hwf Hkinded Hdistinct' Hargs'
         Hstep)
      as (Hvalid' & Hgrows & Htarget & Hbound & Hkinds).
    split; [ exact Hvalid' | ]. split; [ exact Hgrows | ].
    split; [ exact Htarget | ]. split; [ | exact Hkinds ].
    intros index x use statics valuation valuation' Hin Huse Hsatisfied
      Hextends.
    destruct (Hto index x Hin) as (a & -> & Hin').
    specialize
      (Hbound index a use statics valuation valuation' Hin' Huse Hsatisfied
         Hextends).
    destruct answer; exact Hbound.
  - injection Hstep as <- <-.
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ].
    split.
    + intros index x use statics valuation valuation' _ _ _ _.
      destruct x; exact I.
    + intros Hk. split; [ exact Hk | intros simple kind [] ].
Qed.

(* ======================================================================== *)
(* The functions that call the join of [Simple]s                            *)
(* ======================================================================== *)

Section Simples.

Context
  (n_way_join_simples :
     state -> flambda_kind -> list (Index.t * simple)
     -> option (Or_bottom.t simple * state)).

Hypothesis Hsimples :
  n_way_join_simples_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    n_way_join_simples.

Theorem n_way_join_relation_simples_is_sound :
  n_way_join_relation_simples_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    n_way_join_simples.
Proof.
  intros s s' simples x Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_relation_simples in Hstep.
  destruct (n_way_join_simples s (Naked_number Kind_naked_immediate) simples)
    as [[joined s1] | ] eqn:Hjoin; [ | discriminate ].
  assert (Hkinds :
    args_in_scope
      (fun use simple =>
         simple_of_kind use simple (Naked_number Kind_naked_immediate))
      s simples).
  { intros index simple Hin.
    destruct (Hargs index simple Hin) as (use & Huse & _ & Haliases).
    exists use. split; [ exact Huse | ]. apply Haliases. left. reflexivity. }
  destruct
    (Hsimples s s1 _ simples joined Hvalid Hwf Hkinded Hdistinct Hkinds Hjoin)
    as (Hvalid1 & Hgrows & _ & _ & Hok & Hkinded1).
  assert (Hnone :
    Some (None, s1) = Some (x, s') ->
    state_valid s' ∧ grows s s'
    ∧ in_target free_variables_of_option s' x
    ∧ (∀ (index : Index.t) (simple : FlambdaModel.simple)
         (use : Typing_env.t) (statics : static_env)
         (valuation valuation' : env),
         In (index, simple) simples ->
         joined_env s' index = Some use ->
         typing_env_satisfied_strictly statics valuation use ->
         extends s' index valuation valuation' ->
         ∀ n : Z,
           eval_simple valuation simple
           = Some (Value_const (Naked_immediate n)) ->
           variable_is valuation' x n)
    ∧ (state_kinded s ->
       state_kinded s' ∧ kinded_in_target aliases_of_relation s' x)).
  { intros [= <- <-].
    split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
    split; [ intros y [] | ]. split; [ intros; exact I | ].
    intros Hk. split; [ apply Hkinded1; exact Hk | intros simple kind [] ]. }
  destruct joined as [[var | sym | c] | ];
    [ | apply Hnone; exact Hstep .. ].
  injection Hstep as <- <-.
  destruct (Hok (Var var) eq_refl) as (Htarget & Hbound).
  split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
  split; [ exact Htarget | ].
  split.
  - intros index simple use statics valuation valuation' Hin Huse Hsatisfied
      Hextends n Heval.
    exact
      (Hbound index simple use statics valuation valuation' _ Hin Huse
         Hsatisfied Hextends Heval).
  - intros Hk. split; [ apply Hkinded1; exact Hk | ].
    intros simple kind [[= <- <-] | []].
    apply Hkinded1; [ exact Hk | reflexivity ].
Qed.

(* What the [Simple] of a head says of null, for [is_null_simples]. *)
Definition is_null_simple_of (head : head_of_kind_value) (simple : simple)
    : Prop :=
  match is_null_of_head head with
  | Not_null => simple = untagged_const_bool false
  | Maybe_null (Some x) => simple = Var x
  | Maybe_null None => False
  end.

Lemma is_null_simples_spec (heads : list (Index.t * head_of_kind_value)) :
  ∀ simples : list (Index.t * simple),
    is_null_simples heads = Some simples ->
    map fst simples = map fst heads
    ∧ (∀ (index : Index.t) (head : head_of_kind_value),
         In (index, head) heads ->
         ∃ simple : simple,
           In (index, simple) simples ∧ is_null_simple_of head simple)
    ∧ ∀ (index : Index.t) (simple : simple),
        In (index, simple) simples ->
        ∃ head : head_of_kind_value,
          In (index, head) heads ∧ is_null_simple_of head simple.
Proof.
  induction heads as [ | [id [non_null is_null]] heads IH];
    intros simples Hsimples'; simpl in Hsimples'.
  - injection Hsimples' as <-. repeat split; [ intros ? ? [] | intros ? ? [] ].
  - assert (Hcons :
      ∀ simple : simple,
        is_null_simple_of (Head_of_kind_value non_null is_null) simple ->
        option_map (cons (id, simple)) (is_null_simples heads) = Some simples ->
        map fst simples = map fst ((id, Head_of_kind_value non_null is_null)
                                   :: heads)
        ∧ (∀ (index : Index.t) (head : head_of_kind_value),
             In (index, head)
               ((id, Head_of_kind_value non_null is_null) :: heads) ->
             ∃ simple : FlambdaModel.simple,
               In (index, simple) simples ∧ is_null_simple_of head simple)
        ∧ ∀ (index : Index.t) (simple : FlambdaModel.simple),
            In (index, simple) simples ->
            ∃ head : head_of_kind_value,
              In (index, head)
                ((id, Head_of_kind_value non_null is_null) :: heads)
              ∧ is_null_simple_of head simple).
    { intros simple Hsimple Hrest.
      destruct (is_null_simples heads) as [rest | ]; [ | discriminate ].
      injection Hrest as <-.
      destruct (IH rest eq_refl) as (Hfst & Hto & Hfrom).
      repeat split.
      - simpl. rewrite Hfst. reflexivity.
      - intros index head [[= <- <-] | Hin].
        + exists simple. split; [ left; reflexivity | exact Hsimple ].
        + destruct (Hto index head Hin) as (simple' & Hin' & Hsimple').
          exists simple'. split; [ right; exact Hin' | exact Hsimple' ].
      - intros index simple' [[= <- <-] | Hin].
        + eexists. split; [ left; reflexivity | exact Hsimple ].
        + destruct (Hfrom index simple' Hin) as (head & Hin' & Hsimple').
          exists head. split; [ right; exact Hin' | exact Hsimple' ]. }
    destruct is_null as [ | [x | ]].
    + exact (Hcons _ eq_refl Hsimples').
    + exact (Hcons _ eq_refl Hsimples').
    + discriminate.
Qed.

Theorem n_way_join_is_null_is_sound :
  n_way_join_is_null_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    n_way_join_simples.
Proof.
  intros s s' heads is_null Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_is_null in Hstep.
  (* The answer that says nothing. *)
  assert (Hnone :
    ∀ s1 : state,
      state_valid s1 -> grows s s1 -> (state_kinded s -> state_kinded s1) ->
      Some (Maybe_null None, s1) = Some (is_null, s') ->
      state_valid s' ∧ grows s s'
      ∧ in_target variables_of_is_null s' is_null
      ∧ (∀ (index : Index.t) (head : head_of_kind_value)
           (use : Typing_env.t) (statics : static_env)
           (valuation valuation' : env),
           In (index, head) heads ->
           joined_env s' index = Some use ->
           typing_env_satisfied_strictly statics valuation use ->
           extends s' index valuation valuation' ->
           ∀ null : bool,
             is_null_says valuation (is_null_of_head head) null ->
             is_null_says valuation' is_null null)
      ∧ (state_kinded s ->
         state_kinded s' ∧ kinded_in_target aliases_of_is_null s' is_null)).
  { intros s1 Hvalid1 Hgrows Hk [= <- <-].
    split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
    split; [ intros y [] | ]. split; [ intros; exact I | ].
    intros Hk'. split; [ exact (Hk Hk') | intros simple kind [] ]. }
  destruct (is_null_simples heads) as [simples | ] eqn:Hsimples';
    [ | exact (Hnone s Hvalid (grows_refl s) (fun H => H) Hstep) ].
  destruct (is_null_simples_spec heads simples Hsimples')
    as (Hfst & Hto & Hfrom).
  destruct (n_way_join_simples s (Naked_number Kind_naked_immediate) simples)
    as [[joined s1] | ] eqn:Hjoin; [ | discriminate ].
  assert (Hdistinct' : join_args_distinct simples).
  { unfold join_args_distinct. rewrite Hfst. exact Hdistinct. }
  assert (Hkinds :
    args_in_scope
      (fun use simple =>
         simple_of_kind use simple (Naked_number Kind_naked_immediate))
      s simples).
  { intros index simple Hin.
    destruct (Hfrom index simple Hin) as ([non_null is_null'] & Hin' & Hsimple).
    destruct (Hargs index _ Hin') as (use & Huse & _ & Haliases).
    exists use. split; [ exact Huse | ].
    unfold is_null_simple_of in Hsimple. simpl in Hsimple.
    destruct is_null' as [ | [x | ]]; [ | | contradiction ]; subst simple.
    - reflexivity.
    - apply Haliases. simpl. apply in_or_app. right. left. reflexivity. }
  destruct
    (Hsimples s s1 _ simples joined Hvalid Hwf Hkinded Hdistinct' Hkinds Hjoin)
    as (Hvalid1 & Hgrows & _ & _ & Hok & Hkinded1).
  assert (Hk1 : state_kinded s -> state_kinded s1).
  { intros Hk. apply Hkinded1. exact Hk. }
  (* What the join of the [Simple]s gives for a head. *)
  assert (Hjoined :
    ∀ (joined' : simple) (index : Index.t) (head : head_of_kind_value)
      (use : Typing_env.t) (statics : static_env) (valuation valuation' : env)
      (null : bool),
      joined = Or_bottom.Ok joined' ->
      In (index, head) heads ->
      joined_env s1 index = Some use ->
      typing_env_satisfied_strictly statics valuation use ->
      extends s1 index valuation valuation' ->
      is_null_says valuation (is_null_of_head head) null ->
      eval_simple valuation' joined'
      = Some (Value_const (Naked_immediate (if null then 1%Z else 0%Z)))).
  { intros joined' index head use statics valuation valuation' null Hjoined'
      Hin Huse Hsatisfied Hextends Hsays.
    destruct (Hok joined' Hjoined') as (_ & Hbound).
    destruct (Hto index head Hin) as (simple & Hin' & Hsimple).
    apply
      (Hbound index simple use statics valuation valuation' _ Hin' Huse
         Hsatisfied Hextends).
    unfold is_null_simple_of in Hsimple.
    destruct (is_null_of_head head) as [ | [x | ]];
      [ | | contradiction ]; subst simple.
    - simpl in Hsays. subst null. reflexivity.
    - exact Hsays. }
  destruct joined as [[var | sym | c] | ].
  - (* A variable. *)
    injection Hstep as <- <-.
    destruct (Hok (Var var) eq_refl) as (Htarget & _).
    split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
    split; [ exact Htarget | ].
    split.
    + intros index head use statics valuation valuation' Hin Huse Hsatisfied
        Hextends null Hsays.
      exact
        (Hjoined _ index head use statics valuation valuation' null eq_refl
           Hin Huse Hsatisfied Hextends Hsays).
    + intros Hk. split; [ exact (Hk1 Hk) | ].
      intros simple kind [[= <- <-] | []].
      apply Hkinded1; [ exact Hk | reflexivity ].
  - discriminate.
  - (* A constant. *)
    assert (Hfalse :
      ∀ i : Z,
        c = Naked_immediate i -> Z.eqb i 0 = true ->
        Some (Not_null, s1) = Some (is_null, s') ->
        state_valid s' ∧ grows s s'
        ∧ in_target variables_of_is_null s' is_null
        ∧ (∀ (index : Index.t) (head : head_of_kind_value)
             (use : Typing_env.t) (statics : static_env)
             (valuation valuation' : env),
             In (index, head) heads ->
             joined_env s' index = Some use ->
             typing_env_satisfied_strictly statics valuation use ->
             extends s' index valuation valuation' ->
             ∀ null : bool,
               is_null_says valuation (is_null_of_head head) null ->
               is_null_says valuation' is_null null)
        ∧ (state_kinded s ->
           state_kinded s' ∧ kinded_in_target aliases_of_is_null s' is_null)).
    { intros i -> Hzero [= <- <-]. apply Z.eqb_eq in Hzero. subst i.
      split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
      split; [ intros y [] | ].
      split.
      - intros index head use statics valuation valuation' Hin Huse
          Hsatisfied Hextends null Hsays.
        pose proof
          (Hjoined _ index head use statics valuation valuation' null eq_refl
             Hin Huse Hsatisfied Hextends Hsays) as Heval.
        simpl in Heval. destruct null; [ discriminate | reflexivity ].
      - intros Hk. split; [ exact (Hk1 Hk) | intros simple kind [] ]. }
    destruct c as [i | | | | | | | | | | | | | | ];
      try exact (Hnone s1 Hvalid1 Hgrows Hk1 Hstep).
    destruct (Z.eqb i 0) eqn:Hzero.
    + exact (Hfalse i eq_refl Hzero Hstep).
    + exact (Hnone s1 Hvalid1 Hgrows Hk1 Hstep).
  - exact (Hnone s1 Hvalid1 Hgrows Hk1 Hstep).
Qed.

End Simples.

(* ======================================================================== *)
(* Numbers                                                                  *)
(* ======================================================================== *)

Lemma fold_union_keeps (ts : list (Index.t * list Z)) :
  ∀ (acc : list Z) (n : Z),
    n ∈ acc ->
    n ∈ List.fold_left (fun t1 t2 => numbers_union t1 (snd t2)) ts acc.
Proof.
  induction ts as [ | [id t] ts IH]; intros acc n Hin; simpl; [ exact Hin | ].
  apply IH. apply numbers_union_in. left. exact Hin.
Qed.

Lemma fold_union_in (ts : list (Index.t * list Z)) :
  ∀ (acc : list Z) (index : Index.t) (t : list Z) (n : Z),
    In (index, t) ts -> n ∈ t ->
    n ∈ List.fold_left (fun t1 t2 => numbers_union t1 (snd t2)) ts acc.
Proof.
  induction ts as [ | [id t'] ts IH]; intros acc index t n Hin Hn; simpl;
    [ destruct Hin | ].
  destruct Hin as [[= <- <-] | Hin].
  - apply fold_union_keeps. apply numbers_union_in. right. exact Hn.
  - exact (IH _ index t n Hin Hn).
Qed.

Theorem n_way_join_head_of_kind_naked_numbers_is_sound :
  n_way_join_head_of_kind_naked_numbers_sound typing_env_well_formed
    joined_env definitions_of_existentials kind_in_target_env state_valid
    state_kinded.
Proof.
  intros k s s' args answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  destruct args as [ | [id1 head1] heads]; [ discriminate | ].
  injection Hstep as <- <-.
  split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
  split; [ intros x [] | ].
  split.
  - intros index numbers use statics valuation valuation' Hin _ _ _ v
      (c & n & Hv & Hkind & Hnumber & Hn).
    exists c, n. repeat split; try assumption. simpl.
    destruct Hin as [[= <- <-] | Hin].
    + apply fold_union_keeps. exact Hn.
    + exact (fold_union_in _ _ index numbers n Hin Hn).
  - intros Hk. split; [ exact Hk | intros simple kind [] ].
Qed.

Section Reduce.

Context
  (reduce_head_of_kind_naked_immediate :
     Typing_env.t -> head_of_kind_naked_immediate
     -> Or_bottom.t head_of_kind_naked_immediate).

Hypothesis Hreduce :
  reduce_head_of_kind_naked_immediate_sound
    reduce_head_of_kind_naked_immediate.

(* The numbers that the fold answers hold those that it was given to
   start with, and every number that has one of the heads. *)
Lemma join_naked_immediates_spec (s : state)
    (heads : list (Index.t * head_of_kind_naked_immediate)) :
  ∀ (immediates : Or_unknown.t (list Z)) (imms : list Z),
    join_naked_immediates joined_env reduce_head_of_kind_naked_immediate s
      immediates heads
    = Some (Or_unknown.Known imms) ->
    (∃ imms0 : list Z,
       immediates = Or_unknown.Known imms0 ∧ ∀ n : Z, n ∈ imms0 -> n ∈ imms)
    ∧ ∀ (index : Index.t) (head : head_of_kind_naked_immediate)
        (use : Typing_env.t) (statics : static_env) (valuation : env)
        (v : value),
        In (index, head) heads ->
        joined_env s index = Some use ->
        typing_env_satisfied_strictly statics valuation use ->
        head_of_kind_naked_immediate_satisfied statics valuation v head ->
        ∃ n : Z, v = Value_const (Naked_immediate n) ∧ n ∈ imms.
Proof.
  induction heads as [ | [id2 head2] heads IH]; intros immediates imms Hjoin;
    simpl in Hjoin.
  - injection Hjoin as ->. split; [ exists imms; auto | intros ? ? ? ? ? ? [] ].
  - destruct (joined_env s id2) as [tenv | ] eqn:Htenv; [ | discriminate ].
    destruct (reduce_head_of_kind_naked_immediate tenv head2)
      as [head2' | ] eqn:Hreduced.
    + destruct (IH _ imms Hjoin) as ((imms0' & Himms0' & Hkeeps) & Hheads).
      destruct immediates as [imms0 | ]; [ | discriminate ].
      destruct (naked_immediates head2') as [imms2 | ] eqn:Himms2;
        [ | discriminate ].
      injection Himms0' as <-.
      split.
      * exists imms0. split; [ reflexivity | ].
        intros n Hn. apply Hkeeps, numbers_union_in. left. exact Hn.
      * intros index head use statics valuation v [[= <- <-] | Hin] Huse
          Hsatisfied Hhead.
        -- rewrite Htenv in Huse. injection Huse as <-.
           destruct (Hreduce tenv statics valuation v head2 Hsatisfied Hhead)
             as (head' & Hhead' & n & Hv & Hn & _).
           rewrite Hreduced in Hhead'. injection Hhead' as <-.
           rewrite Himms2 in Hn.
           exists n. split; [ exact Hv | ].
           apply Hkeeps, numbers_union_in. right. exact Hn.
        -- exact (Hheads index head use statics valuation v Hin Huse
                    Hsatisfied Hhead).
    + destruct (IH _ imms Hjoin) as (Himms0 & Hheads).
      split; [ exact Himms0 | ].
      intros index head use statics valuation v [[= <- <-] | Hin] Huse
        Hsatisfied Hhead.
      * rewrite Htenv in Huse. injection Huse as <-.
        destruct (Hreduce tenv statics valuation v head2 Hsatisfied Hhead)
          as (head' & Hhead' & _).
        congruence.
      * exact (Hheads index head use statics valuation v Hin Huse Hsatisfied
                 Hhead).
Qed.

Theorem n_way_join_head_of_kind_naked_immediate_is_sound :
  n_way_join_head_of_kind_naked_immediate_sound typing_env_well_formed
    joined_env definitions_of_existentials kind_in_target_env state_valid
    state_kinded reduce_head_of_kind_naked_immediate.
Proof.
  intros s s' heads answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_head_of_kind_naked_immediate in Hstep.
  destruct
    (join_naked_immediates joined_env reduce_head_of_kind_naked_immediate s
       (Or_unknown.Known []) heads)
    as [[imms | ] | ] eqn:Hjoin; [ | | discriminate ].
  - cbv beta iota in Hstep.
    destruct (Keyed.is_empty imms); [ discriminate | ].
    injection Hstep as <- <-.
    destruct (join_naked_immediates_spec s heads _ _ Hjoin) as (_ & Hheads).
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ].
    split.
    + intros index head use statics valuation valuation' Hin Huse Hsatisfied
        _ v Hhead.
      destruct (Hheads index head use statics valuation v Hin Huse Hsatisfied
                  Hhead)
        as (n & Hv & Hn).
      exists n. split; [ exact Hv | ]. split; [ exact Hn | intros ? ? [] ].
    + intros Hk. split; [ exact Hk | intros simple kind [] ].
  - injection Hstep as <- <-.
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ].
    split; [ intros; exact I | ].
    intros Hk. split; [ exact Hk | intros simple kind [] ].
Qed.

End Reduce.

(* ======================================================================== *)
(* Environment extensions                                                   *)
(* ======================================================================== *)

Section Extension.

Context
  (join_env_n_way_join_env_extension :
     state -> list (Index.t * env_extension)
     -> option (Or_bottom.t (env_extension * state))).

Hypothesis Hextension :
  n_way_join_env_extension_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    join_env_n_way_join_env_extension.

Theorem n_way_join_env_extension_is_sound :
  n_way_join_env_extension_sound_here typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    join_env_n_way_join_env_extension.
Proof.
  intros s s' extensions answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_env_extension in Hstep.
  destruct (join_env_n_way_join_env_extension s extensions)
    as [joined | ] eqn:Hjoin; [ | discriminate ].
  assert (Hscope :
    args_in_scope env_extension_in_scope s extensions).
  { intros index extension Hin.
    destruct (Hargs index extension Hin) as (use & Huse & Hknown & _).
    exists use. split; [ exact Huse | exact Hknown ]. }
  assert (Hkinds :
    args_in_scope env_extension_kinded s extensions).
  { intros index extension Hin.
    destruct (Hargs index extension Hin) as (use & Huse & _ & Haliases).
    exists use. split; [ exact Huse | exact Haliases ]. }
  destruct
    (Hextension s extensions joined Hvalid Hwf Hkinded Hdistinct Hscope Hjoin)
    as (Hbottom & Hok & Hkinded').
  destruct joined as [[joined s1] | ].
  - injection Hstep as <- <-.
    destruct (Hok joined s1 eq_refl) as (Hvalid1 & Hgrows & Htarget & Hbound).
    split; [ exact Hvalid1 | ]. split; [ exact Hgrows | ].
    split; [ exact Htarget | ].
    split.
    + intros index extension use statics valuation valuation' Hin Huse
        Hsatisfied Hextends Hholds.
      exact
        (Hbound index extension use statics valuation valuation' Hin Huse
           Hsatisfied Hextends Hholds).
    + intros Hk. exact (Hkinded' Hk Hkinds joined s1 eq_refl).
  - injection Hstep as <- <-. rewrite (Hbottom eq_refl).
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ].
    split; [ intros ? ? ? ? ? ? [] | ].
    intros Hk. split; [ exact Hk | intros simple kind [] ].
Qed.

End Extension.

(* ======================================================================== *)
(* The functions that call the join of types                                *)
(* ======================================================================== *)

Section Body.

Context
  (n_way_join_simples :
     state -> flambda_kind -> list (Index.t * simple)
     -> option (Or_bottom.t simple * state))
  (import_type : state -> flambda_type -> option state)
  (join_env_n_way_join_env_extension :
     state -> list (Index.t * env_extension)
     -> option (Or_bottom.t (env_extension * state)))
  (expand_head : Typing_env.t -> flambda_type -> option Expanded_type.t)
  (reduce_head_of_kind_naked_immediate :
     Typing_env.t -> head_of_kind_naked_immediate
     -> Or_bottom.t head_of_kind_naked_immediate)
  (type_eqb : flambda_type -> flambda_type -> bool)
  (block_shape_eqb : block_shape -> block_shape -> bool).

Hypothesis Hsimples :
  n_way_join_simples_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    n_way_join_simples.
Hypothesis Himport :
  import_type_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    import_type.
Hypothesis Hextension :
  n_way_join_env_extension_sound typing_env_well_formed joined_env
    definitions_of_existentials kind_in_target_env state_valid state_kinded
    join_env_n_way_join_env_extension.
Hypothesis Hexpand : expand_head_sound typing_env_well_formed expand_head.
Hypothesis Hreduce :
  reduce_head_of_kind_naked_immediate_sound
    reduce_head_of_kind_naked_immediate.
Hypothesis Heqb : type_eqb_sound type_eqb.
Hypothesis Hshape : block_shape_eqb_sound block_shape_eqb.

Variable n_way_join_rec :
  state -> list (Index.t * flambda_type)
  -> option (Or_unknown.t flambda_type * state).

Hypothesis Hrec :
  step_sound free_variables aliases_with_kinds (of_known free_variables)
    (of_known aliases_with_kinds) type_bound n_way_join_rec.

(* The invariant of a fold that threads the state from [s]. *)
Definition threaded (s s1 : state) : Prop :=
  state_valid s1 ∧ grows s s1 ∧ (state_kinded s -> state_kinded s1).

(* ------------------------------------------------------------------------ *)
(* Products indexed by slots                                                *)
(* ------------------------------------------------------------------------ *)

Definition variables_of_product (product : finite_map flambda_type)
    : list variable :=
  flat_map (fun binding => free_variables (snd binding)) product.

Definition aliases_of_product (product : finite_map flambda_type)
    : list (simple * flambda_kind) :=
  flat_map (fun binding => aliases_with_kinds (snd binding)) product.

(* Each component of the join bounds the component of each product
   given. *)
Definition product_bound (statics : static_env) (valuation : env)
    (product : finite_map flambda_type) (valuation' : env)
    (joined : finite_map flambda_type) : Prop :=
  ∀ (g : positive) (ty : flambda_type),
    lookup g joined = Some ty ->
    ∃ ty_i : flambda_type,
      lookup g product = Some ty_i
      ∧ ∀ v : value,
          type_satisfied statics valuation v ty_i ->
          type_satisfied statics valuation' v ty.

Lemma lookup_in_product {A : Type} (g : positive) (a : A)
    (product : finite_map A) :
  lookup g product = Some a -> In (g, a) product.
Proof. apply (keyed_lookup_in Pos.eqb Pos.eqb_eq). Qed.

Theorem n_way_join_generic_product_is_sound :
  step_sound variables_of_product aliases_of_product variables_of_product
    aliases_of_product product_bound
    (n_way_join_generic_product n_way_join_rec).
Proof.
  intros s s' products answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_generic_product in Hstep.
  destruct products as [ | product0 products0] eqn:Hproducts.
  { injection Hstep as <- <-.
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ]. split; [ intros ? ? ? ? ? ? [] | ].
    intros Hk. split; [ exact Hk | intros simple kind [] ]. }
  rewrite <- Hproducts in *. clear Hproducts product0 products0.
  (* The types gathered for an index are arguments of the join. *)
  assert (Hgathered :
    ∀ (g : positive) (tys : list (Index.t * flambda_type)),
      lookup g (gather_components products) = Some tys ->
      join_args_distinct tys
      ∧ args_in_scope (arg_ok free_variables aliases_with_kinds) s tys
      ∧ ∀ (index : Index.t) (product : finite_map flambda_type),
          In (index, product) products ->
          ∃ ty_i : flambda_type,
            lookup g product = Some ty_i ∧ In (index, ty_i) tys).
  { intros g tys Htys.
    destruct (gather_components_spec products g tys Htys)
      as (Hfst & Hto & Hfrom).
    split; [ | split; [ | exact Hto ] ].
    - unfold join_args_distinct. rewrite Hfst. apply NoDup_rev.
      exact Hdistinct.
    - apply (args_of_parts _ _ _ _ s products tys Hargs).
      intros index ty Hin.
      destruct (Hfrom index ty Hin) as (product & Hty & Hin').
      exists product. split; [ exact Hin' | ].
      apply lookup_in_product in Hty.
      split; intros y Hy;
        [ unfold variables_of_product | unfold aliases_of_product ];
        apply in_flat_map; exists (g, ty); split; assumption. }
  (* Each step of the fold is a call of the join of types. *)
  set (step :=
    fun (_ : positive) (tys : list (Index.t * flambda_type)) (env : state) =>
      match n_way_join_rec env tys with
      | Some (joined, env) =>
        match joined with
        | Or_unknown.Known ty => Some (Some ty, env)
        | Or_unknown.Unknown => Some (None, env)
        end
      | None => None
      end) in Hstep.
  assert (Hcall :
    ∀ (g : positive) (tys : list (Index.t * flambda_type)) (s1 : state)
      (a : option flambda_type) (s2 : state),
      lookup g (gather_components products) = Some tys ->
      threaded s s1 ->
      step g tys s1 = Some (a, s2) ->
      threaded s s2 ∧ grows s1 s2
      ∧ ∀ ty : flambda_type,
          a = Some ty ->
          answer_holds_from (of_known free_variables)
            (of_known aliases_with_kinds) type_bound s1 s2 tys
            (Or_unknown.Known ty)).
  { intros g tys s1 a s2 Htys (Hvalid1 & Hgrows1 & Hk1) Hstep1.
    destruct (Hgathered g tys Htys) as (Hdistinct' & Hargs' & _).
    unfold step in Hstep1.
    destruct (n_way_join_rec s1 tys) as [[joined s2'] | ] eqn:Hjoin;
      [ | discriminate ].
    destruct
      (step_sound_at _ _ _ _ _ _ Hrec s s1 s2' tys joined Hwf Hkinded Hgrows1
         Hvalid1 Hdistinct' Hargs' Hjoin)
      as (Hvalid2 & Hgrows2 & Hk2 & Hholds).
    assert (Hs2 : s2' = s2) by (destruct joined; congruence). subst s2'.
    split; [ | split; [ exact Hgrows2 | ] ].
    - split; [ exact Hvalid2 | ].
      split; [ exact (grows_trans _ _ _ Hgrows1 Hgrows2) | ].
      intros Hk. exact (Hk2 (Hk1 Hk)).
    - intros ty ->. destruct joined as [ty' | ]; [ | discriminate ].
      injection Hstep1 as ->. exact Hholds. }
  destruct
    (filter_map_fold_spec Pos.eqb Pos.eqb_eq (threaded s) grows grows_refl
       grows_trans step (gather_components products)
       (fun g tys s1 a s2 Htys Hs1 Hstep1 =>
          let H := Hcall g tys s1 a s2 Htys Hs1 Hstep1 in
          conj (proj1 H) (proj1 (proj2 H)))
       s answer s'
       (conj Hvalid (conj (grows_refl s) (fun H => H))) Hstep)
    as ((Hvalid' & Hgrows & Hk') & _ & Hin & Hfound & _).
  (* What a binding of the answer comes from. *)
  assert (Hbinding :
    ∀ (g : positive) (ty : flambda_type),
      lookup g answer = Some ty ->
      ∃ (tys : list (Index.t * flambda_type)) (s1 s2 : state),
        lookup g (gather_components products) = Some tys
        ∧ grows s2 s' ∧ (state_kinded s -> state_kinded s1)
        ∧ answer_holds_from (of_known free_variables)
            (of_known aliases_with_kinds) type_bound s1 s2 tys
            (Or_unknown.Known ty)).
  { intros g ty Hty.
    destruct (Hfound g ty Hty)
      as (tys & s1 & s2 & Htys & Hs1 & _ & Hstep1 & Hgrows2).
    exists tys, s1, s2. split; [ exact Htys | ]. split; [ exact Hgrows2 | ].
    split; [ exact (proj2 (proj2 Hs1)) | ].
    exact (proj2 (proj2 (Hcall g tys s1 _ s2 Htys Hs1 Hstep1)) ty eq_refl). }
  split; [ exact Hvalid' | ]. split; [ exact Hgrows | ].
  split; [ | split ].
  - intros x Hx. apply in_flat_map in Hx as ([g ty] & Hin' & Hx).
    destruct (Hbinding g ty (Hin g ty Hin'))
      as (tys & s1 & s2 & _ & Hgrows2 & _ & Hholds).
    exact (proj1 (Hholds s' Hgrows2) x Hx).
  - intros index product use statics valuation valuation' Hin' Huse
      Hsatisfied Hextends g ty Hty.
    destruct (Hbinding g ty Hty)
      as (tys & s1 & s2 & Htys & Hgrows2 & _ & Hholds).
    destruct (Hgathered g tys Htys) as (_ & _ & Hto).
    destruct (Hto index product Hin') as (ty_i & Hty_i & Hin'').
    exists ty_i. split; [ exact Hty_i | ].
    exact
      (proj1 (proj2 (Hholds s' Hgrows2)) index ty_i use statics valuation
         valuation' Hin'' Huse Hsatisfied Hextends).
  - intros Hk. split; [ exact (Hk' Hk) | ].
    intros simple kind Hsimple.
    apply in_flat_map in Hsimple as ([g ty] & Hin' & Hsimple).
    destruct (Hbinding g ty (Hin g ty Hin'))
      as (tys & s1 & s2 & _ & Hgrows2 & Hk1 & Hholds).
    exact (proj2 (proj2 (Hholds s' Hgrows2)) (Hk1 Hk) simple kind Hsimple).
Qed.

(* ------------------------------------------------------------------------ *)
(* Products indexed by integers: the fields of blocks                       *)
(* ------------------------------------------------------------------------ *)

Definition variables_of_fields (tys : list flambda_type) : list variable :=
  flat_map free_variables tys.

Definition aliases_of_fields (tys : list flambda_type)
    : list (simple * flambda_kind) :=
  flat_map aliases_with_kinds tys.

(* The fields of a block of the shape that have the types given have
   the types joined. *)
Definition fields_bound (shape : block_shape) (statics : static_env)
    (valuation : env) (tys : list flambda_type) (valuation' : env)
    (joined : list flambda_type) : Prop :=
  ∀ (tag : Z) (fields : list value),
    block_has_shape shape tag fields ->
    fields_satisfied (type_satisfied statics valuation) tys fields ->
    fields_satisfied (type_satisfied statics valuation') joined fields.

(* A value that has a type in an input, whose environment knows the
   variables of the type, has it under a valuation that extends the
   input's. *)
Lemma type_satisfied_extends (s : state) (index : Index.t) (use : Typing_env.t)
    (statics : static_env) (valuation valuation' : env) (v : value)
    (ty : flambda_type) :
  joined_env s index = Some use ->
  (∀ x : variable, x ∈ free_variables ty -> knows use x) ->
  extends s index valuation valuation' ->
  type_satisfied statics valuation v ty ->
  type_satisfied statics valuation' v ty.
Proof.
  intros Huse Hknown (use' & Huse' & Hagrees & _) Hty.
  rewrite Huse in Huse'. injection Huse' as <-.
  apply (type_satisfied_coincide statics valuation valuation' v ty);
    [ | exact Hty ].
  intros x Hx. symmetry. apply Hagrees, Hknown, Hx.
Qed.

(* [import_types]: every type given is in the target at every later
   state, and kinded there if it was kinded in an input. *)
Lemma import_types_spec (tys : list flambda_type) :
  ∀ s s' : state,
    state_valid s -> envs_well_formed s -> envs_kinded s ->
    import_types import_type s tys = Some s' ->
    state_valid s' ∧ grows s s'
    ∧ (∀ ty : flambda_type,
         ty ∈ tys -> in_target free_variables s' ty)
    ∧ (state_kinded s ->
       (∀ ty : flambda_type,
          ty ∈ tys ->
          ∃ (index : Index.t) (use : Typing_env.t),
            joined_env s index = Some use ∧ type_kinded use ty) ->
       state_kinded s'
       ∧ ∀ ty : flambda_type,
           ty ∈ tys -> kinded_in_target aliases_with_kinds s' ty).
Proof.
  induction tys as [ | ty tys IH]; intros s s' Hvalid Hwf Hkinded Himports;
    simpl in Himports.
  - injection Himports as <-.
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ intros ? [] | ].
    intros Hk _. split; [ exact Hk | intros ? [] ].
  - destruct (import_type s ty) as [s1 | ] eqn:Himported; [ | discriminate ].
    destruct (Himport s s1 ty Hvalid Hwf Hkinded Himported)
      as (Hvalid1 & Hgrows1 & Htarget1 & Hkinds1).
    destruct
      (IH s1 s' Hvalid1 (grows_well_formed _ _ Hgrows1 Hwf)
         (grows_kinded _ _ Hgrows1 Hkinded) Himports)
      as (Hvalid' & Hgrows' & Htargets & Hkinds').
    split; [ exact Hvalid' | ].
    split; [ exact (grows_trans _ _ _ Hgrows1 Hgrows') | ].
    split.
    + intros ty' [<- | Hin].
      * exact (grows_in_target free_variables _ _ ty Hgrows' Htarget1).
      * exact (Htargets ty' Hin).
    + intros Hk Hkinded_tys.
      destruct (Hkinds1 Hk (Hkinded_tys ty (or_introl eq_refl)))
        as (Hk1 & Hty).
      assert (Hrest :
        ∀ ty' : flambda_type,
          ty' ∈ tys ->
          ∃ (index : Index.t) (use : Typing_env.t),
            joined_env s1 index = Some use ∧ type_kinded use ty').
      { intros ty' Hin.
        destruct (Hkinded_tys ty' (or_intror Hin)) as (index & use & Huse & H).
        exists index, use. rewrite (grows_joined_env _ _ index Hgrows1).
        split; assumption. }
      destruct (Hkinds' Hk1 Hrest) as (Hk' & Htys).
      split; [ exact Hk' | ].
      intros ty' [<- | Hin].
      * exact (grows_kinded_in_target aliases_with_kinds _ _ ty Hgrows' Hty).
      * exact (Htys ty' Hin).
Qed.

(* Fields that are the same have the same values. *)
Lemma fields_the_same_spec (least_length : nat) :
  ∀ first_fields other_fields : list flambda_type,
    fields_the_same type_eqb least_length first_fields other_fields = true ->
    ∀ i : nat,
      i < least_length ->
      ∃ first_field other_field : flambda_type,
        nth_error first_fields i = Some first_field
        ∧ nth_error other_fields i = Some other_field
        ∧ ∀ (statics : static_env) (vars : env) (v : value),
            type_satisfied statics vars v other_field
            <-> type_satisfied statics vars v first_field.
Proof.
  induction least_length as [ | least_length IH];
    intros first_fields other_fields Hsame i Hi; [ lia | ].
  destruct first_fields as [ | first_field first_fields];
    [ discriminate | ].
  destruct other_fields as [ | other_field other_fields];
    [ discriminate | ].
  simpl in Hsame. apply andb_true_iff in Hsame as [Hfield Hsame].
  destruct i as [ | i].
  - exists first_field, other_field. repeat split; try reflexivity.
    + apply (Heqb other_field first_field Hfield).
    + apply (Heqb other_field first_field Hfield).
  - apply (IH first_fields other_fields Hsame i). lia.
Qed.

(* The slow path: the fields joined from an index on. *)
Lemma join_fields_spec (s : state) (shape : block_shape)
    (fields : list (Index.t * list flambda_type)) :
  envs_well_formed s -> envs_kinded s ->
  join_args_distinct fields ->
  args_in_scope (arg_ok variables_of_fields aliases_of_fields) s fields ->
  ∀ (count index : nat) (s1 : state) (answer : list flambda_type)
    (s' : state),
    threaded s s1 ->
    join_fields n_way_join_rec s1 shape fields index count
    = Some (answer, s') ->
    threaded s s' ∧ grows s1 s'
    ∧ in_target variables_of_fields s' answer
    ∧ (∀ (k : nat) (ty : flambda_type),
         nth_error answer k = Some ty ->
         ∀ (id : Index.t) (tys : list flambda_type) (use : Typing_env.t)
           (statics : static_env) (valuation valuation' : env),
           In (id, tys) fields ->
           joined_env s' id = Some use ->
           typing_env_satisfied_strictly statics valuation use ->
           extends s' id valuation valuation' ->
           ∃ ty_i : flambda_type,
             nth_error tys (index + k) = Some ty_i
             ∧ ∀ field : value,
                 (∀ kind : flambda_kind,
                    block_shape_element_kind shape (index + k) = Some kind ->
                    kind_of_value field = kind) ->
                 type_satisfied statics valuation field ty_i ->
                 type_satisfied statics valuation' field ty)
    ∧ (state_kinded s -> kinded_in_target aliases_of_fields s' answer).
Proof.
  intros Hwf Hkinded Hdistinct Hargs.
  induction count as [ | count IH]; intros index s1 answer s' Hs1 Hjoin;
    simpl in Hjoin.
  - injection Hjoin as <- <-.
    split; [ exact Hs1 | ]. split; [ apply grows_refl | ].
    split; [ intros x [] | ].
    split; [ intros [ | k] ty [=] | intros _ simple kind [] ].
  - destruct (fields_at index fields) as [tys | ] eqn:Htys; [ | discriminate ].
    destruct (n_way_join_rec s1 tys) as [[joined s2] | ] eqn:Hjoined;
      [ | discriminate ].
    destruct
      (match joined with
       | Or_unknown.Known ty => Some ty
       | Or_unknown.Unknown => unknown_from_shape shape index
       end) as [ty0 | ] eqn:Hty0; [ | discriminate ].
    destruct (join_fields n_way_join_rec s2 shape fields (S index) count)
      as [[rest s3] | ] eqn:Hrest; [ | discriminate ].
    injection Hjoin as <- <-.
    rewrite fields_at_eq in Htys.
    destruct (indexed_map_opt_spec _ _ tys Htys) as (Hfst & Hto & Hfrom).
    destruct Hs1 as (Hvalid1 & Hgrows1 & Hk1).
    assert (Hdistinct' : join_args_distinct tys).
    { unfold join_args_distinct. rewrite Hfst. exact Hdistinct. }
    assert (Hargs' :
      args_in_scope (arg_ok free_variables aliases_with_kinds) s tys).
    { apply (args_of_parts _ _ _ _ s fields tys Hargs).
      intros id ty Hin. destruct (Hfrom id ty Hin) as (tys0 & Hnth & Hin').
      exists tys0. split; [ exact Hin' | ]. apply nth_error_In in Hnth.
      split; intros y Hy;
        [ unfold variables_of_fields | unfold aliases_of_fields ];
        apply in_flat_map; exists ty; split; assumption. }
    destruct
      (step_sound_at _ _ _ _ _ _ Hrec s s1 s2 tys joined Hwf Hkinded Hgrows1
         Hvalid1 Hdistinct' Hargs' Hjoined)
      as (Hvalid2 & Hgrows2 & Hk2 & Hholds).
    assert (Hs2 : threaded s s2).
    { split; [ exact Hvalid2 | ].
      split; [ exact (grows_trans _ _ _ Hgrows1 Hgrows2) | ].
      intros Hk. exact (Hk2 (Hk1 Hk)). }
    destruct (IH (S index) s2 rest s3 Hs2 Hrest)
      as (Hs3 & Hgrows3 & Htarget & Hbound & Hkinds).
    destruct (Hholds s3 Hgrows3) as (Htarget0 & Hbound0 & Hkinds0).
    split; [ exact Hs3 | ].
    split; [ exact (grows_trans _ _ _ Hgrows2 Hgrows3) | ].
    split; [ | split ].
    + intros x Hx. unfold variables_of_fields in Hx. simpl in Hx.
      apply in_app_or in Hx as [Hx | Hx]; [ | exact (Htarget x Hx) ].
      destruct joined as [ty | ].
      * injection Hty0 as <-. exact (Htarget0 x Hx).
      * unfold unknown_from_shape in Hty0.
        destruct (block_shape_element_kind shape index) as [kind | ];
          [ | discriminate ].
        injection Hty0 as <-. rewrite free_variables_unknown in Hx.
        destruct Hx.
    + intros [ | k] ty Hty id tys0 use statics valuation valuation' Hin Huse
        Hsatisfied Hextends.
      * injection Hty as <-. rewrite Nat.add_0_r.
        destruct (Hto id tys0 Hin) as (ty_i & Hnth & Hin').
        exists ty_i. split; [ exact Hnth | ].
        intros field Hkind Hfield.
        destruct joined as [ty | ].
        -- injection Hty0 as <-.
           exact
             (Hbound0 id ty_i use statics valuation valuation' Hin' Huse
                Hsatisfied Hextends field Hfield).
        -- unfold unknown_from_shape in Hty0.
           destruct (block_shape_element_kind shape index) as [kind | ]
             eqn:Hkind'; [ | discriminate ].
           injection Hty0 as <-. apply unknown_satisfied.
           exact (Hkind kind eq_refl).
      * rewrite <- Nat.add_succ_comm.
        exact
          (Hbound k ty Hty id tys0 use statics valuation valuation' Hin Huse
             Hsatisfied Hextends).
    + intros Hk simple kind Hsimple. unfold aliases_of_fields in Hsimple.
      simpl in Hsimple.
      apply in_app_or in Hsimple as [Hsimple | Hsimple];
        [ | exact (Hkinds Hk simple kind Hsimple) ].
      destruct joined as [ty | ].
      * injection Hty0 as <-. exact (Hkinds0 (Hk1 Hk) simple kind Hsimple).
      * unfold unknown_from_shape in Hty0.
        destruct (block_shape_element_kind shape index) as [kind' | ];
          [ | discriminate ].
        injection Hty0 as <-. rewrite aliases_with_kinds_unknown in Hsimple.
        destruct Hsimple.
Qed.

Theorem n_way_join_int_indexed_product_is_sound (shape : block_shape) :
  step_sound variables_of_fields aliases_of_fields variables_of_fields
    aliases_of_fields (fields_bound shape)
    (fun s fields =>
       n_way_join_int_indexed_product import_type type_eqb n_way_join_rec s
         shape fields).
Proof.
  intros s s' fields answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_int_indexed_product in Hstep.
  destruct fields as [ | [id1 first_fields] other_fields] eqn:Hfields;
    [ discriminate | ].
  rewrite <- Hfields in *.
  set (least_length :=
    List.fold_left
      (fun least_length other_fields =>
         Nat.min least_length (length (snd other_fields)))
      other_fields (length first_fields)) in Hstep.
  destruct (least_length_le other_fields (length first_fields))
    as (Hfirst & Hothers).
  fold least_length in Hfirst, Hothers.
  assert (Hleast :
    ∀ (index : Index.t) (tys : list flambda_type),
      In (index, tys) fields -> least_length <= length tys).
  { intros index tys Hin. rewrite Hfields in Hin.
    destruct Hin as [[= <- <-] | Hin];
      [ exact Hfirst | exact (Hothers index tys Hin) ]. }
  destruct
    (forallb
       (fun other_fields =>
          fields_the_same type_eqb least_length first_fields
            (snd other_fields))
       other_fields) eqn:Hsame.
  - (* The fields are the same: those of one input, imported. *)
    destruct
      (find
         (fun fields_of_id =>
            Nat.eqb (length (snd fields_of_id)) least_length)
         fields) as [[id_j fields_j] | ] eqn:Hfind; [ | discriminate ].
    apply find_some in Hfind as [Hin_j Hlength_j]. simpl in Hlength_j.
    apply Nat.eqb_eq in Hlength_j.
    destruct (import_types import_type s fields_j) as [s1 | ] eqn:Himports;
      [ | discriminate ].
    injection Hstep as <- <-.
    destruct (import_types_spec fields_j s s1 Hvalid Hwf Hkinded Himports)
      as (Hvalid1 & Hgrows1 & Htargets & Hkinds).
    (* Every input has, below the least length, fields with the values
       of the first's. *)
    assert (Hsame_first :
      ∀ (index : Index.t) (tys : list flambda_type) (i : nat),
        In (index, tys) fields ->
        i < least_length ->
        ∃ first_field ty_i : flambda_type,
          nth_error first_fields i = Some first_field
          ∧ nth_error tys i = Some ty_i
          ∧ ∀ (statics : static_env) (vars : env) (v : value),
              type_satisfied statics vars v ty_i
              <-> type_satisfied statics vars v first_field).
    { intros index tys i Hin Hi. rewrite Hfields in Hin.
      destruct Hin as [[= <- <-] | Hin].
      - destruct (nth_error first_fields i) as [first_field | ] eqn:Hnth.
        + exists first_field, first_field. repeat split; auto.
        + apply nth_error_None in Hnth. lia.
      - rewrite forallb_forall in Hsame.
        exact
          (fields_the_same_spec least_length first_fields tys
             (Hsame (index, tys) Hin) i Hi). }
    split; [ exact Hvalid1 | ]. split; [ exact Hgrows1 | ].
    split; [ | split ].
    + intros x Hx. apply in_flat_map in Hx as (ty & Hin & Hx).
      exact (Htargets ty Hin x Hx).
    + intros index tys use statics valuation valuation' Hin Huse Hsatisfied
        Hextends tag vals _ Htys.
      rewrite fields_satisfied_nth_iff in Htys.
      apply fields_satisfied_nth_iff. intros i ty_j field Hty_j Hfield.
      assert (Hi : i < least_length).
      { rewrite <- Hlength_j. apply nth_error_Some. congruence. }
      destruct (Hsame_first index tys i Hin Hi)
        as (first_field & ty_i & Hfirst_field & Hty_i & Hi_first).
      destruct (Hsame_first id_j fields_j i Hin_j Hi)
        as (first_field' & ty_j' & Hfirst_field' & Hty_j' & Hj_first).
      rewrite Hfirst_field in Hfirst_field'. injection Hfirst_field' as <-.
      rewrite Hty_j in Hty_j'. injection Hty_j' as <-.
      apply Hj_first, Hi_first.
      destruct (Hargs index tys Hin) as (use0 & Huse0 & Hknown & _).
      rewrite <- (grows_joined_env _ _ index Hgrows1), Huse in Huse0.
      injection Huse0 as <-.
      apply (type_satisfied_extends s1 index use statics valuation valuation'
               field ty_i Huse);
        [ | exact Hextends | exact (Htys i ty_i field Hty_i Hfield) ].
      intros x Hx. apply Hknown. apply in_flat_map. exists ty_i.
      split; [ exact (nth_error_In _ _ Hty_i) | exact Hx ].
    + intros Hk.
      assert (Hkinded_j :
        ∀ ty : flambda_type,
          ty ∈ fields_j ->
          ∃ (index : Index.t) (use : Typing_env.t),
            joined_env s index = Some use ∧ type_kinded use ty).
      { intros ty Hin.
        destruct (Hargs id_j fields_j Hin_j) as (use & Huse & _ & Haliases).
        exists id_j, use. split; [ exact Huse | ].
        intros simple kind Hsimple. apply Haliases. apply in_flat_map.
        exists ty. split; assumption. }
      destruct (Hkinds Hk Hkinded_j) as (Hk1 & Htys).
      split; [ exact Hk1 | ].
      intros simple kind Hsimple.
      apply in_flat_map in Hsimple as (ty & Hin & Hsimple).
      exact (Htys ty Hin simple kind Hsimple).
  - (* The fields are joined one by one. *)
    destruct
      (join_fields_spec s shape fields Hwf Hkinded Hdistinct Hargs
         least_length 0 s answer s'
         (conj Hvalid (conj (grows_refl s) (fun H => H))) Hstep)
      as ((Hvalid' & Hgrows & Hk') & _ & Htarget & Hbound & Hkinds).
    split; [ exact Hvalid' | ]. split; [ exact Hgrows | ].
    split; [ exact Htarget | ].
    split.
    + intros index tys use statics valuation valuation' Hin Huse Hsatisfied
        Hextends tag vals Hshape' Htys.
      rewrite fields_satisfied_nth_iff in Htys.
      apply fields_satisfied_nth_iff. intros k ty field Hty Hfield.
      destruct
        (Hbound k ty Hty index tys use statics valuation valuation' Hin Huse
           Hsatisfied Hextends)
        as (ty_i & Hty_i & Hkept).
      simpl in Hty_i. apply Hkept.
      * intros kind Hkind.
        exact
          (block_shape_element_kind_of_field shape tag vals k field kind
             Hshape' Hfield Hkind).
      * exact (Htys k ty_i field Hty_i Hfield).
    + intros Hk. split; [ exact (Hk' Hk) | exact (Hkinds Hk) ].
Qed.

(* ------------------------------------------------------------------------ *)
(* Closures entries                                                         *)
(* ------------------------------------------------------------------------ *)

(* A closure with its set of closures: what has a closures entry. *)
Definition closure_and_set : Type :=
  value * function_slot * list (function_slot * code_id)
  * list (value_slot * value).

Definition closures_entry_holds (statics : static_env) (vars : env)
    (w : closure_and_set) (entry : closures_entry) : Prop :=
  let '(v, slot, functions, value_slots) := w in
  closures_entry_satisfied statics vars v slot functions value_slots entry.

Lemma rev_map_distinct {A B : Type} (f : A -> B)
    (entries : list (Index.t * A)) :
  join_args_distinct entries ->
  join_args_distinct
    (rev (map (fun entry => (fst entry, f (snd entry))) entries)).
Proof.
  unfold join_args_distinct. intros Hdistinct.
  rewrite map_rev, map_map. simpl. apply NoDup_rev. exact Hdistinct.
Qed.

Lemma rev_map_in {A B : Type} (f : A -> B) (entries : list (Index.t * A))
    (index : Index.t) (b : B) :
  In (index, b) (rev (map (fun entry => (fst entry, f (snd entry))) entries))
  <-> ∃ a : A, In (index, a) entries ∧ b = f a.
Proof.
  rewrite <- in_rev, in_map_iff. split.
  - intros ([index' a] & [= <- <-] & Hin). exists a. split; auto.
  - intros (a & Hin & ->). exists (index, a). split; auto.
Qed.

Theorem n_way_join_closures_entry_is_sound :
  step_sound free_variables_of_closures_entry aliases_of_closures_entry
    free_variables_of_closures_entry aliases_of_closures_entry
    (all_kept closures_entry_holds closures_entry_holds)
    (n_way_join_closures_entry n_way_join_rec).
Proof.
  intros s s' entries answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_closures_entry,
    n_way_join_function_slot_indexed_product,
    n_way_join_value_slot_indexed_product in Hstep.
  set (closure_types :=
    rev
      (map
         (fun entry => (fst entry, closures_entry_closure_types (snd entry)))
         entries)) in Hstep.
  set (value_slot_types :=
    rev
      (map
         (fun entry =>
            (fst entry, closures_entry_value_slot_types (snd entry)))
         entries)) in Hstep.
  destruct (n_way_join_generic_product n_way_join_rec s closure_types)
    as [[closure_types' s1] | ] eqn:Hclosures; [ | discriminate ].
  destruct (n_way_join_generic_product n_way_join_rec s1 value_slot_types)
    as [[value_slot_types' s2] | ] eqn:Hvalue_slots; [ | discriminate ].
  injection Hstep as <- <-.
  assert (Hargs1 :
    args_in_scope (arg_ok variables_of_product aliases_of_product) s
      closure_types).
  { apply (args_of_parts _ _ _ _ s entries closure_types Hargs).
    intros index product Hin. apply rev_map_in in Hin as (entry & Hin & ->).
    exists entry. split; [ exact Hin | ].
    destruct entry as [function_types closures value_slots]. simpl.
    split; apply incl_appl, incl_refl. }
  assert (Hargs2 :
    args_in_scope (arg_ok variables_of_product aliases_of_product) s
      value_slot_types).
  { apply (args_of_parts _ _ _ _ s entries value_slot_types Hargs).
    intros index product Hin. apply rev_map_in in Hin as (entry & Hin & ->).
    exists entry. split; [ exact Hin | ].
    destruct entry as [function_types closures value_slots]. simpl.
    split; apply incl_appr, incl_refl. }
  destruct
    (step_sound_at _ _ _ _ _ _ n_way_join_generic_product_is_sound s s s1
       closure_types closure_types' Hwf Hkinded (grows_refl s) Hvalid
       (rev_map_distinct _ entries Hdistinct) Hargs1 Hclosures)
    as (Hvalid1 & Hgrows1 & Hk1 & Hholds1).
  destruct
    (step_sound_at _ _ _ _ _ _ n_way_join_generic_product_is_sound s s1 s2
       value_slot_types value_slot_types' Hwf Hkinded Hgrows1 Hvalid1
       (rev_map_distinct _ entries Hdistinct) Hargs2 Hvalue_slots)
    as (Hvalid2 & Hgrows2 & Hk2 & Hholds2).
  destruct (Hholds1 s2 Hgrows2) as (Htarget1 & Hbound1 & Hkinds1).
  destruct (Hholds2 s2 (grows_refl s2)) as (Htarget2 & Hbound2 & Hkinds2).
  split; [ exact Hvalid2 | ].
  split; [ exact (grows_trans _ _ _ Hgrows1 Hgrows2) | ].
  split; [ | split ].
  - intros x Hx. simpl in Hx.
    apply in_app_or in Hx as [Hx | Hx];
      [ exact (Htarget1 x Hx) | exact (Htarget2 x Hx) ].
  - intros index [function_types closures value_slots] use statics valuation
      valuation' Hin Huse Hsatisfied Hextends [[[v slot] functions] slots]
      Hentry.
    unfold closures_entry_holds in *.
    apply
      (n_way_join_function_types_sound statics valuation' v slot functions
         slots _ index function_types).
    { apply in_map_iff.
      exists (index, Closures_entry function_types closures value_slots).
      split; [ reflexivity | exact Hin ]. }
    rewrite closures_entry_lookup_iff in Hentry.
    destruct Hentry as (Hfunctions & Hclosures' & Hslots).
    apply closures_entry_lookup_iff.
    split; [ exact Hfunctions | ].
    split.
    + intros g ty closure Hty Hclosure.
      assert (Hin1 : In (index, closures) closure_types).
      { apply rev_map_in.
        exists (Closures_entry function_types closures value_slots).
        split; [ exact Hin | reflexivity ]. }
      destruct
        (Hbound1 index closures use statics valuation valuation' Hin1 Huse
           Hsatisfied Hextends g ty Hty)
        as (ty_i & Hty_i & Hkept).
      exact (Hkept closure (Hclosures' g ty_i closure Hty_i Hclosure)).
    + intros w ty contents Hty Hcontents.
      assert (Hin2 : In (index, value_slots) value_slot_types).
      { apply rev_map_in.
        exists (Closures_entry function_types closures value_slots).
        split; [ exact Hin | reflexivity ]. }
      destruct
        (Hbound2 index value_slots use statics valuation valuation' Hin2 Huse
           Hsatisfied Hextends w ty Hty)
        as (ty_i & Hty_i & Hkept).
      exact (Hkept contents (Hslots w ty_i contents Hty_i Hcontents)).
  - intros Hk. split; [ exact (Hk2 (Hk1 Hk)) | ].
    intros simple kind Hsimple. simpl in Hsimple.
    apply in_app_or in Hsimple as [Hsimple | Hsimple].
    + exact (Hkinds1 Hk simple kind Hsimple).
    + exact (Hkinds2 (Hk1 Hk) simple kind Hsimple).
Qed.

(* ------------------------------------------------------------------------ *)
(* Cases of row-like structures                                             *)
(* ------------------------------------------------------------------------ *)

Section Cases.

(* [W] is what a case admits: a tag and fields, or a closure with its
   set. *)
Context {lattice shape maps_to W : Type}
  (n_way_join_maps_to :
     state -> shape -> list (Index.t * maps_to) -> option (maps_to * state))
  (equal_index : lattice -> lattice -> bool)
  (inter_index : lattice -> lattice -> lattice)
  (n_way_join_shape : list shape -> or_unknown_or_bottom shape)
  (variables_of_maps_to : maps_to -> list variable)
  (aliases_of_maps_to : maps_to -> list (simple * flambda_kind))
  (index_holds : W -> row_like_index lattice shape -> Prop)
  (maps_to_holds : static_env -> env -> W -> maps_to -> Prop).

Local Abbreviation a_case :=
  (row_like_case lattice shape maps_to env_extension).

Definition variables_of_case (c : a_case) : list variable :=
  variables_of_maps_to (case_maps_to c)
  ++ free_variables_of_env_extension (case_env_extension c).

Definition aliases_of_case (c : a_case) : list (simple * flambda_kind) :=
  aliases_of_maps_to (case_maps_to c)
  ++ aliases_of_env_extension (case_env_extension c).

Definition case_holds (statics : static_env) (vars : env) (w : W) (c : a_case)
    : Prop :=
  index_holds w (case_index c)
  ∧ maps_to_holds statics vars w (case_maps_to c)
  ∧ env_extension_satisfied statics vars (case_env_extension c).

Hypothesis Hindex :
  ∀ (indexes : list (row_like_index lattice shape))
    (index : row_like_index lattice shape),
    n_way_join_index equal_index inter_index n_way_join_shape indexes
    = Ok index ->
    ∀ i : row_like_index lattice shape,
      In i indexes -> ∀ w : W, index_holds w i -> index_holds w index.
Hypothesis Hindex_bottom :
  ∀ indexes : list (row_like_index lattice shape),
    n_way_join_index equal_index inter_index n_way_join_shape indexes
    = Bottom ->
    indexes = [].
Hypothesis Hmaps_to :
  ∀ index : row_like_index lattice shape,
    step_sound variables_of_maps_to aliases_of_maps_to variables_of_maps_to
      aliases_of_maps_to
      (fun statics valuation x valuation' y =>
         ∀ w : W,
           index_holds w index ->
           maps_to_holds statics valuation w x ->
           maps_to_holds statics valuation' w y)
      (fun s args => n_way_join_maps_to s (index_shape index) args).

Theorem n_way_join_case_is_sound :
  case_join_sound variables_of_case aliases_of_case
    (of_known variables_of_case) (of_known aliases_of_case)
    (known_bound (all_kept case_holds case_holds))
    (n_way_join_case join_env_n_way_join_env_extension n_way_join_maps_to
       equal_index inter_index n_way_join_shape).
Proof.
  intros s s1 cases result Hwf Hkinded Hgrows Hvalid Hdistinct Hargs Hjoin.
  unfold n_way_join_case in Hjoin.
  destruct
    (n_way_join_index equal_index inter_index n_way_join_shape
       (map (fun c => case_index (snd c)) cases))
    as [ | index | ] eqn:Hjoined.
  - injection Hjoin as <-.
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ auto | ].
    intros s' Hgrows'. split; [ intros x [] | ].
    split; [ intros; exact I | intros _ simple kind [] ].
  - set (maps_tos := map (fun c => (fst c, case_maps_to (snd c))) cases)
      in Hjoin.
    set (extensions :=
      map (fun c => (fst c, case_env_extension (snd c))) cases) in Hjoin.
    destruct (n_way_join_maps_to s1 (index_shape index) maps_tos)
      as [[joined_maps_to s2] | ] eqn:Hmaps; [ | discriminate ].
    cbn in Hjoin.
    destruct
      (n_way_join_env_extension join_env_n_way_join_env_extension s2
         extensions)
      as [[extension s3] | ] eqn:Hext; [ | discriminate ].
    cbn in Hjoin. injection Hjoin as <-.
    assert (Hdistinct1 : join_args_distinct maps_tos).
    { unfold join_args_distinct, maps_tos. rewrite map_map. exact Hdistinct. }
    assert (Hdistinct2 : join_args_distinct extensions).
    { unfold join_args_distinct, extensions. rewrite map_map.
      exact Hdistinct. }
    assert (Hargs1 :
      args_in_scope (arg_ok variables_of_maps_to aliases_of_maps_to) s
        maps_tos).
    { apply (args_of_parts _ _ _ _ s cases maps_tos Hargs). intros id m Hin.
      apply in_map_iff in Hin as ([id' c] & [= <- <-] & Hin).
      exists c. split; [ exact Hin | ]. split; apply incl_appl, incl_refl. }
    assert (Hargs2 :
      args_in_scope
        (arg_ok free_variables_of_env_extension aliases_of_env_extension) s
        extensions).
    { apply (args_of_parts _ _ _ _ s cases extensions Hargs).
      intros id m Hin.
      apply in_map_iff in Hin as ([id' c] & [= <- <-] & Hin).
      exists c. split; [ exact Hin | ]. split; apply incl_appr, incl_refl. }
    destruct
      (step_sound_at _ _ _ _ _ _ (Hmaps_to index) s s1 s2 maps_tos
         joined_maps_to Hwf Hkinded Hgrows Hvalid Hdistinct1 Hargs1 Hmaps)
      as (Hvalid2 & Hgrows2 & Hk2 & Hholds1).
    destruct
      (step_sound_at _ _ _ _ _ _
         (n_way_join_env_extension_is_sound join_env_n_way_join_env_extension
            Hextension)
         s s2 s3 extensions extension Hwf Hkinded
         (grows_trans _ _ _ Hgrows Hgrows2) Hvalid2 Hdistinct2 Hargs2 Hext)
      as (Hvalid3 & Hgrows3 & Hk3 & Hholds2).
    split; [ exact Hvalid3 | ].
    split; [ exact (grows_trans _ _ _ Hgrows2 Hgrows3) | ].
    split; [ auto | ].
    intros s' Hgrows'.
    destruct (Hholds1 s' (grows_trans _ _ _ Hgrows3 Hgrows'))
      as (Htarget1 & Hbound1 & Hkinds1).
    destruct (Hholds2 s' Hgrows') as (Htarget2 & Hbound2 & Hkinds2).
    split; [ | split ].
    + intros x Hx. cbn [of_known] in Hx. unfold variables_of_case in Hx.
      cbn [case_maps_to case_env_extension] in Hx.
      apply in_app_or in Hx as [Hx | Hx];
        [ exact (Htarget1 x Hx) | exact (Htarget2 x Hx) ].
    + intros id c use statics valuation valuation' Hin Huse Hsatisfied
        Hextends w (Hi & Hm & He).
      assert (Hi' : index_holds w index).
      { apply (Hindex _ index Hjoined (case_index c)); [ | exact Hi ].
        apply in_map_iff. exists (id, c). split; [ reflexivity | exact Hin ]. }
      split; [ exact Hi' | ]. cbn [case_maps_to case_env_extension].
      split.
      * apply
          (Hbound1 id (case_maps_to c) use statics valuation valuation');
          [ | exact Huse | exact Hsatisfied | exact Hextends | exact Hi'
          | exact Hm ].
        apply in_map_iff. exists (id, c). split; [ reflexivity | exact Hin ].
      * apply
          (Hbound2 id (case_env_extension c) use statics valuation
             valuation');
          [ | exact Huse | exact Hsatisfied | exact Hextends | exact He ].
        apply in_map_iff. exists (id, c). split; [ reflexivity | exact Hin ].
    + intros Hk simple kind Hsimple. cbn [of_known] in Hsimple.
      unfold aliases_of_case in Hsimple.
      cbn [case_maps_to case_env_extension] in Hsimple.
      apply in_app_or in Hsimple as [Hsimple | Hsimple];
        [ exact (Hkinds1 Hk simple kind Hsimple)
        | exact (Hkinds2 (Hk2 Hk) simple kind Hsimple) ].
  - injection Hjoin as <-. apply Hindex_bottom in Hjoined.
    exact (map_eq_nil _ _ Hjoined).
Qed.

Theorem n_way_join_knowns_is_sound :
  case_join_sound (of_known variables_of_case) (of_known aliases_of_case)
    (of_known variables_of_case) (of_known aliases_of_case)
    (or_unknown_bound (all_kept case_holds case_holds))
    (n_way_join_knowns join_env_n_way_join_env_extension n_way_join_maps_to
       equal_index inter_index n_way_join_shape).
Proof.
  intros s s1 cases result Hwf Hkinded Hgrows Hvalid Hdistinct Hargs Hjoin.
  unfold n_way_join_knowns in Hjoin. rewrite all_known_eq in Hjoin.
  destruct (indexed_map_opt _ cases) as [known | ] eqn:Hknown.
  - destruct (indexed_map_opt_spec _ _ known Hknown) as (Hfst & Hto & Hfrom).
    assert (Hdistinct' : join_args_distinct known).
    { unfold join_args_distinct. rewrite Hfst. exact Hdistinct. }
    assert (Hargs' :
      args_in_scope (arg_ok variables_of_case aliases_of_case) s known).
    { intros id c Hin. destruct (Hfrom id c Hin) as ([c' | ] & Heq & Hin');
        [ injection Heq as <- | discriminate ].
      exact (Hargs id (Or_unknown.Known c') Hin'). }
    pose proof
      (n_way_join_case_is_sound s s1 known result Hwf Hkinded Hgrows Hvalid
         Hdistinct' Hargs' Hjoin)
      as Hcase.
    destruct result as [[answer s2] | ].
    + destruct Hcase as (Hvalid2 & Hgrows2 & Hk2 & Hholds).
      split; [ exact Hvalid2 | ]. split; [ exact Hgrows2 | ].
      split; [ exact Hk2 | ].
      intros s' Hgrows'.
      destruct (Hholds s' Hgrows') as (Htarget & Hbound & Hkinds).
      split; [ exact Htarget | ]. split; [ | exact Hkinds ].
      intros id x use statics valuation valuation' Hin Huse Hsatisfied
        Hextends.
      destruct (Hto id x Hin) as (c & Hc & Hin').
      destruct x as [c' | ]; [ injection Hc as -> | discriminate ].
      specialize
        (Hbound id c use statics valuation valuation' Hin' Huse Hsatisfied
           Hextends).
      destruct answer; exact Hbound.
    + subst known. symmetry in Hfst. exact (map_eq_nil _ _ Hfst).
  - injection Hjoin as <-.
    split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
    split; [ auto | ].
    intros s' _. split; [ intros x [] | ].
    split; [ | intros _ simple kind [] ].
    intros id x use statics valuation valuation' _ _ _ _. destruct x; exact I.
Qed.

End Cases.

(* ------------------------------------------------------------------------ *)
(* Row-like structures of blocks                                            *)
(* ------------------------------------------------------------------------ *)

(* A block: its tag and its fields. *)
Definition tag_and_fields : Type := (Z * list value)%type.

Definition block_index_holds (w : tag_and_fields)
    (index : row_like_index nat block_shape) : Prop :=
  block_index_satisfied (fst w) (snd w) index.

Definition block_fields_hold (statics : static_env) (vars : env)
    (w : tag_and_fields) (tys : list flambda_type) : Prop :=
  fields_satisfied (type_satisfied statics vars) tys (snd w).

Definition blocks_hold (statics : static_env) (vars : env)
    (w : tag_and_fields) (blocks : row_like_for_blocks) : Prop :=
  row_like_for_blocks_satisfied statics vars (fst w) (snd w) blocks.

Local Abbreviation block_case_variables :=
  (variables_of_case (lattice := nat) (shape := block_shape)
     variables_of_fields).
Local Abbreviation block_case_aliases :=
  (aliases_of_case (lattice := nat) (shape := block_shape) aliases_of_fields).
Local Abbreviation block_case_holds :=
  (case_holds block_index_holds block_fields_hold).

Lemma block_shapes_sound (shapes : list block_shape) (joined : block_shape) :
  n_way_join_block_shape block_shape_eqb shapes = Ok joined ->
  ∀ shape' : block_shape, In shape' shapes -> shape' = joined.
Proof.
  destruct shapes as [ | shape1 rest]; [ discriminate | ]. simpl.
  destruct (forallb (block_shape_eqb shape1) rest) eqn:Hall;
    [ | discriminate ].
  intros [= <-] shape' [<- | Hin]; [ reflexivity | ].
  rewrite forallb_forall in Hall. symmetry.
  exact (Hshape _ _ (Hall shape' Hin)).
Qed.

Lemma block_index_sound (indexes : list (row_like_index nat block_shape))
    (index : row_like_index nat block_shape) :
  n_way_join_index Nat.eqb Nat.min (n_way_join_block_shape block_shape_eqb)
    indexes
  = Ok index ->
  ∀ i : row_like_index nat block_shape,
    In i indexes ->
    ∀ w : tag_and_fields, block_index_holds w i -> block_index_holds w index.
Proof.
  intros Hjoined i Hin w [Hdomain Hshape'].
  refine
    (n_way_join_index_sound Nat.eqb Nat.min
       (n_way_join_block_shape block_shape_eqb)
       (fun (w : tag_and_fields) size => length (snd w) = size)
       (fun (w : tag_and_fields) size => size <= length (snd w))
       (fun (w : tag_and_fields) shape =>
          block_has_shape shape (fst w) (snd w))
       _ _ _ _ _ indexes index Hjoined i Hin w Hdomain Hshape').
  - intros w' l <-. apply Nat.le_refl.
  - intros w' l l' Heq Hl. apply Nat.eqb_eq in Heq. congruence.
  - intros w' l l' Hl. exact (Nat.le_trans _ _ _ (Nat.le_min_l l l') Hl).
  - intros w' l l' Hl. exact (Nat.le_trans _ _ _ (Nat.le_min_r l l') Hl).
  - intros shapes joined Hshapes shape' Hin' w' Hholds.
    rewrite <- (block_shapes_sound shapes joined Hshapes shape' Hin').
    exact Hholds.
Qed.

Lemma block_index_bottom (indexes : list (row_like_index nat block_shape)) :
  n_way_join_index Nat.eqb Nat.min (n_way_join_block_shape block_shape_eqb)
    indexes
  = Bottom ->
  indexes = [].
Proof.
  apply n_way_join_index_bottom. intros [ | shape1 rest]; [ reflexivity | ].
  simpl. destruct (forallb (block_shape_eqb shape1) rest); discriminate.
Qed.

Lemma block_fields_sound (index : row_like_index nat block_shape) :
  step_sound variables_of_fields aliases_of_fields variables_of_fields
    aliases_of_fields
    (fun statics valuation x valuation' y =>
       ∀ w : tag_and_fields,
         block_index_holds w index ->
         block_fields_hold statics valuation w x ->
         block_fields_hold statics valuation' w y)
    (fun s args =>
       n_way_join_int_indexed_product import_type type_eqb n_way_join_rec s
         (index_shape index) args).
Proof.
  apply (step_sound_bound _ _ _ _ (fields_bound (index_shape index)));
    [ | apply n_way_join_int_indexed_product_is_sound ].
  intros statics valuation x valuation' y Hbound w [_ Hshape'] Hfields.
  exact (Hbound (fst w) (snd w) Hshape' Hfields).
Qed.

(* The cases of a row-like structure of blocks that is in scope and
   kinded are. *)
Lemma blocks_parts_in_scope (use : Typing_env.t)
    (blocks : row_like_for_blocks) :
  arg_ok free_variables_of_row_like_for_blocks aliases_of_row_like_for_blocks
    use blocks ->
  (∀ (key : Z) (v : Or_unknown.t row_like_block_case),
     Keyed.lookup Z.eqb key (row_like_known_tags blocks) = Some v ->
     arg_ok (of_known block_case_variables) (of_known block_case_aliases) use
       v)
  ∧ ∀ o : row_like_block_case,
      row_like_other_tags blocks = Or_bottom.Ok o ->
      arg_ok block_case_variables block_case_aliases use o.
Proof.
  destruct blocks as [known_tags other_tags alloc_mode].
  intros [Hvariables Haliases]. simpl in *. split.
  - intros key v Hv.
    apply (keyed_lookup_in Z.eqb z_eqb_decides_equality) in Hv.
    split.
    + intros y Hy. apply Hvariables. apply in_or_app. left.
      apply in_flat_map. exists (key, v). split; [ exact Hv | ].
      destruct v; exact Hy.
    + intros simple kind Hsimple. apply Haliases. apply in_or_app. left.
      apply in_flat_map. exists (key, v). split; [ exact Hv | ].
      destruct v; exact Hsimple.
  - intros o ->. split.
    + intros y Hy. apply Hvariables. apply in_or_app. right. exact Hy.
    + intros simple kind Hsimple. apply Haliases. apply in_or_app. right.
      exact Hsimple.
Qed.

(* The row-like structures that are not bottom, as the fold of
   [n_way_join_row_like_for_blocks] splits them. *)
Definition non_bottom_blocks (row_likes : list (Index.t * row_like_for_blocks))
    : list (Index.t * row_like_for_blocks) :=
  filter
    (fun row_like => negb (row_like_for_blocks_is_bottom (snd row_like)))
    row_likes.

Definition known_of_blocks (row_like : Index.t * row_like_for_blocks)
    : Index.t
      * (Keyed.finite_map Z (Or_unknown.t row_like_block_case)
         * Or_bottom.t row_like_block_case) :=
  (fst row_like,
   (row_like_known_tags (snd row_like), row_like_other_tags (snd row_like))).

Definition other_of_blocks (row_like : Index.t * row_like_for_blocks)
    : Index.t * Or_bottom.t row_like_block_case :=
  (fst row_like, row_like_other_tags (snd row_like)).

Local Abbreviation split_of_blocks :=
  (Or_bottom.t
     (list
        (Index.t
         * (Keyed.finite_map Z (Or_unknown.t row_like_block_case)
            * Or_bottom.t row_like_block_case))
      * list (Index.t * Or_bottom.t row_like_block_case)
      * Alloc_mode.t)).

Definition split_step (acc : split_of_blocks)
    (row_like : Index.t * row_like_for_blocks) : split_of_blocks :=
  if row_like_for_blocks_is_bottom (snd row_like)
  then acc
  else
    match acc with
    | Or_bottom.Bottom =>
      Or_bottom.Ok
        ([known_of_blocks row_like], [other_of_blocks row_like],
         row_like_alloc_mode (snd row_like))
    | Or_bottom.Ok (known, other, alloc_mode) =>
      Or_bottom.Ok
        (known_of_blocks row_like :: known, other_of_blocks row_like :: other,
         join_alloc_mode alloc_mode (row_like_alloc_mode (snd row_like)))
    end.

Definition split_is (kept : list (Index.t * row_like_for_blocks))
    (acc : split_of_blocks) : Prop :=
  match acc with
  | Or_bottom.Bottom => kept = []
  | Or_bottom.Ok (known, other, _) =>
    kept <> []
    ∧ known = rev (map known_of_blocks kept)
    ∧ other = rev (map other_of_blocks kept)
  end.

Lemma split_fold (row_likes : list (Index.t * row_like_for_blocks)) :
  ∀ (kept : list (Index.t * row_like_for_blocks)) (acc : split_of_blocks),
    split_is kept acc ->
    split_is (kept ++ non_bottom_blocks row_likes)
      (List.fold_left split_step row_likes acc).
Proof.
  induction row_likes as [ | row_like row_likes IH]; intros kept acc Hacc.
  - simpl. rewrite app_nil_r. exact Hacc.
  - cbn [List.fold_left].
    assert (Hnext :
      split_is (kept ++ non_bottom_blocks [row_like])
        (split_step acc row_like)).
    { unfold non_bottom_blocks, split_step. cbn [filter].
      destruct (row_like_for_blocks_is_bottom (snd row_like)); cbn [negb].
      - rewrite app_nil_r. exact Hacc.
      - destruct acc as [[[known other] alloc_mode] | ]; simpl in Hacc |- *.
        + destruct Hacc as (Hne & -> & ->).
          split; [ intros Hnil; apply app_eq_nil in Hnil as [_ [=]] | ].
          rewrite !map_app, !rev_app_distr. split; reflexivity.
        + subst kept. split; [ discriminate | split; reflexivity ]. }
    specialize (IH _ _ Hnext).
    replace (kept ++ non_bottom_blocks (row_like :: row_likes))
      with ((kept ++ non_bottom_blocks [row_like])
            ++ non_bottom_blocks row_likes);
      [ exact IH | ].
    rewrite <- app_assoc. f_equal. unfold non_bottom_blocks. cbn [filter].
    destruct (negb _); reflexivity.
Qed.

Theorem n_way_join_row_like_for_blocks_is_sound :
  step_sound free_variables_of_row_like_for_blocks
    aliases_of_row_like_for_blocks
    (of_known free_variables_of_row_like_for_blocks)
    (of_known aliases_of_row_like_for_blocks)
    (known_bound (all_kept blocks_hold blocks_hold))
    (n_way_join_row_like_for_blocks import_type
       join_env_n_way_join_env_extension type_eqb block_shape_eqb
       n_way_join_rec).
Proof.
  intros s s' row_likes answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_row_like_for_blocks in Hstep.
  set (split := List.fold_left _ row_likes Or_bottom.Bottom) in Hstep.
  assert (Hsplit : split_is (non_bottom_blocks row_likes) split)
    by exact (split_fold row_likes [] Or_bottom.Bottom eq_refl).
  assert (Hkept :
    ∀ (index : Index.t) (blocks : row_like_for_blocks),
      In (index, blocks) (non_bottom_blocks row_likes)
      <-> In (index, blocks) row_likes
          ∧ row_like_for_blocks_is_bottom blocks = false).
  { intros index blocks. unfold non_bottom_blocks. rewrite filter_In.
    cbn [snd]. rewrite negb_true_iff. reflexivity. }
  cbv zeta in Hstep.
  destruct split as [[[known other] alloc_mode] | ]; cbn [split_is] in Hsplit.
  2: { injection Hstep as <- <-.
       split; [ exact Hvalid | ]. split; [ apply grows_refl | ].
       split; [ intros x [] | ].
       split.
       - intros index blocks use statics valuation valuation' Hin _ _ _ w Hw.
         exfalso.
         destruct (row_like_for_blocks_is_bottom blocks) eqn:Hb.
         + exact
             (row_like_for_blocks_is_bottom_satisfied statics valuation
                (fst w) (snd w) blocks Hb Hw).
         + assert (Hin' : In (index, blocks) (non_bottom_blocks row_likes))
             by (apply Hkept; split; assumption).
           rewrite Hsplit in Hin'. destruct Hin'.
       - intros Hk. split; [ exact Hk | intros simple kind [] ]. }
  destruct Hsplit as (Hne & -> & ->).
  set (kept := non_bottom_blocks row_likes) in *.
  set (knowns := rev (map known_of_blocks kept)) in *.
  set (others := rev (map other_of_blocks kept)) in *.
  assert (Hkept_distinct : NoDup (map fst kept))
    by (apply filter_indexed_distinct; exact Hdistinct).
  assert (Hknowns_distinct : join_args_distinct knowns).
  { unfold join_args_distinct, knowns. rewrite map_rev, map_map.
    apply NoDup_rev. exact Hkept_distinct. }
  assert (Hothers_distinct : NoDup (map fst others)).
  { unfold others. rewrite map_rev, map_map. apply NoDup_rev.
    exact Hkept_distinct. }
  assert (Hin_knowns :
    ∀ (index : Index.t)
      (known_tags : Keyed.finite_map Z (Or_unknown.t row_like_block_case))
      (other_tags : Or_bottom.t row_like_block_case) (mode : Alloc_mode.t),
      In (index, Row_like_for_blocks known_tags other_tags mode) kept ->
      In (index, (known_tags, other_tags)) knowns).
  { intros index known_tags other_tags mode Hin. unfold knowns.
    rewrite <- in_rev. apply in_map_iff.
    exists (index, Row_like_for_blocks known_tags other_tags mode).
    split; [ reflexivity | exact Hin ]. }
  assert (Hin_others :
    ∀ (index : Index.t)
      (known_tags : Keyed.finite_map Z (Or_unknown.t row_like_block_case))
      (other_tags : Or_bottom.t row_like_block_case) (mode : Alloc_mode.t),
      In (index, Row_like_for_blocks known_tags other_tags mode) kept ->
      In (index, other_tags) others).
  { intros index known_tags other_tags mode Hin. unfold others.
    rewrite <- in_rev. apply in_map_iff.
    exists (index, Row_like_for_blocks known_tags other_tags mode).
    split; [ reflexivity | exact Hin ]. }
  assert (Hargs_knowns :
    args_in_scope
      (known_in_scope Z.eqb Or_unknown.Known (of_known block_case_variables)
         (of_known block_case_aliases))
      s knowns).
  { intros index m Hin. unfold knowns in Hin. rewrite <- in_rev in Hin.
    apply in_map_iff in Hin as ([index' blocks] & [= <- <-] & Hin).
    apply Hkept in Hin as [Hin _].
    destruct (Hargs index' blocks Hin) as (use & Huse & Hok).
    exists use. split; [ exact Huse | ].
    destruct (blocks_parts_in_scope use blocks Hok) as [Hknown Hother].
    split; [ exact Hknown | ]. intros o Ho. exact (Hother o Ho). }
  assert (Hargs_others :
    args_in_scope (arg_ok block_case_variables block_case_aliases) s
      (non_bottom [] others)).
  { intros index o Hin.
    apply (proj2 (non_bottom_spec others Hothers_distinct)) in Hin.
    unfold others in Hin. rewrite <- in_rev in Hin.
    apply in_map_iff in Hin as ([index' blocks] & [= <- Ho] & Hin).
    apply Hkept in Hin as [Hin _].
    destruct (Hargs index' blocks Hin) as (use & Huse & Hok).
    exists use. split; [ exact Huse | ].
    exact (proj2 (blocks_parts_in_scope use blocks Hok) o Ho). }
  pose proof
    (n_way_join_knowns_is_sound
       (n_way_join_int_indexed_product import_type type_eqb n_way_join_rec)
       Nat.eqb Nat.min (n_way_join_block_shape block_shape_eqb)
       variables_of_fields aliases_of_fields block_index_holds
       block_fields_hold block_index_sound block_index_bottom
       block_fields_sound)
    as Hknowns_sound.
  pose proof
    (n_way_join_case_is_sound
       (n_way_join_int_indexed_product import_type type_eqb n_way_join_rec)
       Nat.eqb Nat.min (n_way_join_block_shape block_shape_eqb)
       variables_of_fields aliases_of_fields block_index_holds
       block_fields_hold block_index_sound block_index_bottom
       block_fields_sound)
    as Hcase_sound.
  unfold map_join_result, n_way_join_row_like in Hstep.
  destruct
    (generic_merge_map_known Z.eqb Or_unknown.Known
       (n_way_join_knowns join_env_n_way_join_env_extension
          (n_way_join_int_indexed_product import_type type_eqb n_way_join_rec)
          Nat.eqb Nat.min (n_way_join_block_shape block_shape_eqb))
       s knowns)
    as [[known' sa] | ] eqn:Hmerge; [ | discriminate ].
  cbv beta iota in Hstep.
  destruct
    (generic_merge_map_known_is_sound Z.eqb z_eqb_decides_equality
       Or_unknown.Known (of_known block_case_variables)
       (of_known block_case_aliases)
       (or_unknown_bound (all_kept block_case_holds block_case_holds)) _
       Hknowns_sound s s sa knowns known' Hwf Hkinded (grows_refl s) Hvalid
       Hknowns_distinct Hargs_knowns Hmerge)
    as (Hvalida & Hgrowsa & Hka & Hin_known & Hfound & Hnone).
  assert (Hfinal :
    ∀ (other' : Or_bottom.t row_like_block_case) (sb : state),
      state_valid sb -> grows sa sb ->
      (state_kinded sa -> state_kinded sb) ->
      match other' with
      | Or_bottom.Ok c =>
        answer_holds_from (of_known block_case_variables)
          (of_known block_case_aliases)
          (known_bound (all_kept block_case_holds block_case_holds)) sa sb
          (non_bottom [] others) (Or_unknown.Known c)
      | Or_bottom.Bottom => non_bottom [] others = []
      end ->
      state_valid sb ∧ grows s sb
      ∧ in_target (of_known free_variables_of_row_like_for_blocks) sb
          (Or_unknown.Known (Row_like_for_blocks known' other' alloc_mode))
      ∧ (∀ (index : Index.t) (x : row_like_for_blocks) (use : Typing_env.t)
           (statics : static_env) (valuation valuation' : env),
           In (index, x) row_likes ->
           joined_env sb index = Some use ->
           typing_env_satisfied_strictly statics valuation use ->
           extends sb index valuation valuation' ->
           known_bound (all_kept blocks_hold blocks_hold) statics valuation x
             valuation'
             (Or_unknown.Known (Row_like_for_blocks known' other' alloc_mode)))
      ∧ (state_kinded s ->
         state_kinded sb
         ∧ kinded_in_target (of_known aliases_of_row_like_for_blocks) sb
             (Or_unknown.Known
                (Row_like_for_blocks known' other' alloc_mode)))).
  { intros other' sb Hvalidb Hgrowsb Hkb Hother'.
    split; [ exact Hvalidb | ].
    split; [ exact (grows_trans _ _ _ Hgrowsa Hgrowsb) | ].
    split; [ | split ].
    - intros x Hx. cbn [of_known] in Hx. simpl in Hx.
      apply in_app_or in Hx as [Hx | Hx].
      + apply in_flat_map in Hx as ([key y] & Hin & Hx). cbn [snd] in Hx.
        destruct (Hfound key y (Hin_known key y Hin)) as (vals & _ & Hholds).
        destruct (Hholds sb Hgrowsb) as (Htarget & _ & _). apply Htarget.
        destruct y; exact Hx.
      + destruct other' as [c | ]; [ | destruct Hx ].
        destruct (Hother' sb (grows_refl sb)) as (Htarget & _ & _).
        exact (Htarget x Hx).
    - intros index [known_tags other_tags mode] use statics valuation
        valuation' Hin Huse Hsatisfied Hextends w Hw.
      unfold blocks_hold in *.
      assert (Hin_kept :
        In (index, Row_like_for_blocks known_tags other_tags mode) kept).
      { apply Hkept. split; [ exact Hin | ].
        destruct (row_like_for_blocks_is_bottom _) eqn:Hb; [ | reflexivity ].
        destruct
          (row_like_for_blocks_is_bottom_satisfied statics valuation (fst w)
             (snd w) _ Hb Hw). }
      apply row_like_for_blocks_find_iff in Hw.
      apply row_like_for_blocks_find_iff. unfold row_like_block_case in *.
      destruct (Keyed.lookup Z.eqb (fst w) known') as [y | ] eqn:Hy.
      + destruct (Hfound _ y Hy) as (vals & Hvals & Hholds).
        destruct (Hholds sb Hgrowsb) as (_ & Hbound & _).
        destruct
          (gather_known_spec Z.eqb z_eqb_decides_equality Or_unknown.Known
             knowns (fst w) vals Hknowns_distinct Hvals)
          as (_ & _ & Hto & _).
        destruct
          (Hto (index, (known_tags, other_tags))
             (Hin_knowns _ _ _ _ Hin_kept))
          as (Hsome & Hnone'). cbn [fst snd] in Hsome, Hnone'.
        destruct y as [c' | ]; [ | exact I ].
        destruct (Keyed.lookup Z.eqb (fst w) known_tags) as [v | ] eqn:Hv.
        * specialize
            (Hbound index v use statics valuation valuation' (Hsome v eq_refl)
               Huse Hsatisfied Hextends).
          destruct v as [c | ]; [ exact (Hbound w Hw) | destruct Hbound ].
        * destruct other_tags as [o | ]; [ | destruct Hw ].
          exact
            (Hbound index (Or_unknown.Known o) use statics valuation
               valuation' (Hnone' eq_refl o eq_refl) Huse Hsatisfied Hextends w
               Hw).
      + pose proof
          (gather_known_none Z.eqb z_eqb_decides_equality Or_unknown.Known
             knowns (fst w) (Hnone _ Hy) (index, (known_tags, other_tags))
             (Hin_knowns _ _ _ _ Hin_kept))
          as Hv.
        cbn [fst snd] in Hv. rewrite Hv in Hw.
        destruct other_tags as [o | ]; [ | destruct Hw ].
        assert (Hin_other : In (index, o) (non_bottom [] others)).
        { apply (proj2 (non_bottom_spec others Hothers_distinct)).
          exact (Hin_others _ _ _ _ Hin_kept). }
        destruct other' as [c | ].
        * destruct (Hother' sb (grows_refl sb)) as (_ & Hbound & _).
          exact
            (Hbound index o use statics valuation valuation' Hin_other Huse
               Hsatisfied Hextends w Hw).
        * rewrite Hother' in Hin_other. destruct Hin_other.
    - intros Hk. split; [ exact (Hkb (Hka Hk)) | ].
      intros simple kind Hsimple. cbn [of_known] in Hsimple.
      simpl in Hsimple. apply in_app_or in Hsimple as [Hsimple | Hsimple].
      + apply in_flat_map in Hsimple as ([key y] & Hin & Hsimple).
        cbn [snd] in Hsimple.
        destruct (Hfound key y (Hin_known key y Hin)) as (vals & _ & Hholds).
        destruct (Hholds sb Hgrowsb) as (_ & _ & Hkinds). apply (Hkinds Hk).
        destruct y; exact Hsimple.
      + destruct other' as [c | ]; [ | destruct Hsimple ].
        destruct (Hother' sb (grows_refl sb)) as (_ & _ & Hkinds).
        exact (Hkinds (Hka Hk) simple kind Hsimple). }
  match type of Hstep with
  | context [n_way_join_case ?a ?b ?c ?d ?e sa ?l] =>
    destruct (n_way_join_case a b c d e sa l) as [result | ] eqn:Hother;
      [ | discriminate ]
  end.
  pose proof
    (Hcase_sound s sa (non_bottom [] others) result Hwf Hkinded Hgrowsa
       Hvalida (proj1 (non_bottom_spec others Hothers_distinct)) Hargs_others
       Hother)
    as Hresult.
  destruct result as [[[c | ] sb] | ]; cbv beta iota in Hstep;
    unfold or_unknown_map in Hstep; cbn [fst snd] in Hstep.
  all: injection Hstep as <- <-.
  - destruct Hresult as (Hvalidb & Hgrowsb & Hkb & Hholds).
    exact (Hfinal (Or_bottom.Ok c) sb Hvalidb Hgrowsb Hkb Hholds).
  - destruct Hresult as (Hvalidb & Hgrowsb & Hkb & _).
    split; [ exact Hvalidb | ].
    split; [ exact (grows_trans _ _ _ Hgrowsa Hgrowsb) | ].
    split; [ intros x [] | ]. split; [ intros; exact I | ].
    intros Hk. split; [ exact (Hkb (Hka Hk)) | intros simple kind [] ].
  - exact
      (Hfinal Or_bottom.Bottom sa Hvalida (grows_refl sa) (fun H => H)
         Hresult).
Qed.

(* ------------------------------------------------------------------------ *)
(* Row-like structures of closures                                          *)
(* ------------------------------------------------------------------------ *)

Definition closures_index_holds (w : closure_and_set)
    (index : row_like_index set_of_closures_contents unit) : Prop :=
  closures_index_satisfied (snd (fst w)) (snd w) index.

Definition closures_hold (statics : static_env) (vars : env)
    (w : closure_and_set) (closures : row_like_for_closures) : Prop :=
  let '(v, slot, functions, value_slots) := w in
  row_like_for_closures_satisfied statics vars v slot functions value_slots
    closures.

Local Abbreviation closures_case_variables :=
  (variables_of_case (lattice := set_of_closures_contents) (shape := unit)
     free_variables_of_closures_entry).
Local Abbreviation closures_case_aliases :=
  (aliases_of_case (lattice := set_of_closures_contents) (shape := unit)
     aliases_of_closures_entry).
Local Abbreviation closures_case_holds :=
  (case_holds closures_index_holds closures_entry_holds).

Lemma closures_index_sound
    (indexes : list (row_like_index set_of_closures_contents unit))
    (index : row_like_index set_of_closures_contents unit) :
  n_way_join_index set_of_closures_contents_equal
    set_of_closures_contents_inter (fun _ => Ok tt) indexes
  = Ok index ->
  ∀ i : row_like_index set_of_closures_contents unit,
    In i indexes ->
    ∀ w : closure_and_set,
      closures_index_holds w i -> closures_index_holds w index.
Proof.
  intros Hjoined i Hin w Hdomain.
  refine
    (proj1
       (n_way_join_index_sound set_of_closures_contents_equal
          set_of_closures_contents_inter (fun _ => Ok tt)
          (fun (w : closure_and_set) contents =>
             same_names (contents_closures contents) (domain (snd (fst w)))
             ∧ same_names (contents_value_slots contents) (domain (snd w)))
          (fun (w : closure_and_set) contents =>
             FlambdaMapSpec.all_among (contents_closures contents)
               (domain (snd (fst w)))
             = true
             ∧ FlambdaMapSpec.all_among (contents_value_slots contents)
                 (domain (snd w))
               = true)
          (fun _ _ => True) _ _ _ _ _ indexes index Hjoined i Hin w Hdomain I)).
  - intros w' l [Hc Hv].
    split; apply all_among; intros name Hname;
      [ rewrite <- Hc | rewrite <- Hv ]; exact Hname.
  - intros w' l l' Heq [Hc Hv]. unfold set_of_closures_contents_equal in Heq.
    apply andb_true_iff in Heq as [Heqc Heqv].
    apply (keyed_same_keys_b positive Pos.eqb pos_eqb_decides_equality)
      in Heqc, Heqv.
    split; intros name;
      [ rewrite <- (Hc name); exact (Heqc name)
      | rewrite <- (Hv name); exact (Heqv name) ].
  - intros w' l l' [Hc Hv].
    split; apply all_among; intros name Hname; simpl in Hname;
      rewrite (keyed_among_inter positive Pos.eqb pos_eqb_decides_equality)
        in Hname;
      apply andb_true_iff in Hname as [Hname _];
      [ exact (proj1 (all_among _ _) Hc name Hname)
      | exact (proj1 (all_among _ _) Hv name Hname) ].
  - intros w' l l' [Hc Hv].
    split; apply all_among; intros name Hname; simpl in Hname;
      rewrite (keyed_among_inter positive Pos.eqb pos_eqb_decides_equality)
        in Hname;
      apply andb_true_iff in Hname as [_ Hname];
      [ exact (proj1 (all_among _ _) Hc name Hname)
      | exact (proj1 (all_among _ _) Hv name Hname) ].
  - intros; exact I.
Qed.

Lemma closures_index_bottom
    (indexes : list (row_like_index set_of_closures_contents unit)) :
  n_way_join_index set_of_closures_contents_equal
    set_of_closures_contents_inter (fun _ => Ok tt) indexes
  = Bottom ->
  indexes = [].
Proof. apply n_way_join_index_bottom. intros shapes [=]. Qed.

Lemma closures_entries_sound
    (index : row_like_index set_of_closures_contents unit) :
  step_sound free_variables_of_closures_entry aliases_of_closures_entry
    free_variables_of_closures_entry aliases_of_closures_entry
    (fun statics valuation x valuation' y =>
       ∀ w : closure_and_set,
         closures_index_holds w index ->
         closures_entry_holds statics valuation w x ->
         closures_entry_holds statics valuation' w y)
    (fun s args =>
       (fun env (_ : unit) entries =>
          n_way_join_closures_entry n_way_join_rec env entries)
         s (index_shape index) args).
Proof.
  apply
    (step_sound_bound _ _ _ _
       (all_kept closures_entry_holds closures_entry_holds));
    [ | exact n_way_join_closures_entry_is_sound ].
  intros statics valuation x valuation' y Hbound w _ Hentry.
  exact (Hbound w Hentry).
Qed.

Theorem n_way_join_row_like_for_closures_is_sound :
  step_sound free_variables_of_row_like_for_closures
    aliases_of_row_like_for_closures free_variables_of_row_like_for_closures
    aliases_of_row_like_for_closures (all_kept closures_hold closures_hold)
    (n_way_join_row_like_for_closures join_env_n_way_join_env_extension
       n_way_join_rec).
Proof.
  intros s s' closures answer Hvalid Hwf Hkinded Hdistinct Hargs Hstep.
  unfold n_way_join_row_like_for_closures in Hstep.
  set (knowns :=
    rev
      (map
         (fun closures =>
            (fst closures,
             (row_like_known_closures (snd closures),
              @Or_bottom.Bottom row_like_closures_case)))
         closures)) in Hstep.
  unfold n_way_join_row_like in Hstep.
  pose proof
    (n_way_join_knowns_is_sound
       (fun env (_ : unit) entries =>
          n_way_join_closures_entry n_way_join_rec env entries)
       set_of_closures_contents_equal set_of_closures_contents_inter
       (fun _ => Ok tt) free_variables_of_closures_entry
       aliases_of_closures_entry closures_index_holds closures_entry_holds
       closures_index_sound closures_index_bottom closures_entries_sound)
    as Hknowns_sound.
  match type of Hstep with
  | context [generic_merge_map_known ?eqb ?of_other ?j s knowns] =>
    set (join := j) in Hstep;
    destruct (generic_merge_map_known eqb of_other join s knowns)
      as [[known' sa] | ] eqn:Hmerge; [ | discriminate ]
  end.
  assert (Hjoin_sound :
    case_join_sound closures_case_variables closures_case_aliases
      closures_case_variables closures_case_aliases
      (all_kept closures_case_holds closures_case_holds) join).
  { intros s0 s1 cases result Hwf0 Hkinded0 Hgrows0 Hvalid0 Hdistinct0 Hargs0
      Hjoin.
    unfold join in Hjoin. cbv beta zeta in Hjoin.
    match type of Hjoin with
    | context [n_way_join_knowns ?a ?b ?c ?d ?e s1 ?l] =>
      set (knowns' := l) in Hjoin;
      destruct (n_way_join_knowns a b c d e s1 knowns') as [joined | ]
        eqn:Hknowns; [ | discriminate ]
    end.
    assert (Hdistinct' : join_args_distinct knowns').
    { unfold join_args_distinct, knowns'. rewrite map_map. exact Hdistinct0. }
    assert (Hargs' :
      args_in_scope
        (arg_ok (of_known closures_case_variables)
           (of_known closures_case_aliases))
        s0 knowns').
    { intros id x Hin.
      apply in_map_iff in Hin as ([id' c] & [= <- <-] & Hin).
      exact (Hargs0 id' c Hin). }
    pose proof
      (Hknowns_sound s0 s1 knowns' joined Hwf0 Hkinded0 Hgrows0 Hvalid0
         Hdistinct' Hargs' Hknowns)
      as Hresult.
    destruct joined as [[[c | ] s2] | ]; cbv beta iota in Hjoin;
      [ injection Hjoin as <- | discriminate | injection Hjoin as <- ].
    - destruct Hresult as (Hvalid2 & Hgrows2 & Hk2 & Hholds).
      split; [ exact Hvalid2 | ]. split; [ exact Hgrows2 | ].
      split; [ exact Hk2 | ].
      intros s'' Hgrows''.
      destruct (Hholds s'' Hgrows'') as (Htarget & Hbound & Hkinds).
      split; [ exact Htarget | ]. split; [ | exact Hkinds ].
      intros id c0 use statics valuation valuation' Hin Huse Hsatisfied
        Hextends.
      exact
        (Hbound id (Or_unknown.Known c0) use statics valuation valuation'
           (in_map (fun case => (fst case, Or_unknown.Known (snd case))) cases
              (id, c0) Hin)
           Huse Hsatisfied Hextends).
    - exact (map_eq_nil _ _ Hresult). }
  cbv beta iota delta [n_way_join_case n_way_join_index non_bottom map]
    in Hstep.
  injection Hstep as <- <-.
  assert (Hknowns_distinct : join_args_distinct knowns).
  { unfold join_args_distinct, knowns. rewrite map_rev, map_map.
    apply NoDup_rev. exact Hdistinct. }
  assert (Hin_knowns :
    ∀ (index : Index.t)
      (known_closures : finite_map row_like_closures_case),
      In (index, Row_like_for_closures known_closures) closures ->
      In (index, (known_closures, Or_bottom.Bottom)) knowns).
  { intros index known_closures Hin. unfold knowns. rewrite <- in_rev.
    apply in_map_iff. exists (index, Row_like_for_closures known_closures).
    split; [ reflexivity | exact Hin ]. }
  assert (Hargs_knowns :
    args_in_scope
      (known_in_scope Pos.eqb (fun case : row_like_closures_case => case)
         closures_case_variables closures_case_aliases)
      s knowns).
  { intros index m Hin. unfold knowns in Hin. rewrite <- in_rev in Hin.
    apply in_map_iff in Hin as ([index' [known_closures]] & [= <- <-] & Hin).
    destruct (Hargs index' _ Hin) as (use & Huse & Hvariables & Haliases).
    exists use. split; [ exact Huse | ].
    split; [ | intros o [=] ].
    intros key c Hc. cbn [fst snd row_like_known_closures] in Hc.
    apply (keyed_lookup_in Pos.eqb pos_eqb_decides_equality) in Hc.
    split.
    - intros y Hy. apply Hvariables. simpl. apply in_flat_map.
      exists (key, c). split; [ exact Hc | exact Hy ].
    - intros simple kind Hsimple. apply Haliases. simpl. apply in_flat_map.
      exists (key, c). split; [ exact Hc | exact Hsimple ]. }
  destruct
    (generic_merge_map_known_is_sound Pos.eqb pos_eqb_decides_equality
       (fun case : row_like_closures_case => case) closures_case_variables
       closures_case_aliases
       (all_kept closures_case_holds closures_case_holds) join Hjoin_sound s s
       sa knowns known' Hwf Hkinded (grows_refl s) Hvalid Hknowns_distinct
       Hargs_knowns Hmerge)
    as (Hvalida & Hgrowsa & Hka & Hin_known & Hfound & Hnone).
  split; [ exact Hvalida | ]. split; [ exact Hgrowsa | ].
  split; [ | split ].
  - intros x Hx. simpl in Hx.
    apply in_flat_map in Hx as ([key y] & Hin & Hx). cbn [snd] in Hx.
    destruct (Hfound key y (Hin_known key y Hin)) as (vals & _ & Hholds).
    destruct (Hholds sa (grows_refl sa)) as (Htarget & _ & _).
    exact (Htarget x Hx).
  - intros index [known_closures] use statics valuation valuation' Hin Huse
      Hsatisfied Hextends [[[v slot] functions] value_slots] Hw.
    unfold closures_hold in *.
    apply row_like_for_closures_lookup_iff in Hw as (c & Hc & Hsatisfied_c).
    apply row_like_for_closures_lookup_iff.
    destruct (Keyed.lookup Pos.eqb slot known') as [y | ] eqn:Hy.
    + exists y. split; [ exact Hy | ].
      destruct (Hfound slot y Hy) as (vals & Hvals & Hholds).
      destruct (Hholds sa (grows_refl sa)) as (_ & Hbound & _).
      destruct
        (gather_known_spec Pos.eqb pos_eqb_decides_equality
           (fun case : row_like_closures_case => case) knowns slot vals
           Hknowns_distinct Hvals)
        as (_ & _ & Hto & _).
      destruct
        (Hto (index, (known_closures, Or_bottom.Bottom))
           (Hin_knowns _ _ Hin))
        as (Hsome & _). cbn [fst snd] in Hsome.
      exact
        (Hbound index c use statics valuation valuation' (Hsome c Hc) Huse
           Hsatisfied Hextends (v, slot, functions, value_slots)
           Hsatisfied_c).
    + pose proof
        (gather_known_none Pos.eqb pos_eqb_decides_equality
           (fun case : row_like_closures_case => case) knowns slot
           (Hnone slot Hy) (index, (known_closures, Or_bottom.Bottom))
           (Hin_knowns _ _ Hin))
        as Hv.
      cbn [fst snd] in Hv.
      discriminate (eq_trans (eq_sym Hv) Hc).
  - intros Hk. split; [ exact (Hka Hk) | ].
    intros simple kind Hsimple. simpl in Hsimple.
    apply in_flat_map in Hsimple as ([key y] & Hin & Hsimple).
    cbn [snd] in Hsimple.
    destruct (Hfound key y (Hin_known key y Hin)) as (vals & _ & Hholds).
    destruct (Hholds sa (grows_refl sa)) as (_ & _ & Hkinds).
    exact (Hkinds Hk simple kind Hsimple).
Qed.

End Body.

End Traversal.

(* ======================================================================== *)
(* The statements                                                           *)
(* ======================================================================== *)

Theorem flat_heads_sound : flat_heads_sound_statement.
Proof.
  intros typing_env_well_formed state joined_env definitions_of_existentials
    kind_in_target_env state_valid state_kinded n_way_join_simples
    import_type join_env_n_way_join_env_extension
    reduce_head_of_kind_naked_immediate
    (_ & Hsimples & _ & Hextension) Hreduce.
  split; [ apply n_way_join_unknown_is_sound | ].
  split; [ apply n_way_join_relation_simples_is_sound; exact Hsimples | ].
  split; [ apply n_way_join_is_null_is_sound; exact Hsimples | ].
  split;
    [ apply n_way_join_head_of_kind_naked_immediate_is_sound; exact Hreduce
    | ].
  split; [ apply n_way_join_head_of_kind_naked_numbers_is_sound | ].
  split; [ apply n_way_join_env_extension_is_sound; exact Hextension | ].
  split;
    [ exact deduce_is_int_simple_is_sound
    | exact deduce_get_tag_simple_is_sound ].
Qed.
