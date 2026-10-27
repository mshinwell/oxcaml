(* Models of the OxCaml [List] functions the compiler models use, over
   [int]-keyed association lists where a key is involved.

   Functions whose OxCaml callback may raise an exception come in a variant
   returning [option] (see OxCamlOption.v): [map_opt] is [List.map] and
   [filter_map_opt] is [List.filter_map], each returning [None] if any call
   of the callback would have raised. *)

From Stdlib Require Import ZArith Lia List.
From OxCamlStdlib Require Import OxCamlOption OxCamlInt.
Import ListNotations.

Local Open Scope sint63_scope.

(* [List.assoc_opt] on [int] keys. *)
Fixpoint assoc_opt {C} (id : int) (l : list (int * C)) : option C :=
  match l with
  | [] => None
  | (k, c) :: l => if id =? k then Some c else assoc_opt id l
  end.

(* The value for [id] in an association list, [dflt] if there is none. *)
Definition assoc_default {C} (dflt : C) (id : int) (l : list (int * C)) : C :=
  match assoc_opt id l with Some c => c | None => dflt end.

Fixpoint filter_map {A B} (f : A -> option B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: l =>
    match f x with
    | Some y => y :: filter_map f l
    | None => filter_map f l
    end
  end.

Definition concat_map {A B} (f : A -> list B) (l : list A) : list B :=
  flat_map f l.

(* [List.fold_left f init l]; Rocq's own [fold_left] takes [init] last. *)
Definition fold_left {A B} (f : A -> B -> A) (init : A) (l : list B) : A :=
  List.fold_left f l init.

(* How many elements of [l] [same] accepts. *)
Definition count_occurrences {A} (same : A -> bool) (l : list A) : int :=
  fold_left (fun n x => if same x then n + one else n) zero l.

(* [List.sort_uniq Int.compare]. Only what the proofs need is assumed: the
   result has no duplicates and the same members as the input. *)
Parameter sort_uniq : list int -> list int.
Axiom sort_uniq_NoDup : forall l, NoDup (sort_uniq l).
Axiom sort_uniq_In : forall l x, In x (sort_uniq l) <-> In x l.

(* [List.compare_length_with l n], the sign of [length l - n]. The models
   only use it to apply a size limit, on which nothing they claim depends,
   so no property of it is assumed. *)
Parameter compare_length_with : forall {A : Type}, list A -> int -> int.

(* [List.map f l] where [f] may raise. *)
Fixpoint map_opt {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: l =>
    let* y := f x in
    let* l := map_opt f l in
    Some (y :: l)
  end.

(* [List.filter_map f l] where [f] may raise: the outer [option] is the
   exception, the inner one is [f]'s answer. *)
Fixpoint filter_map_opt {A B} (f : A -> option (option B)) (l : list A)
    : option (list B) :=
  match l with
  | [] => Some []
  | x :: l =>
    let* y := f x in
    let* l := filter_map_opt f l in
    Some (match y with Some y => y :: l | None => l end)
  end.

(* [arr.(i)] on an array held as a list: [None] where OxCaml would raise
   [Invalid_argument], i.e. for [i] outside [0 .. length - 1]. *)
Fixpoint nth_int {A} (l : list A) (i : int) : option A :=
  match l with
  | [] => None
  | x :: l => if i =? zero then Some x else nth_int l (i - one)
  end.

(* [Array.length a = Array.length b] on arrays held as lists. *)
Fixpoint same_length {A B} (l1 : list A) (l2 : list B) : bool :=
  match l1, l2 with
  | [], [] => true
  | _ :: l1, _ :: l2 => same_length l1 l2
  | [], _ :: _ | _ :: _, [] => false
  end.

(* ---- Lemmas ----------------------------------------------------------- *)

Lemma same_length_spec : forall {A B} (l1 : list A) (l2 : list B),
  same_length l1 l2 = true <-> length l1 = length l2.
Proof.
  intros A B l1. induction l1 as [ | x l1 IH ]; intros [ | y l2 ]; simpl;
    [ tauto | split; discriminate | split; discriminate | ].
  rewrite IH. split; [ intros ->; reflexivity | intros H; injection H; auto ].
Qed.

(* An element at some position is an element of the list. *)
Lemma nth_int_In : forall {A} (l : list A) i x,
  nth_int l i = Some x -> In x l.
Proof.
  intros A l. induction l as [ | y l IH ]; intros i x H; simpl in H.
  - discriminate.
  - destruct (i =? zero).
    + injection H as ->. left. reflexivity.
    + right. exact (IH _ _ H).
Qed.

(* An element of [filter_map f l] is [f] of an element of [l]. *)
Lemma filter_map_In : forall {A B} (f : A -> option B) l y,
  In y (filter_map f l) -> exists x, In x l /\ f x = Some y.
Proof.
  intros A B f l y. induction l as [ | x l IH ]; simpl; intros H.
  - contradiction.
  - destruct (f x) as [ y' | ] eqn:Hx.
    + destruct H as [ -> | H ].
      * exists x. split; [ left; reflexivity | exact Hx ].
      * destruct (IH H) as [x' [Hin Hx']]. exists x'. auto.
    + destruct (IH H) as [x' [Hin Hx']]. exists x'. auto.
Qed.

(* [assoc_opt] finds an entry with the key ... *)
Lemma assoc_opt_In : forall {C} id (l : list (int * C)) c,
  assoc_opt id l = Some c -> In (id, c) l.
Proof.
  intros C id l c. induction l as [ | [k c'] l IH ]; simpl; intros H.
  - discriminate.
  - destruct (id =? k) eqn:E.
    + apply eqb_int in E. injection H as <-. subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(* ... finds one whenever the key is present ... *)
Lemma assoc_opt_Some : forall {C} id (l : list (int * C)),
  In id (map fst l) -> exists c, assoc_opt id l = Some c.
Proof.
  intros C id l. induction l as [ | [k c] l IH ]; simpl; intros H.
  - contradiction.
  - destruct (id =? k) eqn:E; [ exists c; reflexivity | ].
    destruct H as [ -> | H ]; [ rewrite eqb_int_refl in E; discriminate | ].
    apply IH. exact H.
Qed.

(* ... and none when it is absent. *)
Lemma assoc_opt_None : forall {C} id (l : list (int * C)),
  ~ In id (map fst l) -> assoc_opt id l = None.
Proof.
  intros C id l. induction l as [ | [k c] l IH ]; simpl; intros H.
  - reflexivity.
  - destruct (id =? k) eqn:E.
    + apply eqb_int in E. subst. exfalso. apply H. left. reflexivity.
    + apply IH. intros H'. apply H. right. exact H'.
Qed.

(* [map_opt] over an association list, mapping the values: the keys are
   unchanged ... *)
Lemma map_opt_keys : forall {C D} (g : C -> option D) (l : list (int * C)) l',
  map_opt (fun '(id, c) => let* d := g c in Some (id, d)) l = Some l' ->
  map fst l' = map fst l.
Proof.
  intros C D g l. induction l as [ | [k c] l IH ]; simpl; intros l' H.
  - injection H as <-. reflexivity.
  - destruct (g c) as [ d | ]; [ | discriminate ].
    destruct (map_opt _ l) as [ rest | ] eqn:Hr; [ | discriminate ].
    injection H as <-. simpl. f_equal. apply IH. reflexivity.
Qed.

(* ... and each value is mapped. *)
Lemma map_opt_assoc : forall {C D} (g : C -> option D) (l : list (int * C)) l',
  map_opt (fun '(id, c) => let* d := g c in Some (id, d)) l = Some l' ->
  forall id,
    match assoc_opt id l with
    | Some c => exists d, g c = Some d /\ assoc_opt id l' = Some d
    | None => assoc_opt id l' = None
    end.
Proof.
  intros C D g l. induction l as [ | [k c] l IH ]; simpl; intros l' H id.
  - injection H as <-. reflexivity.
  - destruct (g c) as [ d | ] eqn:Hg; [ | discriminate ].
    destruct (map_opt _ l) as [ rest | ] eqn:Hr; [ | discriminate ].
    injection H as <-. simpl. destruct (id =? k).
    + exists d. split; [ exact Hg | reflexivity ].
    + apply IH. reflexivity.
Qed.

(* [rev_append] has the elements of both lists. *)
Lemma in_rev_append : forall {A} (l1 l2 : list A) x,
  In x (rev_append l1 l2) <-> In x l1 \/ In x l2.
Proof.
  intros. rewrite rev_append_rev, in_app_iff, <- in_rev. reflexivity.
Qed.

(* [filter_map] over atoms, where the callback keeps the atom as the key:
   the keys of the result are among the atoms ... *)
Lemma filter_map_keys_In : forall {C} (f : int -> option (int * C)) ids id,
  (forall id p, f id = Some p -> fst p = id) ->
  In id (map fst (filter_map f ids)) -> In id ids.
Proof.
  intros C f ids id Hf Hin.
  apply in_map_iff in Hin as [[id' c] [Hfst Hin]]. simpl in Hfst. subst id'.
  apply filter_map_In in Hin as [x [Hx Hfx]].
  pose proof (Hf x _ Hfx) as E. simpl in E. subst x. exact Hx.
Qed.

(* ... and are distinct if the atoms are. *)
Lemma filter_map_NoDup_keys : forall {C} (f : int -> option (int * C)) ids,
  (forall id p, f id = Some p -> fst p = id) ->
  NoDup ids -> NoDup (map fst (filter_map f ids)).
Proof.
  intros C f ids Hf Hnd. induction Hnd as [ | id ids Hnin Hnd IH ]; simpl.
  - constructor.
  - destruct (f id) as [ p | ] eqn:Hp; [ | exact IH ].
    simpl. constructor; [ | exact IH ].
    intros Hin. apply Hnin. rewrite (Hf id p Hp) in Hin.
    apply (filter_map_keys_In f ids id Hf Hin).
Qed.

(* --- [assoc_opt] and [assoc_default] --- *)

(* In a list whose keys are distinct, the lookup of a key finds its entry. *)
Lemma assoc_opt_NoDup : forall {C} (l : list (int * C)) id c,
  NoDup (map fst l) -> In (id, c) l -> assoc_opt id l = Some c.
Proof.
  intros C l id c. induction l as [ | [k c'] l IH ]; intros Hnd Hin.
  - contradiction.
  - cbn [map fst] in Hnd. inversion Hnd as [ | ? ? Hnin Hnd' ]. subst.
    cbn [assoc_opt]. destruct Hin as [ Heq | Hin ].
    + injection Heq as <- <-. rewrite eqb_int_refl. reflexivity.
    + destruct (id =? k)%sint63 eqn:E.
      * apply eqb_int in E. subst k. exfalso. apply Hnin.
        apply in_map_iff. exists (id, c). split; [ reflexivity | exact Hin ].
      * apply IH; assumption.
Qed.

(* [assoc_default] on a cons: the head's value if its key matches, else the
   lookup in the tail. *)
Lemma assoc_default_cons : forall {C} (dflt : C) id k c l,
  assoc_default dflt id ((k, c) :: l)
  = if (id =? k)%sint63 then c else assoc_default dflt id l.
Proof.
  intros. unfold assoc_default. simpl. destruct (id =? k)%sint63; reflexivity.
Qed.

(* An absent key gives the default. *)
Lemma assoc_default_not_in : forall {C} (dflt : C) id l,
  ~ In id (map fst l) -> assoc_default dflt id l = dflt.
Proof.
  intros. unfold assoc_default. rewrite assoc_opt_None by assumption.
  reflexivity.
Qed.

(* --- [filter] --- *)

Lemma length_filter_le : forall {A} (f : A -> bool) (l : list A),
  (length (filter f l) <= length l)%nat.
Proof.
  intros A f l. induction l as [ | x l IH ]; [ reflexivity | ].
  simpl. destruct (f x); simpl; lia.
Qed.

(* A filter that accepts less keeps no more elements ... *)
Lemma filter_le : forall {A} (f g : A -> bool) (l : list A),
  (forall y, f y = true -> g y = true) ->
  (length (filter f l) <= length (filter g l))%nat.
Proof.
  intros A f g l Hfg. induction l as [ | y l IH ]; [ reflexivity | ].
  simpl. destruct (f y) eqn:Hf.
  - rewrite (Hfg y Hf). simpl. lia.
  - destruct (g y); simpl; lia.
Qed.

(* ... and strictly fewer when it rejects an element of the list that the
   other accepts. *)
Lemma filter_lt : forall {A} (f g : A -> bool) (l : list A) x,
  (forall y, f y = true -> g y = true) ->
  In x l -> g x = true -> f x = false ->
  (length (filter f l) < length (filter g l))%nat.
Proof.
  intros A f g l x Hfg Hin Hg Hf.
  induction l as [ | y l IH ]; [ contradiction | ].
  simpl. destruct Hin as [ -> | Hin ].
  - rewrite Hf, Hg. simpl. pose proof (filter_le f g l Hfg). lia.
  - destruct (f y) eqn:Hfy.
    + rewrite (Hfg y Hfy). simpl. apply IH in Hin. lia.
    + destruct (g y); simpl; apply IH in Hin; lia.
Qed.
