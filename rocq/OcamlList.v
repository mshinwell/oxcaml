(* Models of the OCaml [List] functions the compiler models use, over
   [int]-keyed association lists where a key is involved.

   Functions whose OCaml callback may raise an exception come in a variant
   returning [option] (see OcamlOption.v): [map_opt] is [List.map] and
   [filter_map_opt] is [List.filter_map], each returning [None] if any call
   of the callback would have raised. *)

From Stdlib Require Import ZArith List.
From OxcamlStdlib Require Import OcamlOption OcamlInt.
Import ListNotations.

Local Open Scope sint63_scope.

(* [List.assoc_opt] on [int] keys. *)
Fixpoint assoc_opt {C} (id : int) (l : list (int * C)) : option C :=
  match l with
  | [] => None
  | (k, c) :: l => if id =? k then Some c else assoc_opt id l
  end.

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

(* ---- Lemmas ----------------------------------------------------------- *)

Lemma filter_map_In : forall {A B} (f : A -> option B) l y,
  In y (filter_map f l) -> exists x, In x l /\ f x = Some y.
Proof.
  intros A B f l y. induction l as [| x l IH]; simpl; intros H.
  - contradiction.
  - destruct (f x) as [y'|] eqn:Hx.
    + destruct H as [-> | H].
      * exists x. split; [left; reflexivity | exact Hx].
      * destruct (IH H) as [x' [Hin Hx']]. exists x'. auto.
    + destruct (IH H) as [x' [Hin Hx']]. exists x'. auto.
Qed.

Lemma assoc_opt_In : forall {C} id (l : list (int * C)) c,
  assoc_opt id l = Some c -> In (id, c) l.
Proof.
  intros C id l c. induction l as [| [k c'] l IH]; simpl; intros H.
  - discriminate.
  - destruct (id =? k) eqn:E.
    + apply eqb_int in E. injection H as <-. subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

Lemma assoc_opt_Some : forall {C} id (l : list (int * C)),
  In id (map fst l) -> exists c, assoc_opt id l = Some c.
Proof.
  intros C id l. induction l as [| [k c] l IH]; simpl; intros H.
  - contradiction.
  - destruct (id =? k) eqn:E; [exists c; reflexivity |].
    destruct H as [-> | H]; [rewrite eqb_int_refl in E; discriminate |].
    apply IH. exact H.
Qed.

Lemma assoc_opt_None : forall {C} id (l : list (int * C)),
  ~ In id (map fst l) -> assoc_opt id l = None.
Proof.
  intros C id l. induction l as [| [k c] l IH]; simpl; intros H.
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
  intros C D g l. induction l as [| [k c] l IH]; simpl; intros l' H.
  - injection H as <-. reflexivity.
  - destruct (g c) as [d|]; [| discriminate].
    destruct (map_opt _ l) as [rest|] eqn:Hr; [| discriminate].
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
  intros C D g l. induction l as [| [k c] l IH]; simpl; intros l' H id.
  - injection H as <-. reflexivity.
  - destruct (g c) as [d|] eqn:Hg; [| discriminate].
    destruct (map_opt _ l) as [rest|] eqn:Hr; [| discriminate].
    injection H as <-. simpl. destruct (id =? k).
    + exists d. split; [exact Hg | reflexivity].
    + apply IH. reflexivity.
Qed.

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
  intros C f ids Hf Hnd. induction Hnd as [| id ids Hnin Hnd IH]; simpl.
  - constructor.
  - destruct (f id) as [p |] eqn:Hp; [| exact IH].
    simpl. constructor; [| exact IH].
    intros Hin. apply Hnin. rewrite (Hf id p Hp) in Hin.
    apply (filter_map_keys_In f ids id Hf Hin).
Qed.
