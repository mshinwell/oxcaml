(* A Rocq model of [backend/ssa/loop/fourier_motzkin.ml].

   See the reading guide at the top of LoopComparisons.v for the Rocq
   vocabulary and the layout of the shared files. As there, this file has
   four parts: (1) a transcription of the OCaml, (2) the intended meaning,
   (3) stepping-stone lemmas, (4) the theorems. Parts 1 and 2 are the part
   to check by eye.

   The OCaml raises [Overflow] where an integer operation would wrap; here
   every function that can overflow returns an [option], with [None]
   standing for the exception (see OcamlOption.v).

   Trusted parts, beyond the [Int64] model in OcamlInt64.v and the
   [sort_uniq] assumptions in OcamlList.v (each is a few lines of OCaml to
   review): the overflow tests of the [_ovf] helpers are taken as given,
   by the axioms [add_fits_spec] and friends below, to answer whether the
   exact result fits the type. The OCaml implements that test with the
   standard sign-bit trick for addition and a divide-back check for
   multiplication (the lines quoted in FourierMotzkinExtract.v).

   The main results are [feasible_sound] and [entails_sound] in part 4: when
   [feasible] says "infeasible", no integer assignment satisfies the
   inequalities, and when [entails] says the goal follows from the facts, it
   does, for every integer assignment satisfying the facts. These are the
   directions the loop passes rely on; [feasible] answering [true] promises
   nothing (it is conservative on overflow and on size limits). *)

From Stdlib Require Import ZArith Lia Bool List Recdef.
From OxcamlStdlib Require Import OcamlOption OcamlInt OcamlInt64 OcamlList.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: transcription of the OCaml                                       *)
(* ======================================================================== *)

Local Open Scope sint63_scope.

(* ---- Overflow-checked [int] arithmetic (the [_ovf] helpers) ----------- *)

(* The overflow tests: whether the exact sum or product of two machine
   integers fits an OCaml [int]. *)
Parameter add_fits mul_fits : int -> int -> bool.
Axiom add_fits_spec : forall a b, add_fits a b = fits_int (to_Z a + to_Z b).
Axiom mul_fits_spec : forall a b, mul_fits a b = fits_int (to_Z a * to_Z b).

Definition add_ovf (a b : int) : option int :=
  if add_fits a b then Some (a + b) else None.

Definition mul_ovf (a b : int) : option int :=
  if mul_fits a b then Some (a * b) else None.

Definition neg_ovf (a : int) : option int :=
  if a =? min_int then None else Some (- a).

(* The coefficient of [id] in a term list, [dflt] if absent. *)
Definition coeff_gen {C} (dflt : C) (id : int) (terms : list (int * C)) : C :=
  match assoc_opt id terms with Some c => c | None => dflt end.

(* ---- [module Affine] -------------------------------------------------- *)

Module Affine.
  Record t := { const : int; terms : list (int * int) }.

  (* OCaml [Affine.const]; the name is taken by the field here. *)
  Definition constant (c : int) : t := {| const := c; terms := [] |}.

  Definition var (id : int) : t := {| const := zero; terms := [(id, one)] |}.

  Definition coeff (id : int) (f : t) : int := coeff_gen zero id f.(terms).

  Fixpoint terms_equal (l1 l2 : list (int * int)) : bool :=
    match l1, l2 with
    | [], [] => true
    | (i1, c1) :: l1, (i2, c2) :: l2 =>
      (i1 =? i2) && (c1 =? c2) && terms_equal l1 l2
    | _, _ => false
    end.

  Definition equal (a b : t) : bool :=
    (a.(const) =? b.(const)) && terms_equal a.(terms) b.(terms).

  Definition add_const (f : t) (c : int) : t :=
    {| const := f.(const) + c; terms := f.(terms) |}.

  Definition add (a b : t) : t :=
    let ids := sort_uniq (map fst a.(terms) ++ map fst b.(terms)) in
    let ts :=
      filter_map
        (fun id =>
          let c := coeff id a + coeff id b in
          if c =? zero then None else Some (id, c))
        ids
    in
    {| const := a.(const) + b.(const); terms := ts |}.

  Definition scale (k : int) (f : t) : t :=
    if k =? zero
    then constant zero
    else
      {| const := f.(const) * k;
         terms := map (fun '(id, c) => (id, c * k)) f.(terms) |}.

  Definition neg (f : t) : t := scale minus_one f.

  Definition sub (a b : t) : t := add a (neg b).

  Definition scale_checked (k : int) (f : t) : option t :=
    if k =? zero
    then Some (constant zero)
    else
      let* c := mul_ovf f.(const) k in
      let* ts :=
        map_opt (fun '(id, c) => let* c := mul_ovf c k in Some (id, c))
          f.(terms)
      in
      Some {| const := c; terms := ts |}.

  Definition add_checked (a b : t) : option t :=
    let ids := sort_uniq (map fst a.(terms) ++ map fst b.(terms)) in
    let* ts :=
      filter_map_opt
        (fun id =>
          let* c := add_ovf (coeff id a) (coeff id b) in
          Some (if c =? zero then None else Some (id, c)))
        ids
    in
    let* c := add_ovf a.(const) b.(const) in
    Some {| const := c; terms := ts |}.

  Definition add_const_checked (f : t) (c : int) : option t :=
    let* k := add_ovf f.(const) c in
    Some {| const := k; terms := f.(terms) |}.

  Definition sub_checked (a b : t) : option t :=
    let* nb := scale_checked minus_one b in
    add_checked a nb.
End Affine.

(* ---- Resolvents ------------------------------------------------------- *)

(* [add_ovf64] / [mul_ovf64]: the exact result, if it fits. *)
(* The overflow tests on [Int64], as for [int] above. *)
Parameter add_fits64 mul_fits64 : Int64.t -> Int64.t -> bool.
Axiom add_fits64_spec : forall a b,
  add_fits64 a b = fits_int64 (Int64.to_Z a + Int64.to_Z b).
Axiom mul_fits64_spec : forall a b,
  mul_fits64 a b = fits_int64 (Int64.to_Z a * Int64.to_Z b).

Definition add_ovf64 (a b : Int64.t) : option Int64.t :=
  if add_fits64 a b then Some (Int64.add a b) else None.

Definition mul_ovf64 (a b : Int64.t) : option Int64.t :=
  if mul_fits64 a b then Some (Int64.mul a b) else None.

(* [let rec gcd64 a b = if b = 0L then a else gcd64 b (Int64.rem a b)].
   Rocq needs a termination argument: [|b|] strictly decreases. *)
Function gcd64 (a b : Int64.t)
    {measure (fun b => Z.to_nat (Z.abs (Int64.to_Z b))) b} : Int64.t :=
  if Int64.equal b Int64.zero then a else gcd64 b (Int64.rem a b).
Proof.
  intros a b Hb. apply Int64.nonzero in Hb.
  rewrite Int64.rem_spec by exact Hb.
  apply Z2Nat.inj_lt; try apply Z.abs_nonneg.
  apply Z.rem_bound_abs. exact Hb.
Defined.

(* Floor division for [g > 0]. *)
Definition fdiv64 (c g : Int64.t) : Int64.t :=
  let q := Int64.div c g in
  if (Int64.compare c Int64.zero <? zero)
     && negb (Int64.equal (Int64.rem c g) Int64.zero)
  then Int64.sub q Int64.one
  else q.

Definition to_int_ovf (x : Int64.t) : option int :=
  let i := Int64.to_int x in
  if Int64.equal (Int64.of_int i) x then Some i else None.

(* The local [coeff] of [resolvent], over [Int64] coefficients. *)
Definition coeff64 := coeff_gen Int64.zero.

(* The local [scaled] of [resolvent]. *)
Definition scaled (k : Int64.t) (f : Affine.t)
    : option (Int64.t * list (int * Int64.t)) :=
  let* c := mul_ovf64 k (Int64.of_int f.(Affine.const)) in
  let* ts :=
    map_opt
      (fun '(id, c) => let* c := mul_ovf64 k (Int64.of_int c) in Some (id, c))
      f.(Affine.terms)
  in
  Some (c, ts).

Definition resolvent (cp cn : int) (p n : Affine.t) : option Affine.t :=
  let cp64 := Int64.of_int cp in
  let cn64 := Int64.of_int cn in
  match scaled cn64 p, scaled cp64 n with
  | Some (pc, pterms), Some (nc, nterms) =>
    let ids := sort_uniq (map fst pterms ++ map fst nterms) in
    let* ts :=
      filter_map_opt
        (fun id =>
          let* c := add_ovf64 (coeff64 id pterms) (coeff64 id nterms) in
          Some (if Int64.equal c Int64.zero then None else Some (id, c)))
        ids
    in
    let* c := add_ovf64 pc nc in
    match ts with
    | [] =>
      Some {| Affine.const :=
                if zero <=? Int64.compare c Int64.zero then zero
                else minus_one;
              Affine.terms := [] |}
    | _ :: _ =>
      let g :=
        fold_left (fun g '(_, c) => gcd64 g (Int64.abs c)) Int64.zero ts
      in
      let g := if zero <? Int64.compare g Int64.one then g else Int64.one in
      let* k := to_int_ovf (fdiv64 c g) in
      let* ts :=
        map_opt
          (fun '(id, c) => let* c := to_int_ovf (Int64.div c g) in Some (id, c))
          ts
      in
      Some {| Affine.const := k; Affine.terms := ts |}
    end
  | _, _ => None
  end.

(* ---- [feasible] and [entails] ----------------------------------------- *)

Definition max_atoms : int := 64.
Definition max_ineqs : int := 10000.

(* The local [elim] of [feasible]. [None] is the [Overflow] raised on the size
   limit; an overflowing resolvent is dropped by [filter_map]. *)
Definition elim (v : int) (ineqs : list Affine.t) : option (list Affine.t) :=
  if zero <? compare_length_with ineqs max_ineqs
  then None
  else
    let cf f := Affine.coeff v f in
    let pos := filter (fun f => zero <? cf f) ineqs in
    let neg := filter (fun f => cf f <? zero) ineqs in
    let zero_coeff := filter (fun f => cf f =? zero) ineqs in
    let resolvents :=
      concat_map
        (fun p =>
          filter_map
            (fun n => let* cn := neg_ovf (cf n) in resolvent (cf p) cn p n)
            neg)
        pos
    in
    Some (rev_append zero_coeff resolvents).

(* [List.fold_left (fun acc v -> elim v acc) ineqs atoms], with [elim]'s
   [Overflow] propagating. *)
Fixpoint elim_all (atoms : list int) (ineqs : list Affine.t)
    : option (list Affine.t) :=
  match atoms with
  | [] => Some ineqs
  | v :: atoms => let* ineqs := elim v ineqs in elim_all atoms ineqs
  end.

Definition feasible (ineqs : list Affine.t) : bool :=
  let atoms :=
    sort_uniq (concat_map (fun f => map fst f.(Affine.terms)) ineqs) in
  if zero <? compare_length_with atoms max_atoms
  then true
  else
    match elim_all atoms ineqs with
    | Some reduced => forallb (fun f => zero <=? f.(Affine.const)) reduced
    | None => true
    end.

Definition entails (facts : list Affine.t) (goal : Affine.t) : bool :=
  let negated :=
    let* ng := Affine.scale_checked minus_one goal in
    Affine.add_const_checked ng minus_one
  in
  match negated with
  | Some ng => negb (feasible (ng :: facts))
  | None => false
  end.

(* ======================================================================== *)
(* Part 2: what the values mean                                             *)
(* ======================================================================== *)

Local Open Scope Z_scope.

(* An assignment of integers to atoms. Atoms stand for machine values, but
   nothing here depends on their range: the results hold for every integer
   assignment, so a fortiori for the machine ones. *)
Definition valuation := int -> Z.

(* [sum coeff * atom] over a term list, for any coefficient type that reads
   as an integer. *)
Definition denote_terms {C} (cZ : C -> Z) (rho : valuation)
    (terms : list (int * C)) : Z :=
  fold_right (fun '(id, c) acc => cZ c * rho id + acc) 0 terms.

(* The value of an affine form: [const + sum coeff * atom]. *)
Definition denote (rho : valuation) (f : Affine.t) : Z :=
  to_Z f.(Affine.const) + denote_terms to_Z rho f.(Affine.terms).

(* A form asserts that its value is non-negative. *)
Definition holds (rho : valuation) (f : Affine.t) : Prop := 0 <= denote rho f.

Definition holds_all (rho : valuation) (l : list Affine.t) : Prop :=
  Forall (holds rho) l.

(* The representation invariant: each atom appears at most once in a term
   list. Every constructor in [Affine] maintains it, so every form the loop
   passes build satisfies it. *)
Definition wf (f : Affine.t) : Prop := NoDup (map fst f.(Affine.terms)).

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

(* --- The overflow-checked operations compute the exact result. --- *)

Lemma add_ovf_spec : forall a b s,
  add_ovf a b = Some s -> to_Z s = to_Z a + to_Z b.
Proof.
  unfold add_ovf. intros a b s H. rewrite add_fits_spec in H.
  destruct (fits_int _) eqn:Hr; [ | discriminate ].
  injection H as <-. apply Sint63.to_Z_add.
  rewrite to_Z_min_int, to_Z_max_int. apply fits_int_true. exact Hr.
Qed.

Lemma mul_ovf_spec : forall a b s,
  mul_ovf a b = Some s -> to_Z s = to_Z a * to_Z b.
Proof.
  unfold mul_ovf. intros a b s H. rewrite mul_fits_spec in H.
  destruct (fits_int _) eqn:Hr; [ | discriminate ].
  injection H as <-. apply Sint63.to_Z_mul.
  rewrite to_Z_min_int, to_Z_max_int. apply fits_int_true. exact Hr.
Qed.

Lemma neg_ovf_spec : forall a s, neg_ovf a = Some s -> to_Z s = - to_Z a.
Proof.
  unfold neg_ovf. intros a s H.
  destruct (a =? min_int)%sint63 eqn:E; [ discriminate | ].
  injection H as <-. apply Sint63.to_Z_opp. apply eqb_int_false. exact E.
Qed.

Lemma add_ovf64_spec : forall a b s,
  add_ovf64 a b = Some s -> Int64.to_Z s = Int64.to_Z a + Int64.to_Z b.
Proof.
  unfold add_ovf64. intros a b s H. rewrite add_fits64_spec in H.
  destruct (fits_int64 _) eqn:Hr; [ | discriminate ].
  injection H as <-. rewrite Int64.add_spec. apply wrap64_id.
  apply fits_int64_true. exact Hr.
Qed.

Lemma mul_ovf64_spec : forall a b s,
  mul_ovf64 a b = Some s -> Int64.to_Z s = Int64.to_Z a * Int64.to_Z b.
Proof.
  unfold mul_ovf64. intros a b s H. rewrite mul_fits64_spec in H.
  destruct (fits_int64 _) eqn:Hr; [ | discriminate ].
  injection H as <-. rewrite Int64.mul_spec. apply wrap64_id.
  apply fits_int64_true. exact Hr.
Qed.

Lemma to_int_ovf_spec : forall x i,
  to_int_ovf x = Some i -> to_Z i = Int64.to_Z x.
Proof.
  unfold to_int_ovf. intros x i H.
  destruct (Int64.equal _ _) eqn:E; [ | discriminate ].
  injection H as <-. apply Int64.equal_spec in E.
  rewrite Int64.of_int_spec in E. exact E.
Qed.

(* --- The normalisation of a resolvent: gcd and floor division. --- *)

(* [gcd64 a b] divides both arguments (that it is their greatest common
   divisor is not needed). *)
Lemma gcd64_divides : forall a b,
  (Int64.to_Z (gcd64 a b) | Int64.to_Z a)
  /\ (Int64.to_Z (gcd64 a b) | Int64.to_Z b).
Proof.
  intros a b. functional induction (gcd64 a b).
  - apply Int64.equal_spec in e. rewrite Int64.to_Z_zero in e. rewrite e.
    split; [ apply Z.divide_refl | apply Z.divide_0_r ].
  - match goal with IH : _ /\ _ |- _ => destruct IH as [IH1 IH2] end.
    apply Int64.nonzero in e.
    rewrite Int64.rem_spec in IH2 by exact e.
    split; [ | exact IH1 ].
    rewrite (Z.quot_rem' (Int64.to_Z a) (Int64.to_Z b)).
    apply Z.divide_add_r; [ apply Z.divide_mul_l; exact IH1 | exact IH2 ].
Qed.

(* [Int64.abs] does not change divisibility, even on [min_int] (which it
   leaves unchanged). *)
Lemma abs64_divide : forall d c,
  (d | Int64.to_Z (Int64.abs c)) -> (d | Int64.to_Z c).
Proof.
  intros d c H. rewrite Int64.abs_spec in H.
  pose proof (Int64.to_Z_bounded c) as Hc. unfold in_int64 in Hc.
  destruct (Z.eq_dec (Int64.to_Z c) (- two63)) as [ E | NE ].
  - rewrite E in *.
    replace (wrap64 (Z.abs (- two63))) with (- two63) in H
      by (unfold wrap64, two63, two64; vm_compute; reflexivity).
    exact H.
  - rewrite wrap64_id in H by (unfold in_int64; lia).
    apply Z.divide_abs_r. exact H.
Qed.

(* The gcd fold of [resolvent] yields a common divisor of all coefficients. *)
Lemma fold_gcd_divides_acc : forall (ts : list (int * Int64.t)) g0,
  (Int64.to_Z (fold_left (fun g '(_, c) => gcd64 g (Int64.abs c)) g0 ts)
   | Int64.to_Z g0).
Proof.
  unfold fold_left. induction ts as [ | [id c] ts IH ]; intros g0; simpl.
  - apply Z.divide_refl.
  - eapply Z.divide_trans; [ apply IH | apply gcd64_divides ].
Qed.

Lemma fold_gcd_divides : forall (ts : list (int * Int64.t)) g0 id c,
  In (id, c) ts ->
  (Int64.to_Z (fold_left (fun g '(_, c) => gcd64 g (Int64.abs c)) g0 ts)
   | Int64.to_Z c).
Proof.
  unfold fold_left.
  induction ts as [ | [id' c'] ts IH ]; intros g0 id c Hin; simpl in *.
  - contradiction.
  - destruct Hin as [ E | Hin ].
    + injection E as -> ->.
      pose proof (fold_gcd_divides_acc ts (gcd64 g0 (Int64.abs c))) as Hacc.
      unfold fold_left in Hacc.
      eapply Z.divide_trans; [ exact Hacc | ].
      apply abs64_divide. apply gcd64_divides.
    + eapply IH. exact Hin.
Qed.

(* [fdiv64] is floor division. *)
Lemma fdiv64_spec : forall c g,
  0 < Int64.to_Z g -> Int64.to_Z (fdiv64 c g) = Int64.to_Z c / Int64.to_Z g.
Proof.
  intros c g Hg. unfold fdiv64.
  assert (Hg0 : Int64.to_Z g <> 0) by lia.
  pose proof (Int64.to_Z_bounded c) as Hc. unfold in_int64 in Hc.
  pose proof (Z.quot_rem' (Int64.to_Z c) (Int64.to_Z g)) as Hqr.
  pose proof (Z.rem_bound_abs (Int64.to_Z c) (Int64.to_Z g) Hg0) as Hrb.
  assert (Hq : Int64.to_Z (Int64.div c g)
               = Z.quot (Int64.to_Z c) (Int64.to_Z g)).
  { rewrite Int64.div_spec by exact Hg0. apply wrap64_id.
    apply quot_in_range; [ exact Hg | exact (Int64.to_Z_bounded c) ]. }
  assert (Hlt' : (Int64.compare c Int64.zero <? zero)%sint63 = true
                 <-> Int64.to_Z c < 0)
    by (rewrite Int64.compare_lt, Int64.to_Z_zero; reflexivity).
  assert (Heq' : Int64.equal (Int64.rem c g) Int64.zero = true
                 <-> Z.rem (Int64.to_Z c) (Int64.to_Z g) = 0)
    by (rewrite Int64.equal_spec, Int64.rem_spec, Int64.to_Z_zero by exact Hg0;
        reflexivity).
  destruct (Int64.compare c Int64.zero <? zero)%sint63 eqn:Hlt;
    destruct (Int64.equal (Int64.rem c g) Int64.zero) eqn:Heq; simpl.
  - (* c < 0 and g divides c: the quotient is exact. *)
    assert (Hr : Z.rem (Int64.to_Z c) (Int64.to_Z g) = 0)
      by (apply Heq'; reflexivity).
    rewrite Hq. apply Z.div_unique_pos with (r := 0); lia.
  - (* c < 0 and g does not divide c: round the quotient down. *)
    assert (Hneg : Int64.to_Z c < 0) by (apply Hlt'; reflexivity).
    assert (Hr : Z.rem (Int64.to_Z c) (Int64.to_Z g) <> 0)
      by (intro H; apply Heq' in H; discriminate).
    assert (Hrneg : Z.rem (Int64.to_Z c) (Int64.to_Z g) <= 0)
      by (apply Z.rem_nonpos; lia).
    assert (Hg2 : 2 <= Int64.to_Z g).
    { destruct (Z.eq_dec (Int64.to_Z g) 1) as [ E | E ]; [ | lia ].
      rewrite E, Z.rem_1_r in Hr. contradiction. }
    assert (Hqb : - two63 < Z.quot (Int64.to_Z c) (Int64.to_Z g)).
    { pose proof (quot_abs_le (Int64.to_Z c) (Int64.to_Z g) Hg) as Habs.
      pose proof (Int64.to_Z_bounded g) as Hgb. unfold in_int64 in Hgb.
      destruct (Z.eq_dec (Z.quot (Int64.to_Z c) (Int64.to_Z g)) (- two63))
        as [ E | NE ].
      - exfalso. rewrite E in Hqr. unfold two63 in *. lia.
      - unfold two63 in *. lia. }
    pose proof (quot_in_range (Int64.to_Z c) (Int64.to_Z g) Hg
                  (Int64.to_Z_bounded c)) as Hqrange.
    unfold in_int64 in Hqrange.
    rewrite Int64.sub_spec, Hq, Int64.to_Z_one.
    rewrite wrap64_id by (unfold in_int64; unfold two63 in *; lia).
    apply Z.div_unique_pos
      with (r := Z.rem (Int64.to_Z c) (Int64.to_Z g) + Int64.to_Z g).
    + lia.
    + rewrite Z.mul_sub_distr_l. lia.
  - (* c >= 0 and g divides c. *)
    assert (Hr : Z.rem (Int64.to_Z c) (Int64.to_Z g) = 0)
      by (apply Heq'; reflexivity).
    rewrite Hq. apply Z.div_unique_pos with (r := 0); lia.
  - (* c >= 0 and g does not divide c: the quotient is already the floor. *)
    assert (Hnn : 0 <= Int64.to_Z c).
    { destruct (Z_le_gt_dec 0 (Int64.to_Z c)) as [ | Hneg ]; [ assumption | ].
      exfalso. assert (E : false = true) by (apply Hlt'; lia). discriminate E. }
    assert (Hrnn : 0 <= Z.rem (Int64.to_Z c) (Int64.to_Z g))
      by (apply Z.rem_nonneg; lia).
    rewrite Hq.
    apply Z.div_unique_pos with (r := Z.rem (Int64.to_Z c) (Int64.to_Z g)); lia.
Qed.

(* [Int64.div] by a positive divisor that divides exactly is the exact
   quotient. *)
Lemma div_exact64 : forall c g,
  0 < Int64.to_Z g -> (Int64.to_Z g | Int64.to_Z c) ->
  Int64.to_Z (Int64.div c g) = Int64.to_Z c / Int64.to_Z g.
Proof.
  intros c g Hg Hd. rewrite Int64.div_spec by lia.
  rewrite wrap64_id
    by (apply quot_in_range; [ lia | apply Int64.to_Z_bounded ]).
  apply Z.quot_div_exact; [ lia | exact Hd ].
Qed.

(* --- Sums over atoms. --- *)

(* [sum f id] over a list of atoms. *)
Definition sum_ids (f : int -> Z) (ids : list int) : Z :=
  fold_right (fun id acc => f id + acc) 0 ids.

Lemma sum_ids_cons : forall f id ids,
  sum_ids f (id :: ids) = f id + sum_ids f ids.
Proof. reflexivity. Qed.

Lemma sum_ids_ext : forall f g ids,
  (forall id, In id ids -> f id = g id) -> sum_ids f ids = sum_ids g ids.
Proof.
  intros f g ids H. induction ids as [ | id ids IH ]; [ reflexivity | ].
  rewrite !sum_ids_cons. rewrite H by (left; reflexivity).
  rewrite IH; [ reflexivity | ]. intros. apply H. right. assumption.
Qed.

Lemma sum_ids_zero : forall f ids,
  (forall id, In id ids -> f id = 0) -> sum_ids f ids = 0.
Proof.
  intros f ids H. induction ids as [ | id ids IH ]; [ reflexivity | ].
  rewrite sum_ids_cons, H by (left; reflexivity).
  rewrite IH; [ reflexivity | ]. intros. apply H. right. assumption.
Qed.

Lemma sum_ids_add : forall f g ids,
  sum_ids (fun id => f id + g id) ids = sum_ids f ids + sum_ids g ids.
Proof.
  intros f g ids. induction ids as [ | id ids IH ]; [ reflexivity | ].
  rewrite !sum_ids_cons, IH. cbv beta. ring.
Qed.

Lemma sum_ids_scale : forall k f ids,
  sum_ids (fun id => k * f id) ids = k * sum_ids f ids.
Proof.
  intros k f ids. induction ids as [ | id ids IH ]; [ simpl; ring | ].
  rewrite !sum_ids_cons, IH. cbv beta. ring.
Qed.

(* Splitting off the contribution of one atom [id0] that occurs exactly
   once in [ids]. *)
Lemma sum_ids_split : forall f g ids id0 v,
  NoDup ids -> In id0 ids ->
  (forall id, id <> id0 -> f id = g id) -> f id0 = v + g id0 ->
  sum_ids f ids = v + sum_ids g ids.
Proof.
  intros f g ids id0 v Hnd Hin Hfg Hv.
  induction ids as [ | id ids IH ]; [ contradiction | ].
  apply NoDup_cons_iff in Hnd as [Hnotin Hnd].
  rewrite !sum_ids_cons.
  destruct Hin as [ -> | Hin ].
  - rewrite Hv. rewrite (sum_ids_ext f g ids); [ lia | ].
    intros id' Hid'. apply Hfg. intros ->. contradiction.
  - rewrite (Hfg id) by (intros ->; contradiction).
    rewrite (IH Hnd Hin). lia.
Qed.

Lemma denote_terms_cons : forall {C} (cZ : C -> Z) rho id c terms,
  denote_terms cZ rho ((id, c) :: terms)
  = cZ c * rho id + denote_terms cZ rho terms.
Proof. reflexivity. Qed.

Lemma coeff_gen_cons : forall {C} (dflt : C) id k c terms,
  coeff_gen dflt id ((k, c) :: terms)
  = if (id =? k)%sint63 then c else coeff_gen dflt id terms.
Proof.
  intros. unfold coeff_gen. simpl. destruct (id =? k)%sint63; reflexivity.
Qed.

Lemma coeff_gen_not_in : forall {C} (dflt : C) id terms,
  ~ In id (map fst terms) -> coeff_gen dflt id terms = dflt.
Proof.
  intros. unfold coeff_gen. rewrite assoc_opt_None by assumption. reflexivity.
Qed.

(* The value of a duplicate-free term list is the sum, over any
   duplicate-free list of atoms covering it, of coefficient times atom. *)
Lemma sum_ids_coeff : forall {C} (cZ : C -> Z) (dflt : C) rho terms ids,
  cZ dflt = 0 -> NoDup (map fst terms) -> NoDup ids ->
  incl (map fst terms) ids ->
  sum_ids (fun id => cZ (coeff_gen dflt id terms) * rho id) ids
  = denote_terms cZ rho terms.
Proof.
  intros C cZ dflt rho terms.
  induction terms as [ | [k c] terms IH ]; intros ids Hd Hnd Hnd_ids Hincl.
  - apply sum_ids_zero. intros id _. unfold coeff_gen. simpl. rewrite Hd. ring.
  - apply NoDup_cons_iff in Hnd as [Hk Hnd].
    rewrite denote_terms_cons.
    rewrite <- (IH ids Hd Hnd Hnd_ids)
      by (intros x Hx; apply Hincl; right; exact Hx).
    apply (sum_ids_split _ _ ids k).
    + exact Hnd_ids.
    + apply Hincl. left. reflexivity.
    + intros id Hne. cbv beta. rewrite coeff_gen_cons.
      destruct (id =? k)%sint63 eqn:E; [ apply eqb_int in E; contradiction | ].
      reflexivity.
    + cbv beta. rewrite coeff_gen_cons, eqb_int_refl.
      rewrite (coeff_gen_not_in dflt k terms Hk), Hd. ring.
Qed.

(* A duplicate-free term list all of whose coefficients are zero has value
   zero. *)
Lemma denote_terms_zero : forall rho (terms : list (int * int)),
  NoDup (map fst terms) ->
  (forall id, In id (map fst terms) -> to_Z (coeff_gen zero id terms) = 0) ->
  denote_terms to_Z rho terms = 0.
Proof.
  intros rho terms Hnd Hz.
  rewrite <- (sum_ids_coeff to_Z zero rho terms (map fst terms));
    [ | reflexivity | exact Hnd | exact Hnd | intros x Hx; exact Hx ].
  apply sum_ids_zero. intros id Hid. rewrite Hz by exact Hid. ring.
Qed.

(* --- Merging term lists. --- *)

(* The shape shared by [Affine.add_checked] and [resolvent]: for each atom
   a checked coefficient, dropped when zero. *)
Definition merge_terms {C} (f : int -> option C) (is_zero : C -> bool)
    (ids : list int) : option (list (int * C)) :=
  filter_map_opt
    (fun id =>
      let* c := f id in
      Some (if is_zero c then None else Some (id, c)))
    ids.

Lemma merge_terms_cons : forall {C} f (z : C -> bool) id ids,
  merge_terms f z (id :: ids)
  = (let* c := f id in
     let* rest := merge_terms f z ids in
     Some (if z c then rest else (id, c) :: rest)).
Proof.
  intros. unfold merge_terms. simpl.
  destruct (f id) as [ c | ]; [ | reflexivity ].
  destruct (filter_map_opt _ ids); [ | reflexivity ].
  destruct (z c); reflexivity.
Qed.

Lemma merge_keys : forall {C} f (z : C -> bool) ids ts,
  merge_terms f z ids = Some ts -> forall id, In id (map fst ts) -> In id ids.
Proof.
  intros C f z ids. induction ids as [ | id ids IH ]; intros ts H id' Hin.
  - injection H as <-. contradiction.
  - rewrite merge_terms_cons in H.
    destruct (f id) as [ c | ]; [ | discriminate ].
    destruct (merge_terms f z ids) as [ rest | ] eqn:Hr; [ | discriminate ].
    injection H as <-. destruct (z c).
    + right. eapply IH; [ reflexivity | exact Hin ].
    + simpl in Hin. destruct Hin as [ -> | Hin ]; [ left; reflexivity | ].
      right. eapply IH; [ reflexivity | exact Hin ].
Qed.

Lemma merge_NoDup : forall {C} f (z : C -> bool) ids ts,
  NoDup ids -> merge_terms f z ids = Some ts -> NoDup (map fst ts).
Proof.
  intros C f z ids. induction ids as [ | id ids IH ]; intros ts Hnd H.
  - injection H as <-. constructor.
  - apply NoDup_cons_iff in Hnd as [Hnot Hnd].
    rewrite merge_terms_cons in H.
    destruct (f id) as [ c | ]; [ | discriminate ].
    destruct (merge_terms f z ids) as [ rest | ] eqn:Hr; [ | discriminate ].
    injection H as <-. destruct (z c).
    + eapply IH; [ exact Hnd | reflexivity ].
    + simpl. constructor; [ | eapply IH; [ exact Hnd | reflexivity  ] ].
      intros Hin. apply Hnot. eapply merge_keys; [ exact Hr | exact Hin ].
Qed.

Lemma merge_coeff : forall {C} f (z : C -> bool) (dflt : C) ids ts,
  NoDup ids -> merge_terms f z ids = Some ts ->
  forall id, In id ids ->
    exists c, f id = Some c
      /\ coeff_gen dflt id ts = (if z c then dflt else c)
      /\ (In id (map fst ts) <-> z c = false).
Proof.
  intros C f z dflt ids. induction ids as [ | id ids IH ];
    intros ts Hnd H id' Hin;
    [ contradiction | ].
  apply NoDup_cons_iff in Hnd as [Hnot Hnd].
  rewrite merge_terms_cons in H.
  destruct (f id) as [ c | ] eqn:Hf; [ | discriminate ].
  destruct (merge_terms f z ids) as [ rest | ] eqn:Hr; [ | discriminate ].
  injection H as <-.
  assert (Hrest : ~ In id (map fst rest))
    by (intros Hin'; apply Hnot; eapply merge_keys; [ exact Hr | exact Hin' ]).
  destruct Hin as [ -> | Hin ].
  - exists c. split; [ exact Hf | ]. destruct (z c) eqn:Hz.
    + split; [ apply coeff_gen_not_in; exact Hrest | ].
      split; [ intros Hin'; contradiction | discriminate ].
    + split; [ rewrite coeff_gen_cons, eqb_int_refl; reflexivity | ].
      split; [ reflexivity | intros _; left; reflexivity ].
  - destruct (IH rest Hnd eq_refl id' Hin) as [c' [Hf' [Hc' Hin']]].
    exists c'. split; [ exact Hf' | ].
    assert (Hne : id' <> id) by (intros ->; contradiction).
    destruct (z c).
    + split; [ exact Hc' | exact Hin' ].
    + split.
      * rewrite coeff_gen_cons.
        destruct (id' =? id)%sint63 eqn:E;
          [ apply eqb_int in E; contradiction | exact Hc' ].
      * simpl. split.
        { intros [ E | Hin'' ]; [ congruence | apply Hin'; exact Hin'' ]. }
        { intros Hz. right. apply Hin'. exact Hz. }
Qed.

(* The value of a merged term list is the sum over the atoms of the merged
   coefficients. *)
Lemma merge_denote : forall {C} (cZ : C -> Z) f (z : C -> bool) (dflt : C)
    rho (fz : int -> Z) ids ts,
  cZ dflt = 0 -> (forall c, z c = true -> cZ c = 0) -> NoDup ids ->
  (forall id c, In id ids -> f id = Some c -> cZ c = fz id) ->
  merge_terms f z ids = Some ts ->
  denote_terms cZ rho ts = sum_ids (fun id => fz id * rho id) ids.
Proof.
  intros C cZ f z dflt rho fz ids ts Hd Hz Hnd Hf H.
  rewrite <- (sum_ids_coeff cZ dflt rho ts ids);
    [ | exact Hd | eapply merge_NoDup; eauto | exact Hnd
     | intros x Hx; eapply merge_keys; eauto].
  apply sum_ids_ext. intros id Hid.
  destruct (merge_coeff f z dflt ids ts Hnd H id Hid) as [c [Hc [Hcoeff _]]].
  rewrite Hcoeff. rewrite <- (Hf id c Hid Hc).
  destruct (z c) eqn:Hzc; [ rewrite Hd, (Hz c Hzc); reflexivity | reflexivity ].
Qed.

(* --- The [Affine] operations. --- *)

Lemma denote_record : forall rho c ts,
  denote rho {| Affine.const := c; Affine.terms := ts |}
  = to_Z c + denote_terms to_Z rho ts.
Proof. reflexivity. Qed.

Lemma constant_denote : forall rho c, denote rho (Affine.constant c) = to_Z c.
Proof.
  intros. unfold Affine.constant. rewrite denote_record.
  change (denote_terms to_Z rho []) with 0. ring.
Qed.

Lemma constant_wf : forall c, wf (Affine.constant c).
Proof. intros. constructor. Qed.

Lemma var_denote : forall rho id, denote rho (Affine.var id) = rho id.
Proof.
  intros. unfold Affine.var. rewrite denote_record, denote_terms_cons.
  change (denote_terms to_Z rho []) with 0. rewrite to_Z_zero, to_Z_one. ring.
Qed.

Lemma var_wf : forall id, wf (Affine.var id).
Proof. intros. unfold wf. simpl. constructor; [ tauto | constructor ]. Qed.

Lemma scale_terms_denote : forall rho k (terms : list (int * int)) ts,
  map_opt (fun '(id, c) => let* c := mul_ovf c k in Some (id, c)) terms
  = Some ts ->
  denote_terms to_Z rho ts = to_Z k * denote_terms to_Z rho terms.
Proof.
  intros rho k terms. induction terms as [ | [id c0] terms IH ]; intros ts Hts.
  - injection Hts as <-. change (denote_terms to_Z rho []) with 0. ring.
  - cbn [map_opt] in Hts.
    destruct (mul_ovf c0 k) as [ d | ] eqn:Hd; [ | discriminate ].
    destruct (map_opt _ terms) as [ rest | ] eqn:Hr; [ | discriminate ].
    injection Hts as <-. rewrite !denote_terms_cons, (IH rest eq_refl).
    apply mul_ovf_spec in Hd. rewrite Hd. ring.
Qed.

Lemma scale_checked_spec : forall rho k f f',
  Affine.scale_checked k f = Some f' ->
  denote rho f' = to_Z k * denote rho f
  /\ (forall id, In id (map fst f'.(Affine.terms)) ->
        In id (map fst f.(Affine.terms)))
  /\ (wf f -> wf f').
Proof.
  intros rho k f f' H. unfold Affine.scale_checked in H.
  destruct (k =? zero)%sint63 eqn:Hk.
  - apply eqb_int in Hk. subst k. injection H as <-.
    rewrite constant_denote, to_Z_zero.
    split; [ ring | ].
    split; [ intros id Hin; contradiction | intros _; constructor ].
  - destruct (mul_ovf _ k) as [ c | ] eqn:Hc; [ | discriminate ].
    destruct (map_opt _ _) as [ ts | ] eqn:Hts; [ | discriminate ].
    injection H as <-.
    pose proof (map_opt_keys _ _ _ Hts) as Hkeys.
    pose proof (scale_terms_denote rho k _ _ Hts) as Hdt.
    apply mul_ovf_spec in Hc.
    unfold denote, wf. cbn [Affine.const Affine.terms]. rewrite Hc, Hdt, Hkeys.
    split; [ ring | split; tauto ].
Qed.

Lemma add_checked_spec : forall rho a b c,
  wf a -> wf b -> Affine.add_checked a b = Some c ->
  denote rho c = denote rho a + denote rho b
  /\ (forall id, In id (map fst c.(Affine.terms)) ->
        In id (map fst a.(Affine.terms)) \/ In id (map fst b.(Affine.terms)))
  /\ wf c.
Proof.
  intros rho a b c Ha Hb H. unfold Affine.add_checked in H.
  set (ids := sort_uniq (map fst a.(Affine.terms) ++ map fst b.(Affine.terms)))
    in *.
  assert (Hnd : NoDup ids) by apply sort_uniq_NoDup.
  assert (Hids : forall x, In x ids <->
                   In x (map fst a.(Affine.terms))
                   \/ In x (map fst b.(Affine.terms)))
    by (intros x; unfold ids; rewrite sort_uniq_In, in_app_iff; reflexivity).
  change (filter_map_opt _ ids)
    with (merge_terms
            (fun id => add_ovf (Affine.coeff id a) (Affine.coeff id b))
            (fun c => (c =? zero)%sint63) ids) in H.
  destruct (merge_terms _ _ ids) as [ ts | ] eqn:Hts; [ | discriminate ].
  destruct (add_ovf _ _) as [ k | ] eqn:Hk; [ | discriminate ].
  injection H as <-. apply add_ovf_spec in Hk.
  assert (Hdt : denote_terms to_Z rho ts
                = denote_terms to_Z rho a.(Affine.terms)
                  + denote_terms to_Z rho b.(Affine.terms)).
  { rewrite (merge_denote to_Z
               (fun id => add_ovf (Affine.coeff id a) (Affine.coeff id b))
               (fun c => (c =? zero)%sint63) zero rho
               (fun id => to_Z (Affine.coeff id a) + to_Z (Affine.coeff id b))
               ids ts).
    - rewrite (sum_ids_ext _
                 (fun id => to_Z (Affine.coeff id a) * rho id
                            + to_Z (Affine.coeff id b) * rho id))
        by (intros; ring).
      rewrite sum_ids_add. unfold Affine.coeff.
      rewrite !(sum_ids_coeff to_Z zero rho)
        by first [ reflexivity | assumption
                 | (intros x Hx; apply Hids; tauto) ].
      reflexivity.
    - reflexivity.
    - intros c0 Hc0. apply eqb_int in Hc0. subst c0. reflexivity.
    - exact Hnd.
    - intros id c0 _ Hc0. apply add_ovf_spec in Hc0. exact Hc0.
    - exact Hts. }
  unfold denote, wf. cbn [Affine.const Affine.terms]. rewrite Hk, Hdt.
  split; [ ring | split ].
  - intros id Hin. apply Hids. eapply merge_keys; [ exact Hts | exact Hin ].
  - eapply merge_NoDup; [ exact Hnd | exact Hts ].
Qed.

Lemma add_const_checked_spec : forall rho f k f',
  Affine.add_const_checked f k = Some f' ->
  denote rho f' = denote rho f + to_Z k
  /\ f'.(Affine.terms) = f.(Affine.terms)
  /\ (wf f -> wf f').
Proof.
  intros rho f k f' H. unfold Affine.add_const_checked in H.
  destruct (add_ovf _ _) as [ c | ] eqn:Hc; [ | discriminate ].
  injection H as <-. apply add_ovf_spec in Hc.
  unfold denote, wf. cbn [Affine.const Affine.terms]. rewrite Hc.
  split; [ ring | split; [ reflexivity | tauto  ] ].
Qed.

Lemma sub_checked_spec : forall rho a b c,
  wf a -> wf b -> Affine.sub_checked a b = Some c ->
  denote rho c = denote rho a - denote rho b
  /\ (forall id, In id (map fst c.(Affine.terms)) ->
        In id (map fst a.(Affine.terms)) \/ In id (map fst b.(Affine.terms)))
  /\ wf c.
Proof.
  intros rho a b c Ha Hb H. unfold Affine.sub_checked in H.
  destruct (Affine.scale_checked minus_one b) as [ nb | ] eqn:Hnb;
    [ | discriminate ].
  destruct (scale_checked_spec rho _ _ _ Hnb) as [Hd [Hkeys Hwf]].
  rewrite to_Z_minus_one in Hd.
  destruct (add_checked_spec rho _ _ _ Ha (Hwf Hb) H) as [Hd' [Hkeys' Hwf']].
  split; [ | split ].
  - rewrite Hd', Hd. ring.
  - intros id Hin. destruct (Hkeys' id Hin) as [ Hin' | Hin' ];
      [ left; exact Hin' | right; apply Hkeys; exact Hin' ].
  - exact Hwf'.
Qed.

(* --- Resolvents. --- *)

Definition int_eq_dec : forall x y : int, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (x =? y)%sint63 eqn:E.
  - left. apply eqb_int. exact E.
  - right. apply eqb_int_false. exact E.
Defined.

(* [scaled k f] multiplies the constant and every coefficient of [f] by
   [k], exactly. *)
Lemma scaled_spec : forall k f c ts,
  scaled k f = Some (c, ts) ->
  Int64.to_Z c = Int64.to_Z k * to_Z f.(Affine.const)
  /\ map fst ts = map fst f.(Affine.terms)
  /\ (forall id, Int64.to_Z (coeff64 id ts)
                 = Int64.to_Z k * to_Z (Affine.coeff id f)).
Proof.
  unfold scaled. intros k f c ts H.
  destruct (mul_ovf64 _ _) as [ c' | ] eqn:Hc; [ | discriminate ].
  destruct (map_opt _ _) as [ ts' | ] eqn:Hts; [ | discriminate ].
  injection H as <- <-.
  split; [ | split ].
  - apply mul_ovf64_spec in Hc. rewrite Hc, Int64.of_int_spec. reflexivity.
  - eapply map_opt_keys. exact Hts.
  - intros id. unfold coeff64, Affine.coeff, coeff_gen.
    pose proof (map_opt_assoc _ _ _ Hts id) as Ha. revert Ha.
    destruct (assoc_opt id f.(Affine.terms)) as [ c0 | ]; intro Ha.
    + destruct Ha as [d [Hd ->]]. apply mul_ovf64_spec in Hd.
      rewrite Hd, Int64.of_int_spec. reflexivity.
    + rewrite Ha, Int64.to_Z_zero, to_Z_zero. ring.
Qed.

(* What a resolvent is: a form [r] whose coefficients are, up to a positive
   factor [g], the combination [cn * p + cp * n], and which holds whenever
   that combination is non-negative. *)
Lemma resolvent_spec : forall cp cn p n r,
  wf p -> wf n -> resolvent cp cn p n = Some r ->
  wf r
  /\ (forall id, In id (map fst r.(Affine.terms)) ->
        In id (map fst p.(Affine.terms)) \/ In id (map fst n.(Affine.terms)))
  /\ (exists g, 0 < g /\
        forall id,
          g * to_Z (Affine.coeff id r)
          = to_Z cn * to_Z (Affine.coeff id p)
            + to_Z cp * to_Z (Affine.coeff id n))
  /\ (forall rho,
        0 <= to_Z cn * denote rho p + to_Z cp * denote rho n ->
        0 <= denote rho r).
Proof.
  intros cp cn p n r Hp Hn H. unfold resolvent in H.
  destruct (scaled (Int64.of_int cn) p) as [ [pc pterms] | ] eqn:Hsp;
    [ | discriminate ].
  destruct (scaled (Int64.of_int cp) n) as [ [nc nterms] | ] eqn:Hsn;
    [ | discriminate ].
  destruct (scaled_spec _ _ _ _ Hsp) as [Hpc [Hpkeys Hpcoeff]].
  destruct (scaled_spec _ _ _ _ Hsn) as [Hnc [Hnkeys Hncoeff]].
  rewrite Int64.of_int_spec in Hpc, Hnc, Hpcoeff, Hncoeff.
  set (ids := sort_uniq (map fst pterms ++ map fst nterms)) in *.
  assert (Hnd : NoDup ids) by apply sort_uniq_NoDup.
  assert (Hids : forall x, In x ids <->
                   In x (map fst p.(Affine.terms))
                   \/ In x (map fst n.(Affine.terms))).
  { intros x. unfold ids.
    rewrite sort_uniq_In, in_app_iff, Hpkeys, Hnkeys. reflexivity. }
  change (filter_map_opt _ ids)
    with (merge_terms
            (fun id => add_ovf64 (coeff64 id pterms) (coeff64 id nterms))
            (fun c => Int64.equal c Int64.zero) ids) in H.
  destruct (merge_terms _ _ ids) as [ ts | ] eqn:Hts; [ | discriminate ].
  destruct (add_ovf64 pc nc) as [ c | ] eqn:Hc; [ | discriminate ].
  apply add_ovf64_spec in Hc. rewrite Hpc, Hnc in Hc.
  (* The merged coefficient of each atom. *)
  set (m := fun id => to_Z cn * to_Z (Affine.coeff id p)
                      + to_Z cp * to_Z (Affine.coeff id n)).
  assert (Hm : forall id, In id ids ->
            Int64.to_Z (coeff64 id ts) = m id
            /\ (In id (map fst ts) <-> m id <> 0)).
  { intros id Hid.
    destruct (merge_coeff _ _ Int64.zero ids ts Hnd Hts id Hid)
      as [c0 [Hc0 [Hcoeff Hin]]].
    apply add_ovf64_spec in Hc0. rewrite Hpcoeff, Hncoeff in Hc0.
    unfold coeff64. rewrite Hcoeff, Hin.
    destruct (Int64.equal c0 Int64.zero) eqn:Hz.
    - apply Int64.equal_spec in Hz. rewrite Int64.to_Z_zero in Hz.
      split; [ rewrite Int64.to_Z_zero; unfold m; lia | ].
      split; [ discriminate | intros Hne; exfalso; apply Hne; unfold m; lia ].
    - apply Int64.equal_false in Hz. rewrite Int64.to_Z_zero in Hz.
      split; [ unfold m; lia | ].
      split; [ intros _; unfold m; lia | reflexivity ]. }
  assert (Hm0 : forall id, ~ In id ids -> m id = 0 /\ ~ In id (map fst ts)).
  { intros id Hid. split.
    - unfold m, Affine.coeff. rewrite !coeff_gen_not_in;
        [ rewrite to_Z_zero; ring | | ];
        intros Hin; apply Hid; apply Hids; tauto.
    - intros Hin. apply Hid. eapply merge_keys; [ exact Hts | exact Hin ]. }
  (* The combination, as a sum over [ids]. *)
  assert (Hsum : forall rho,
            to_Z cn * denote rho p + to_Z cp * denote rho n
            = Int64.to_Z c + sum_ids (fun id => m id * rho id) ids).
  { intros rho. unfold denote. rewrite Hc.
    rewrite (sum_ids_ext _
               (fun id => to_Z cn * (to_Z (Affine.coeff id p) * rho id)
                          + to_Z cp * (to_Z (Affine.coeff id n) * rho id)))
      by (intros; unfold m; ring).
    rewrite sum_ids_add, !sum_ids_scale. unfold Affine.coeff.
    rewrite !(sum_ids_coeff to_Z zero rho)
      by first [ reflexivity | assumption | (intros x Hx; apply Hids; tauto) ].
    ring. }
  destruct ts as [ | t0 ts' ].
  - (* No atom left: a constant inequality, decided by the sign of [c]. *)
    injection H as <-.
    assert (Hm_all : forall id, m id = 0).
    { intros id. destruct (in_dec int_eq_dec id ids) as [ Hin | Hnin ].
      - destruct (Hm id Hin) as [_ Hiff].
        destruct (Z.eq_dec (m id) 0) as [ E | NE ]; [ exact E | ].
        exfalso. apply Hiff. exact NE.
      - apply Hm0. exact Hnin. }
    split; [ | split; [ | split ] ].
    + constructor.
    + intros id Hin. contradiction.
    + exists 1. split; [ lia | ]. intros id.
      specialize (Hm_all id). unfold m in Hm_all. rewrite Hm_all.
      unfold Affine.coeff, coeff_gen. cbn [Affine.terms assoc_opt].
      rewrite to_Z_zero. ring.
    + intros rho Hpos. rewrite Hsum in Hpos.
      rewrite sum_ids_zero in Hpos by (intros; rewrite Hm_all; ring).
      assert (Hge : (zero <=? Int64.compare c Int64.zero)%sint63 = true)
        by (apply Int64.compare_ge; rewrite Int64.to_Z_zero; lia).
      unfold denote. rewrite Hge. cbn [Affine.const Affine.terms].
      change (denote_terms to_Z rho []) with 0. rewrite to_Z_zero. lia.
  - (* Normalise by the gcd of the coefficients. *)
    cbv zeta in H.
    set (g0 := fold_left (fun g '(_, c) => gcd64 g (Int64.abs c)) Int64.zero
                 (t0 :: ts')) in H.
    set (g := if (zero <? Int64.compare g0 Int64.one)%sint63 then g0
              else Int64.one) in H.
    assert (Hg : 0 < Int64.to_Z g
                 /\ forall id c0, In (id, c0) (t0 :: ts') ->
                      (Int64.to_Z g | Int64.to_Z c0)).
    { unfold g. destruct (zero <? Int64.compare g0 Int64.one)%sint63 eqn:Hgt.
      - apply Int64.compare_gt in Hgt. rewrite Int64.to_Z_one in Hgt.
        split; [ lia | ]. intros id c0 Hin. unfold g0.
        eapply fold_gcd_divides. exact Hin.
      - rewrite Int64.to_Z_one. split; [ lia | ]. intros. apply Z.divide_1_l. }
    clearbody g.
    destruct (to_int_ovf (fdiv64 c g)) as [ k | ] eqn:Hk; [ | discriminate ].
    destruct (map_opt _ (t0 :: ts')) as [ rts | ] eqn:Hrts; [ | discriminate ].
    injection H as <-.
    apply to_int_ovf_spec in Hk. rewrite fdiv64_spec in Hk by lia.
    pose proof (map_opt_keys _ _ _ Hrts) as Hkeys.
    assert (Hcoeff : forall id,
              Int64.to_Z g
              * to_Z (Affine.coeff id
                        {| Affine.const := k; Affine.terms := rts |})
              = m id).
    { intros id. unfold Affine.coeff, coeff_gen. cbn [Affine.terms].
      pose proof (map_opt_assoc _ _ _ Hrts id) as Ha. revert Ha.
      destruct (assoc_opt id (t0 :: ts')) as [ c0 | ] eqn:Ha0; intro Ha.
      - destruct Ha as [d [Hd Hd']]. rewrite Hd'.
        apply to_int_ovf_spec in Hd. rewrite Hd.
        assert (Hdiv : (Int64.to_Z g | Int64.to_Z c0))
          by (apply (proj2 Hg id c0); apply assoc_opt_In; exact Ha0).
        rewrite div_exact64 by first [ lia | exact Hdiv ].
        destruct Hdiv as [q Hq]. rewrite Hq, Z.div_mul by lia.
        assert (Hin : In id ids).
        { eapply merge_keys; [ exact Hts | ].
          apply assoc_opt_In in Ha0. apply (in_map fst) in Ha0. exact Ha0. }
        destruct (Hm id Hin) as [Hm1 _].
        unfold coeff64, coeff_gen in Hm1. rewrite Ha0 in Hm1.
        rewrite <- Hm1, Hq. ring.
      - rewrite Ha, to_Z_zero.
        assert (Hnot : ~ In id (map fst (t0 :: ts'))).
        { intros Hin. destruct (assoc_opt_Some id (t0 :: ts') Hin) as [c0 E].
          congruence. }
        destruct (in_dec int_eq_dec id ids) as [ Hin | Hnin ].
        + destruct (Hm id Hin) as [_ Hiff].
          destruct (Z.eq_dec (m id) 0) as [ E | NE ]; [ rewrite E; ring | ].
          exfalso. apply Hnot. apply Hiff. exact NE.
        + destruct (Hm0 id Hnin) as [E _]. rewrite E. ring. }
    split; [ | split; [ | split ] ].
    + unfold wf. cbn [Affine.terms]. rewrite Hkeys.
      eapply merge_NoDup; [ exact Hnd | exact Hts ].
    + intros id Hin. cbn [Affine.terms] in Hin. rewrite Hkeys in Hin.
      apply Hids.
      eapply merge_keys; [ exact Hts | exact Hin ].
    + exists (Int64.to_Z g). split; [ lia | exact Hcoeff ].
    + intros rho Hpos. rewrite Hsum in Hpos.
      assert (Hdt : sum_ids (fun id => m id * rho id) ids
                    = Int64.to_Z g * denote_terms to_Z rho rts).
      { rewrite <- (sum_ids_coeff to_Z zero rho rts ids);
          [ | reflexivity | | exact Hnd | ].
        - rewrite <- sum_ids_scale. apply sum_ids_ext. intros id _.
          rewrite <- (Hcoeff id). unfold Affine.coeff. cbn [Affine.terms]. ring.
        - rewrite Hkeys. eapply merge_NoDup; [ exact Hnd | exact Hts ].
        - intros x Hx. rewrite Hkeys in Hx.
          eapply merge_keys; [ exact Hts | exact Hx ]. }
      unfold denote. cbn [Affine.const Affine.terms]. rewrite Hk.
      rewrite Hdt in Hpos.
      assert (Hlow : - denote_terms to_Z rho rts
                     <= Int64.to_Z c / Int64.to_Z g).
      { apply Z.div_le_lower_bound; [ lia | ].
        replace (Int64.to_Z g * - denote_terms to_Z rho rts)
          with (- (Int64.to_Z g * denote_terms to_Z rho rts)) by ring.
        lia. }
      lia.
Qed.

(* ======================================================================== *)
(* Part 4: soundness of [feasible] and [entails]                            *)
(* ======================================================================== *)

(* --- Every constructor of [Affine] builds a well-formed form. --- *)

Lemma add_const_wf : forall f c, wf f -> wf (Affine.add_const f c).
Proof. intros f c H. exact H. Qed.

Lemma add_wf : forall a b, wf (Affine.add a b).
Proof.
  intros a b. unfold wf, Affine.add. cbv zeta. cbn [Affine.terms].
  apply filter_map_NoDup_keys; [ | apply sort_uniq_NoDup ].
  intros id p Hp. cbv beta zeta in Hp.
  destruct (_ =? zero)%sint63; [ discriminate | ].
  injection Hp as <-. reflexivity.
Qed.

Lemma scale_wf : forall k f, wf f -> wf (Affine.scale k f).
Proof.
  intros k f H. unfold wf, Affine.scale.
  destruct (k =? zero)%sint63; [ constructor | ].
  cbn [Affine.terms]. rewrite map_map.
  erewrite map_ext; [ exact H | ]. intros [id c]. reflexivity.
Qed.

Lemma neg_wf : forall f, wf f -> wf (Affine.neg f).
Proof. intros. apply scale_wf. assumption. Qed.

Lemma sub_wf : forall a b, wf (Affine.sub a b).
Proof. intros. apply add_wf. Qed.

(* --- One elimination step. --- *)

(* Eliminating [v] keeps the forms well-formed and their atoms among the
   input atoms, gives every output a zero coefficient of [v], keeps zero any
   coefficient that was zero throughout the input, and preserves truth: a
   valuation satisfying the input satisfies the output. *)
Lemma elim_spec : forall v ineqs out,
  Forall wf ineqs -> elim v ineqs = Some out ->
  Forall wf out
  /\ (forall S, (forall f, In f ineqs -> incl (map fst f.(Affine.terms)) S) ->
        forall f, In f out -> incl (map fst f.(Affine.terms)) S)
  /\ (forall f, In f out -> to_Z (Affine.coeff v f) = 0)
  /\ (forall id, (forall f, In f ineqs -> to_Z (Affine.coeff id f) = 0) ->
        forall f, In f out -> to_Z (Affine.coeff id f) = 0)
  /\ (forall rho, holds_all rho ineqs -> holds_all rho out).
Proof.
  intros v ineqs out Hwf H. unfold elim in H.
  destruct (zero <? compare_length_with ineqs max_ineqs)%sint63;
    [ discriminate | ].
  injection H as <-. cbv beta zeta.
  rewrite Forall_forall in Hwf.
  set (pos := filter (fun f => (zero <? Affine.coeff v f)%sint63) ineqs).
  set (neg := filter (fun f => (Affine.coeff v f <? zero)%sint63) ineqs).
  set (zc := filter (fun f => (Affine.coeff v f =? zero)%sint63) ineqs).
  set (res := concat_map _ pos).
  (* Each output is an input with a zero coefficient of [v], or the resolvent
     of an input pair with coefficients of opposite signs. *)
  assert (Hcase : forall f, In f (rev_append zc res) ->
            (In f ineqs /\ Affine.coeff v f = zero)
            \/ (exists p n cn, In p ineqs /\ In n ineqs
                  /\ 0 < to_Z (Affine.coeff v p)
                  /\ to_Z (Affine.coeff v n) < 0
                  /\ to_Z cn = - to_Z (Affine.coeff v n)
                  /\ resolvent (Affine.coeff v p) cn p n = Some f)).
  { intros f Hin. apply in_rev_append in Hin as [ Hin | Hin ].
    - left. apply filter_In in Hin as [Hin Hz]. apply eqb_int in Hz. auto.
    - right. unfold res, concat_map in Hin.
      apply in_flat_map in Hin as [p [Hp Hin]].
      apply filter_In in Hp as [Hp Hpos]. apply ltb_int in Hpos.
      apply filter_map_In in Hin as [n [Hn Hres]]. cbv beta in Hres.
      apply filter_In in Hn as [Hn Hneg]. apply ltb_int in Hneg.
      rewrite to_Z_zero in Hpos, Hneg.
      destruct (neg_ovf (Affine.coeff v n)) as [ cn | ] eqn:Hcn;
        [ | discriminate ].
      cbv iota in Hres. apply neg_ovf_spec in Hcn.
      exists p, n, cn. tauto. }
  split; [ | split; [ | split; [ | split ] ] ].
  - apply Forall_forall. intros f Hin.
    destruct (Hcase f Hin)
      as [ [Hin' _] | [p [n [cn [Hp [Hn [_ [_ [_ Hres]]]]]]]] ].
    + apply Hwf. exact Hin'.
    + exact (proj1 (resolvent_spec _ _ _ _ _ (Hwf p Hp) (Hwf n Hn) Hres)).
  - intros S HS f Hin id Hid.
    destruct (Hcase f Hin)
      as [ [Hin' _] | [p [n [cn [Hp [Hn [_ [_ [_ Hres]]]]]]]] ].
    + apply (HS f Hin' id Hid).
    + destruct (resolvent_spec _ _ _ _ _ (Hwf p Hp) (Hwf n Hn) Hres)
        as [_ [Hkeys _]].
      destruct (Hkeys id Hid) as [ Hid' | Hid' ].
      * apply (HS p Hp id Hid').
      * apply (HS n Hn id Hid').
  - intros f Hin.
    destruct (Hcase f Hin)
      as [ [_ Hz] | [p [n [cn [Hp [Hn [Hpos [Hneg [Hcn Hres]]]]]]]] ].
    + rewrite Hz. apply to_Z_zero.
    + destruct (resolvent_spec _ _ _ _ _ (Hwf p Hp) (Hwf n Hn) Hres)
        as [_ [_ [[g [Hg Hcoeff]] _]]].
      specialize (Hcoeff v). rewrite Hcn in Hcoeff.
      assert (E : g * to_Z (Affine.coeff v f) = 0) by (rewrite Hcoeff; ring).
      apply Z.mul_eq_0 in E as [ E | E ]; lia.
  - intros id Hz f Hin.
    destruct (Hcase f Hin)
      as [ [Hin' _] | [p [n [cn [Hp [Hn [_ [_ [_ Hres]]]]]]]] ].
    + apply Hz. exact Hin'.
    + destruct (resolvent_spec _ _ _ _ _ (Hwf p Hp) (Hwf n Hn) Hres)
        as [_ [_ [[g [Hg Hcoeff]] _]]].
      specialize (Hcoeff id). rewrite (Hz p Hp), (Hz n Hn) in Hcoeff.
      assert (E : g * to_Z (Affine.coeff id f) = 0) by lia.
      apply Z.mul_eq_0 in E as [ E | E ]; lia.
  - intros rho Hholds. unfold holds_all in *. rewrite Forall_forall in *.
    intros f Hin.
    destruct (Hcase f Hin)
      as [ [Hin' _] | [p [n [cn [Hp [Hn [Hpos [Hneg [Hcn Hres]]]]]]]] ].
    + apply Hholds. exact Hin'.
    + destruct (resolvent_spec _ _ _ _ _ (Hwf p Hp) (Hwf n Hn) Hres)
        as [_ [_ [_ Hsound]]].
      apply Hsound. rewrite Hcn.
      pose proof (Hholds p Hp). pose proof (Hholds n Hn). unfold holds in *.
      apply Z.add_nonneg_nonneg; apply Z.mul_nonneg_nonneg; lia.
Qed.

(* --- Eliminating every atom in turn. --- *)

(* The same, for a sequence of eliminations: every eliminated atom, and
   every atom that was absent throughout the input, has a zero coefficient in
   every output. *)
Lemma elim_all_spec : forall atoms ineqs out,
  Forall wf ineqs -> elim_all atoms ineqs = Some out ->
  Forall wf out
  /\ (forall S, (forall f, In f ineqs -> incl (map fst f.(Affine.terms)) S) ->
        forall f, In f out -> incl (map fst f.(Affine.terms)) S)
  /\ (forall id,
        In id atoms \/ (forall f, In f ineqs -> to_Z (Affine.coeff id f) = 0) ->
        forall f, In f out -> to_Z (Affine.coeff id f) = 0)
  /\ (forall rho, holds_all rho ineqs -> holds_all rho out).
Proof.
  induction atoms as [ | v atoms IH ]; intros ineqs out Hwf H.
  - injection H as <-. split; [ exact Hwf | split; [ | split ] ].
    + intros S HS f Hin. apply HS. exact Hin.
    + intros id [ Hid | Hz ] f Hin; [ contradiction | apply Hz; exact Hin ].
    + intros rho Hh. exact Hh.
  - cbn [elim_all] in H.
    destruct (elim v ineqs) as [ mid | ] eqn:He; [ | discriminate ].
    destruct (elim_spec v ineqs mid Hwf He) as [Hwf1 [Hkeys1 [Hv1 [Hz1 Hh1]]]].
    destruct (IH mid out Hwf1 H) as [Hwf2 [Hkeys2 [Hz2 Hh2]]].
    split; [ exact Hwf2 | split; [ | split ] ].
    + intros S HS. apply Hkeys2. apply Hkeys1. exact HS.
    + intros id Hid f Hin. apply (Hz2 id); [ | exact Hin ].
      destruct Hid as [ [ -> | Hid ] | Hz ].
      * right. exact Hv1.
      * left. exact Hid.
      * right. apply Hz1. exact Hz.
    + intros rho Hh. apply Hh2. apply Hh1. exact Hh.
Qed.

(* --- The theorems. --- *)

(* [feasible] never wrongly reports an infeasible system: if it answers
   [false], no integer valuation of the atoms satisfies every inequality.
   (It may answer [true] for an infeasible system: on the size limits, on
   an overflow, or because Fourier-Motzkin elimination is only complete over
   the rationals.) *)
Theorem feasible_sound : forall ineqs,
  Forall wf ineqs -> feasible ineqs = false ->
  forall rho, ~ holds_all rho ineqs.
Proof.
  intros ineqs Hwf Hf rho Hholds. unfold feasible in Hf. cbv zeta in Hf.
  set (atoms := sort_uniq _) in Hf.
  destruct (zero <? compare_length_with atoms max_atoms)%sint63;
    [ discriminate | ].
  destruct (elim_all atoms ineqs) as [ reduced | ] eqn:He; [ | discriminate ].
  cbv iota in Hf.
  destruct (elim_all_spec atoms ineqs reduced Hwf He)
    as [Hwf' [Hkeys [Hzero Hpres]]].
  specialize (Hpres rho Hholds). unfold holds_all in Hpres.
  rewrite Forall_forall in Hwf', Hpres.
  rewrite <- not_true_iff_false in Hf. apply Hf.
  apply forallb_forall. intros f Hin.
  assert (Hatoms : incl (map fst f.(Affine.terms)) atoms).
  { apply (Hkeys atoms); [ | exact Hin ]. intros f0 Hf0 x Hx.
    unfold atoms. apply sort_uniq_In. unfold concat_map. apply in_flat_map.
    exists f0. split; [ exact Hf0 | exact Hx ]. }
  assert (Hd : denote_terms to_Z rho f.(Affine.terms) = 0).
  { apply denote_terms_zero; [ apply Hwf'; exact Hin | ].
    intros id Hid. exact (Hzero id (or_introl (Hatoms id Hid)) f Hin). }
  specialize (Hpres f Hin). unfold holds, denote in Hpres. rewrite Hd in Hpres.
  apply leb_int. rewrite to_Z_zero. lia.
Qed.

(* [entails] never wrongly reports an entailment: if it answers [true], every
   integer valuation satisfying the facts satisfies the goal. *)
Theorem entails_sound : forall facts goal,
  Forall wf facts -> wf goal -> entails facts goal = true ->
  forall rho, holds_all rho facts -> 0 <= denote rho goal.
Proof.
  intros facts goal Hwf Hwfg He rho Hfacts.
  unfold entails in He. cbv zeta in He.
  destruct (Affine.scale_checked minus_one goal) as [ ng | ] eqn:Hng;
    [ | discriminate ].
  cbv iota in He.
  destruct (Affine.add_const_checked ng minus_one) as [ ng' | ] eqn:Hng';
    [ | discriminate ].
  cbv iota in He. apply negb_true_iff in He.
  destruct (scale_checked_spec rho _ _ _ Hng) as [Hd1 [_ Hwf1]].
  destruct (add_const_checked_spec rho _ _ _ Hng') as [Hd2 [_ Hwf2]].
  rewrite to_Z_minus_one in Hd1, Hd2.
  assert (Hwf' : Forall wf (ng' :: facts))
    by (constructor; [ auto | exact Hwf ]).
  pose proof (feasible_sound (ng' :: facts) Hwf' He rho) as Hinf.
  destruct (Z_le_gt_dec 0 (denote rho goal)) as [ Hle | Hgt ]; [ exact Hle | ].
  exfalso. apply Hinf. constructor; [ | exact Hfacts ].
  unfold holds. rewrite Hd2, Hd1. lia.
Qed.

