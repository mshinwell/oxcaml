(* A Rocq model of [backend/ssa/loop/affine_expr.ml].

   See the reading guide at the top of LoopComparisons.v for the Rocq
   vocabulary and the layout of the shared files, and FourierMotzkin.v for
   the model of [Affine] that this one builds on. As there, this file has
   four parts: (1) a transcription of the OCaml, (2) the intended meaning,
   (3) stepping-stone lemmas, (4) the theorems. Parts 1 and 2 are the part
   to check by eye.

   The OCaml's [to_affine] raises [Overflow] (through the checked [Affine]
   operations) where a coefficient would wrap; here it returns an [option],
   with [None] standing for the exception (see OcamlOption.v).

   The results, in part 4:

   - [Range]: each operation on value ranges contains the exact result when
     its arguments are in the given ranges, and a range only ever holds
     64-bit values ([add_sound], [scale_sound], ...). This is what lets
     [Affine_ssa] certify that a decomposition is machine-exact.

   - [to_affine_sound]: the affine form returned for an expression has the
     expression's value (over unbounded integers), and every side fact is
     true, provided the atoms standing for the atomized shifts and ors have
     the values the machine gives them ([consistent] below says what that
     means, and is what [Affine_ssa] guarantees). [to_affine_wf] adds that
     the forms are well-formed, as [Fourier_motzkin.entails] needs.

   Trusted parts, beyond those of FourierMotzkin.v: the [Int64] shifts and
   negation, the exactness of [Int64.to_int] on values that fit an [int]
   (axioms in OcamlInt64.v), and the extraction of [lsl] (OcamlExtract.v). *)

From Stdlib Require Import ZArith Lia Bool List Zbitwise.
From OxcamlStdlib Require Import OcamlOption OcamlInt OcamlInt64 OcamlList.
From OxcamlLoop Require Import FourierMotzkin.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: transcription of the OCaml                                       *)
(* ======================================================================== *)

Local Open Scope sint63_scope.

(* OCaml [Affine_expr.t]. The OCaml's inline records ([Shr_atom of { atom;
   arg; bits }]) are positional arguments here, in the same order. *)
Inductive t : Type :=
  | Const (c : int)
  | Atom (id : int)
  | Add (a b : t)
  | Sub (a b : t)
  | Scale (k : int) (a : t)
  | Shr_atom (atom : int) (arg : t) (bits : int)
  | Lsr_atom (atom : int) (bits : int)
  | Or_atom (atom : int) (arg : t) (mask : int).

Module Range.
  Record t := { lo : Int64.t; hi : Int64.t }.

  Definition full : t := {| lo := Int64.min_int; hi := Int64.max_int |}.

  Definition const (c : int) : t :=
    let c := Int64.of_int c in {| lo := c; hi := c |}.

  Definition shr_signed (bits : int) : t :=
    {| lo := Int64.shift_right Int64.min_int bits;
       hi := Int64.shift_right Int64.max_int bits |}.

  Definition shr_logical (bits : int) : t :=
    if bits <=? zero
    then full
    else {| lo := Int64.zero;
            hi := Int64.shift_right_logical Int64.minus_one bits |}.

  (* The OCaml's [add64] and [mul64] are copies of the checked 64-bit
     arithmetic of fourier_motzkin.ml, modelled in FourierMotzkin.v. *)
  Definition add64 : Int64.t -> Int64.t -> option Int64.t := add_ovf64.
  Definition mul64 : Int64.t -> Int64.t -> option Int64.t := mul_ovf64.

  Definition add (a b : t) : option t :=
    match add64 a.(lo) b.(lo), add64 a.(hi) b.(hi) with
    | Some lo, Some hi => Some {| lo := lo; hi := hi |}
    | _, _ => None
    end.

  Definition neg (r : t) : option t :=
    if Int64.equal r.(lo) Int64.min_int
    then None
    else Some {| lo := Int64.neg r.(hi); hi := Int64.neg r.(lo) |}.

  (* OCaml [Option.bind (neg b) (add a)]. *)
  Definition sub (a b : t) : option t :=
    let* nb := neg b in add a nb.

  (* OCaml [Option.map (fun hi -> ...) (add64 ...)]. *)
  Definition or_mask (mask : int) (r : t) : option t :=
    if mask <? zero
    then None
    else
      let* hi := add64 r.(hi) (Int64.of_int mask) in
      Some {| lo := r.(lo); hi := hi |}.

  Definition scale (k : int) (r : t) : option t :=
    if k =? zero
    then Some {| lo := Int64.zero; hi := Int64.zero |}
    else
      let k := Int64.of_int k in
      match mul64 k r.(lo), mul64 k r.(hi) with
      | Some a, Some b =>
        if Int64.compare a b <=? zero
        then Some {| lo := a; hi := b |}
        else Some {| lo := b; hi := a |}
      | _, _ => None
      end.
End Range.

(* The [64] of [64 - bits]: the width of a register. *)
Definition word_bits : int := 64.

(* OCaml [shr_range_facts ~signed ~atom ~bits]. *)
Definition shr_range_facts (signed : bool) (atom bits : int)
    : list Affine.t :=
  if signed
  then
    if bits <? one
    then []
    else
      let hi := Int64.to_int (Int64.shift_right Int64.max_int bits) in
      let upper :=
        Affine.add_const (Affine.scale minus_one (Affine.var atom)) hi
      in
      if two <=? bits
      then
        let lo := Int64.to_int (Int64.shift_right Int64.min_int bits) in
        [upper; Affine.add_const (Affine.var atom) (- lo)]
      else [upper]
  else if bits <? one
  then []
  else
    let lower := Affine.var atom in
    if two <=? bits
    then
      let hi := (one << (word_bits - bits)) - one in
      [Affine.add_const (Affine.scale minus_one (Affine.var atom)) hi; lower]
    else [lower].

(* OCaml [to_affine]. Each checked operation is a [let*] step; where the
   OCaml nests them in one expression, the steps are written out in the
   order the values are needed. *)
Fixpoint to_affine (e : t) : option (Affine.t * list Affine.t) :=
  match e with
  | Const c => Some (Affine.constant c, [])
  | Atom id => Some (Affine.var id, [])
  | Add a b =>
    let* '(fa, sa) := to_affine a in
    let* '(fb, sb) := to_affine b in
    let* f := Affine.add_checked fa fb in
    Some (f, sa ++ sb)
  | Sub a b =>
    let* '(fa, sa) := to_affine a in
    let* '(fb, sb) := to_affine b in
    let* nfb := Affine.scale_checked minus_one fb in
    let* f := Affine.add_checked fa nfb in
    Some (f, sa ++ sb)
  | Scale k a =>
    let* '(fa, sa) := to_affine a in
    let* f := Affine.scale_checked k fa in
    Some (f, sa)
  | Shr_atom atom arg bits =>
    let* '(fa, sa) := to_affine arg in
    let v := Affine.var atom in
    let pow := one << bits in
    (* [fa - pow * v >= 0] *)
    let* m := Affine.scale_checked (- pow) v in
    let* s1 := Affine.add_checked fa m in
    (* [pow * v + (pow - 1) - fa >= 0] *)
    let* p := Affine.scale_checked pow v in
    let* pc := Affine.add_const_checked p (pow - one) in
    let* nfa := Affine.scale_checked minus_one fa in
    let* s2 := Affine.add_checked pc nfa in
    Some (v, s1 :: s2 :: (shr_range_facts true atom bits ++ sa))
  | Lsr_atom atom bits =>
    Some (Affine.var atom, shr_range_facts false atom bits)
  | Or_atom atom arg mask =>
    let* '(fa, sa) := to_affine arg in
    let v := Affine.var atom in
    (* [v - fa >= 0] *)
    let* nfa := Affine.scale_checked minus_one fa in
    let* s1 := Affine.add_checked v nfa in
    (* [fa + mask - v >= 0] *)
    let* fm := Affine.add_const_checked fa mask in
    let* nv := Affine.scale_checked minus_one v in
    let* s2 := Affine.add_checked fm nv in
    Some (v, s1 :: s2 :: sa)
  end.

(* ======================================================================== *)
(* Part 2: the intended meaning                                             *)
(* ======================================================================== *)

Local Open Scope Z_scope.

(* The value of an expression over unbounded integers, [rho] giving the
   atoms' values. The atomized shifts and ors are atoms: their value is
   whatever [rho] says, and their relation to their argument is only
   expressed by the side facts of [to_affine]. *)
Fixpoint eval (rho : valuation) (e : t) : Z :=
  match e with
  | Const c => to_Z c
  | Atom id => rho id
  | Add a b => eval rho a + eval rho b
  | Sub a b => eval rho a - eval rho b
  | Scale k a => to_Z k * eval rho a
  | Shr_atom atom _ _ => rho atom
  | Lsr_atom atom _ => rho atom
  | Or_atom atom _ _ => rho atom
  end.

(* A range contains an integer. *)
Definition in_range (r : Range.t) (z : Z) : Prop :=
  Int64.to_Z r.(Range.lo) <= z <= Int64.to_Z r.(Range.hi).

(* What [Affine_ssa] guarantees about the atoms standing for shifts and
   ors: each has the value the machine computes from the exact value of its
   argument, that value fitting a 64-bit register (which [Affine_ssa]
   certifies with [Range] before it builds the node). [bits] and [mask] are
   within the ranges [Affine_ssa] produces them in (its shift amounts are
   below 16; here the bound is the one under which [1 lsl bits] is
   [2^bits]). Over unbounded integers:

   - [arg asr bits] is [arg / 2^bits], rounding towards minus infinity;
   - [r lsr bits] is [unsigned64 r / 2^bits], for some register value [r]
     (the argument of a logical shift is not kept in the expression);
   - [arg lor mask] is the two's-complement [Z.lor]. *)
Fixpoint consistent (rho : valuation) (e : t) : Prop :=
  match e with
  | Const _ | Atom _ => True
  | Add a b | Sub a b => consistent rho a /\ consistent rho b
  | Scale _ a => consistent rho a
  | Shr_atom atom arg bits =>
    consistent rho arg
    /\ 0 <= to_Z bits <= 61
    /\ in_int64 (eval rho arg)
    /\ rho atom = eval rho arg / 2 ^ to_Z bits
  | Lsr_atom atom bits =>
    1 <= to_Z bits <= 63
    /\ exists r, in_int64 r /\ rho atom = unsigned64 r / 2 ^ to_Z bits
  | Or_atom atom arg mask =>
    consistent rho arg
    /\ 0 <= to_Z mask
    /\ rho atom = Z.lor (eval rho arg) (to_Z mask)
  end.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros n Hn. apply Z.pow_pos_nonneg; lia. Qed.

(* [2^1 <= 2^n <= 2^63] for [1 <= n <= 63], with the powers as numerals, so
   that [lia] can use them. *)
Lemma pow2_bounds : forall n, 0 <= n <= 63 -> 1 <= 2 ^ n <= two63.
Proof.
  intros n Hn. rewrite two63_pow. split.
  - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia.
  - apply Z.pow_le_mono_r; lia.
Qed.

Lemma pow2_ge_2 : forall n, 1 <= n -> 2 <= 2 ^ n.
Proof. intros n Hn. change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia. Qed.

Lemma pow2_ge_4 : forall n, 2 <= n -> 4 <= 2 ^ n.
Proof. intros n Hn. change 4 with (2 ^ 2) at 1. apply Z.pow_le_mono_r; lia. Qed.

(* --- The two forms of a range fact. --- *)

Lemma upper_denote : forall rho atom hi,
  denote rho (Affine.add_const (Affine.scale minus_one (Affine.var atom)) hi)
  = to_Z hi - rho atom.
Proof.
  intros rho atom hi. unfold Affine.add_const, Affine.scale, Affine.var.
  change (minus_one =? zero)%sint63 with false. cbv iota.
  cbn [map Affine.const Affine.terms].
  rewrite denote_record, denote_terms_cons.
  change (denote_terms to_Z rho []) with 0.
  change (zero * minus_one)%sint63 with zero.
  change (one * minus_one)%sint63 with minus_one.
  rewrite Sint63.to_Z_add
    by (rewrite to_Z_zero, to_Z_min_int, to_Z_max_int;
        pose proof (int_bounds hi); lia).
  rewrite to_Z_zero, to_Z_minus_one. ring.
Qed.

Lemma lower_denote : forall rho atom c,
  denote rho (Affine.add_const (Affine.var atom) c) = rho atom + to_Z c.
Proof.
  intros rho atom c. unfold Affine.add_const, Affine.var.
  cbn [Affine.const Affine.terms].
  rewrite denote_record, denote_terms_cons.
  change (denote_terms to_Z rho []) with 0.
  rewrite Sint63.to_Z_add
    by (rewrite to_Z_zero, to_Z_min_int, to_Z_max_int;
        pose proof (int_bounds c); lia).
  rewrite to_Z_zero, to_Z_one. ring.
Qed.

(* --- The range facts of an atomized shift. --- *)

Lemma shr_range_facts_wf : forall signed atom bits,
  Forall wf (shr_range_facts signed atom bits).
Proof.
  intros signed atom bits. unfold shr_range_facts.
  destruct signed; destruct (bits <? one)%sint63; try apply Forall_nil;
    cbv zeta; destruct (two <=? bits)%sint63;
    repeat (apply Forall_cons || apply Forall_nil);
    auto using add_const_wf, scale_wf, var_wf.
Qed.

Lemma shr_range_facts_signed_sound : forall rho atom bits x,
  0 <= to_Z bits <= 63 -> in_int64 x -> rho atom = x / 2 ^ to_Z bits ->
  holds_all rho (shr_range_facts true atom bits).
Proof.
  intros rho atom bits x Hb Hx Hatom. unfold shr_range_facts.
  destruct (bits <? one)%sint63 eqn:E1; [ apply Forall_nil | ].
  rewrite <- not_true_iff_false, ltb_int, to_Z_one in E1.
  cbv zeta. unfold in_int64 in Hx.
  pose proof (pow2_pos (to_Z bits) ltac:(lia)) as Hp.
  pose proof (pow2_ge_2 (to_Z bits) ltac:(lia)) as Hp2.
  (* The upper bound, [max_int asr bits], fits an [int]. *)
  assert (Hhi : to_Z (Int64.to_int (Int64.shift_right Int64.max_int bits))
                = (two63 - 1) / 2 ^ to_Z bits).
  { rewrite Int64.to_int_exact;
      rewrite Int64.shift_right_spec by lia; rewrite Int64.to_Z_max_int;
      [ reflexivity | ].
    assert (0 <= (two63 - 1) / 2 ^ to_Z bits)
      by (apply Z.div_pos; [ unfold two63; lia | lia ]).
    assert ((two63 - 1) / 2 ^ to_Z bits < two62)
      by (apply Z.div_lt_upper_bound; [ lia | unfold two63, two62; lia ]).
    lia. }
  assert (Hup : x / 2 ^ to_Z bits <= (two63 - 1) / 2 ^ to_Z bits)
    by (apply Z.div_le_mono; lia).
  destruct (two <=? bits)%sint63 eqn:E2.
  - apply leb_int in E2. rewrite to_Z_two in E2.
    pose proof (pow2_ge_4 (to_Z bits) ltac:(lia)) as Hp4.
    (* The lower bound, [min_int asr bits], fits an [int] and is not
       [min_int], so its negation is exact. *)
    assert (Hlo : to_Z (Int64.to_int (Int64.shift_right Int64.min_int bits))
                  = - two63 / 2 ^ to_Z bits).
    { rewrite Int64.to_int_exact;
        rewrite Int64.shift_right_spec by lia; rewrite Int64.to_Z_min_int;
        [ reflexivity | ].
      assert (- two62 <= - two63 / 2 ^ to_Z bits)
        by (apply Z.div_le_lower_bound; [ lia | unfold two63, two62; lia ]).
      assert (- two63 / 2 ^ to_Z bits <= 0)
        by (apply Z.div_le_upper_bound; [ lia | unfold two63; lia ]).
      unfold two62 in *. lia. }
    assert (Hlo' : - two62 < - two63 / 2 ^ to_Z bits).
    { assert (- 2305843009213693952 <= - two63 / 2 ^ to_Z bits)
        by (apply Z.div_le_lower_bound; [ lia | unfold two63; lia ]).
      unfold two63, two62 in *. lia. }
    assert (Hdown : - two63 / 2 ^ to_Z bits <= x / 2 ^ to_Z bits)
      by (apply Z.div_le_mono; lia).
    repeat (apply Forall_cons || apply Forall_nil); unfold holds.
    + rewrite upper_denote, Hhi, Hatom. lia.
    + rewrite lower_denote, Sint63.to_Z_opp.
      * rewrite Hlo, Hatom. lia.
      * intro C. apply (f_equal to_Z) in C. rewrite Hlo, to_Z_min_int in C.
        lia.
  - apply Forall_cons; [ | apply Forall_nil ]. unfold holds.
    rewrite upper_denote, Hhi, Hatom. lia.
Qed.

Lemma to_Z_word_bits : to_Z word_bits = 64.
Proof. reflexivity. Qed.

Lemma shr_range_facts_logical_sound : forall rho atom bits x,
  1 <= to_Z bits <= 63 -> in_int64 x ->
  rho atom = unsigned64 x / 2 ^ to_Z bits ->
  holds_all rho (shr_range_facts false atom bits).
Proof.
  intros rho atom bits x Hb Hx Hatom. unfold shr_range_facts.
  destruct (bits <? one)%sint63 eqn:E1.
  { apply ltb_int in E1. rewrite to_Z_one in E1. lia. }
  cbv zeta.
  pose proof (pow2_pos (to_Z bits) ltac:(lia)) as Hp.
  pose proof (unsigned64_bounds x Hx) as Hu.
  assert (Hnn : 0 <= rho atom) by (rewrite Hatom; apply Z.div_pos; lia).
  destruct (two <=? bits)%sint63 eqn:E2.
  - apply leb_int in E2. rewrite to_Z_two in E2.
    assert (Hm : to_Z (word_bits - bits)%sint63 = 64 - to_Z bits).
    { rewrite Sint63.to_Z_sub; rewrite to_Z_word_bits; [ reflexivity | ].
      rewrite to_Z_min_int, to_Z_max_int. unfold two62. lia. }
    assert (Hhi : to_Z ((one << (word_bits - bits)) - one)%sint63
                  = 2 ^ (64 - to_Z bits) - 1).
    { rewrite to_Z_lsl_one_pred; rewrite Hm; [ reflexivity | lia ]. }
    assert (Hlt : unsigned64 x / 2 ^ to_Z bits < 2 ^ (64 - to_Z bits)).
    { apply Z.div_lt_upper_bound; [ lia | ].
      rewrite <- Z.pow_add_r by lia.
      replace (to_Z bits + (64 - to_Z bits)) with 64 by lia.
      rewrite <- two64_pow. lia. }
    repeat (apply Forall_cons || apply Forall_nil); unfold holds.
    + rewrite upper_denote, Hhi, Hatom. lia.
    + rewrite var_denote. exact Hnn.
  - apply Forall_cons; [ | apply Forall_nil ]. unfold holds.
    rewrite var_denote. exact Hnn.
Qed.

(* --- [x lor m] for [m >= 0] lies in [[x, x + m]] (two's complement). --- *)

Lemma lor_bounds : forall x m, 0 <= m -> x <= Z.lor x m <= x + m.
Proof.
  intros x m Hm.
  pose proof (Z.add_lor_land x m) as Hsum.
  assert (H0 : 0 <= Z.land x m) by (apply Z.land_nonneg; right; exact Hm).
  assert (Hle : Z.land x m <= m).
  { pose proof (Z.sub_land_same_l m x) as Hs. rewrite (Z.land_comm m x) in Hs.
    assert (0 <= Z.land m (Z.lnot x))
      by (apply Z.land_nonneg; left; exact Hm).
    lia. }
  lia.
Qed.

(* ======================================================================== *)
(* Part 4: the theorems                                                     *)
(* ======================================================================== *)

(* --- [Range] --- *)

(* A range only holds 64-bit values. *)
Theorem in_range_int64 : forall r z, in_range r z -> in_int64 z.
Proof.
  intros r z [Hlo Hhi].
  pose proof (Int64.to_Z_bounded r.(Range.lo)).
  pose proof (Int64.to_Z_bounded r.(Range.hi)).
  unfold in_int64 in *. lia.
Qed.

Theorem full_sound : forall z, in_int64 z -> in_range Range.full z.
Proof.
  intros z Hz. unfold in_range, Range.full. cbn [Range.lo Range.hi].
  rewrite Int64.to_Z_min_int, Int64.to_Z_max_int. unfold in_int64 in Hz. lia.
Qed.

Theorem const_sound : forall c, in_range (Range.const c) (to_Z c).
Proof.
  intros c. unfold in_range, Range.const. cbv zeta. cbn [Range.lo Range.hi].
  rewrite Int64.of_int_spec. lia.
Qed.

(* [x asr bits], i.e. [x / 2^bits], for any 64-bit [x]. *)
Theorem shr_signed_sound : forall bits x,
  0 <= to_Z bits <= 63 -> in_int64 x ->
  in_range (Range.shr_signed bits) (x / 2 ^ to_Z bits).
Proof.
  intros bits x Hb Hx. unfold in_range, Range.shr_signed.
  cbn [Range.lo Range.hi].
  rewrite !Int64.shift_right_spec by exact Hb.
  rewrite Int64.to_Z_min_int, Int64.to_Z_max_int.
  unfold in_int64 in Hx. pose proof (pow2_pos (to_Z bits) ltac:(lia)).
  split; apply Z.div_le_mono; lia.
Qed.

(* [x lsr bits], i.e. [unsigned64 x / 2^bits], for any 64-bit [x]. *)
Theorem shr_logical_sound : forall bits x,
  1 <= to_Z bits <= 63 -> in_int64 x ->
  in_range (Range.shr_logical bits) (unsigned64 x / 2 ^ to_Z bits).
Proof.
  intros bits x Hb Hx. unfold in_range, Range.shr_logical.
  destruct (bits <=? zero)%sint63 eqn:E.
  { apply leb_int in E. rewrite to_Z_zero in E. lia. }
  cbn [Range.lo Range.hi]. rewrite Int64.to_Z_zero.
  rewrite Int64.shift_right_logical_spec by lia.
  rewrite Int64.to_Z_minus_one.
  pose proof (pow2_pos (to_Z bits) ltac:(lia)) as Hp.
  pose proof (pow2_ge_2 (to_Z bits) ltac:(lia)) as Hp2.
  pose proof (unsigned64_bounds x Hx) as Hu.
  change (unsigned64 (-1)) with (two64 - 1).
  assert (Hq : 0 <= (two64 - 1) / 2 ^ to_Z bits < two63).
  { split.
    - apply Z.div_pos; [ unfold two64; lia | lia ].
    - apply Z.div_lt_upper_bound; [ lia | unfold two63, two64; lia ]. }
  rewrite wrap64_id by (unfold in_int64; lia).
  split; [ apply Z.div_pos; lia | apply Z.div_le_mono; lia ].
Qed.

Theorem add_sound : forall a b r x y,
  Range.add a b = Some r -> in_range a x -> in_range b y ->
  in_range r (x + y).
Proof.
  intros a b r x y H [Hax Hxa] [Hby Hyb]. unfold Range.add in H.
  destruct (Range.add64 (Range.lo a) (Range.lo b)) as [ lo | ] eqn:Hlo;
    [ | discriminate ].
  destruct (Range.add64 (Range.hi a) (Range.hi b)) as [ hi | ] eqn:Hhi;
    [ | discriminate ].
  injection H as <-. unfold in_range. cbn [Range.lo Range.hi].
  apply add_ovf64_spec in Hlo. apply add_ovf64_spec in Hhi. lia.
Qed.

Theorem neg_sound : forall a r x,
  Range.neg a = Some r -> in_range a x -> in_range r (- x).
Proof.
  intros a r x H [Hlo Hhi]. unfold Range.neg in H.
  destruct (Int64.equal _ _) eqn:E; [ discriminate | ].
  injection H as <-. unfold in_range. cbn [Range.lo Range.hi].
  apply Int64.equal_false in E. rewrite Int64.to_Z_min_int in E.
  pose proof (Int64.to_Z_bounded (Range.lo a)).
  pose proof (Int64.to_Z_bounded (Range.hi a)).
  unfold in_int64 in *.
  rewrite !Int64.neg_spec, !wrap64_id by (unfold in_int64; lia). lia.
Qed.

Theorem sub_sound : forall a b r x y,
  Range.sub a b = Some r -> in_range a x -> in_range b y ->
  in_range r (x - y).
Proof.
  intros a b r x y H Ha Hb. unfold Range.sub in H.
  destruct (Range.neg b) as [ nb | ] eqn:Hnb; [ | discriminate ].
  pose proof (neg_sound _ _ _ Hnb Hb).
  replace (x - y) with (x + - y) by ring. eapply add_sound; eassumption.
Qed.

Theorem or_mask_sound : forall mask a r x,
  Range.or_mask mask a = Some r -> in_range a x ->
  in_range r (Z.lor x (to_Z mask)).
Proof.
  intros mask a r x H [Hlo Hhi]. unfold Range.or_mask in H.
  destruct (mask <? zero)%sint63 eqn:E; [ discriminate | ].
  rewrite <- not_true_iff_false, ltb_int, to_Z_zero in E.
  destruct (Range.add64 _ _) as [ hi | ] eqn:Hhi'; [ | discriminate ].
  injection H as <-. unfold in_range. cbn [Range.lo Range.hi].
  apply add_ovf64_spec in Hhi'. rewrite Int64.of_int_spec in Hhi'.
  pose proof (lor_bounds x (to_Z mask) ltac:(lia)). lia.
Qed.

Theorem scale_sound : forall k a r x,
  Range.scale k a = Some r -> in_range a x -> in_range r (to_Z k * x).
Proof.
  intros k a r x H [Hlo Hhi]. unfold Range.scale in H.
  destruct (k =? zero)%sint63 eqn:Ek.
  { apply eqb_int in Ek. subst k. injection H as <-.
    unfold in_range. cbn [Range.lo Range.hi].
    rewrite Int64.to_Z_zero, to_Z_zero. lia. }
  cbv zeta in H.
  destruct (Range.mul64 _ (Range.lo a)) as [ p | ] eqn:Hp; [ | discriminate ].
  destruct (Range.mul64 _ (Range.hi a)) as [ q | ] eqn:Hq; [ | discriminate ].
  apply mul_ovf64_spec in Hp. apply mul_ovf64_spec in Hq.
  rewrite Int64.of_int_spec in Hp, Hq.
  assert (Hk : to_Z k * Int64.to_Z (Range.lo a) <= to_Z k * x
               /\ to_Z k * x <= to_Z k * Int64.to_Z (Range.hi a)
               \/ to_Z k * Int64.to_Z (Range.hi a) <= to_Z k * x
                  /\ to_Z k * x <= to_Z k * Int64.to_Z (Range.lo a)).
  { destruct (Z_lt_le_dec 0 (to_Z k)) as [ Hpos | Hneg ].
    - left. split; apply Z.mul_le_mono_nonneg_l; lia.
    - right. split; apply Z.mul_le_mono_nonpos_l; lia. }
  destruct (Int64.compare p q <=? zero)%sint63 eqn:Ec; injection H as <-;
    unfold in_range; cbn [Range.lo Range.hi].
  - apply Int64.compare_le in Ec. lia.
  - rewrite <- not_true_iff_false, Int64.compare_le in Ec. lia.
Qed.

(* --- [to_affine] --- *)

(* Everything at once, by induction on the expression: the form and the
   side facts are well-formed, the form has the expression's value, and
   the side facts hold when the atoms are consistent. ([shr_range_facts]
   is kept folded while [to_affine] is unfolded.) *)
Opaque shr_range_facts.
Lemma to_affine_spec : forall e f sides,
  to_affine e = Some (f, sides) ->
  wf f /\ Forall wf sides
  /\ (forall rho, denote rho f = eval rho e)
  /\ (forall rho, consistent rho e -> holds_all rho sides).
Proof.
  induction e; intros f sides H; cbn [to_affine] in H.
  - (* Const *)
    injection H as <- <-.
    split; [ apply constant_wf | split; [ constructor | ] ].
    split; [ intros rho; apply constant_denote | intros rho _; constructor ].
  - (* Atom *)
    injection H as <- <-.
    split; [ apply var_wf | split; [ constructor | ] ].
    split; [ intros rho; apply var_denote | intros rho _; constructor ].
  - (* Add *)
    destruct (to_affine e1) as [ [fa sa] | ] eqn:Ha; [ | discriminate ].
    destruct (to_affine e2) as [ [fb sb] | ] eqn:Hb; [ | discriminate ].
    destruct (Affine.add_checked fa fb) as [ f' | ] eqn:Hf; [ | discriminate ].
    injection H as <- <-.
    destruct (IHe1 _ _ eq_refl) as [Hwa [Hwsa [Hda Hsa]]].
    destruct (IHe2 _ _ eq_refl) as [Hwb [Hwsb [Hdb Hsb]]].
    split; [ | split; [ | split ] ].
    + exact (proj2 (proj2 (add_checked_spec (fun _ => 0) _ _ _ Hwa Hwb Hf))).
    + apply Forall_app; split; assumption.
    + intros rho. destruct (add_checked_spec rho _ _ _ Hwa Hwb Hf) as [Hd _].
      rewrite Hd, Hda, Hdb. reflexivity.
    + intros rho [Hca Hcb]. unfold holds_all. apply Forall_app.
      split; [ apply Hsa | apply Hsb ]; assumption.
  - (* Sub *)
    destruct (to_affine e1) as [ [fa sa] | ] eqn:Ha; [ | discriminate ].
    destruct (to_affine e2) as [ [fb sb] | ] eqn:Hb; [ | discriminate ].
    destruct (Affine.scale_checked minus_one fb) as [ nfb | ] eqn:Hn;
      [ | discriminate ].
    destruct (Affine.add_checked fa nfb) as [ f' | ] eqn:Hf; [ | discriminate ].
    injection H as <- <-.
    destruct (IHe1 _ _ eq_refl) as [Hwa [Hwsa [Hda Hsa]]].
    destruct (IHe2 _ _ eq_refl) as [Hwb [Hwsb [Hdb Hsb]]].
    pose proof (proj2 (proj2 (scale_checked_spec (fun _ => 0) _ _ _ Hn)) Hwb)
      as Hwn.
    split; [ | split; [ | split ] ].
    + exact (proj2 (proj2 (add_checked_spec (fun _ => 0) _ _ _ Hwa Hwn Hf))).
    + apply Forall_app; split; assumption.
    + intros rho. destruct (add_checked_spec rho _ _ _ Hwa Hwn Hf) as [Hd _].
      destruct (scale_checked_spec rho _ _ _ Hn) as [Hdn _].
      rewrite Hd, Hdn, Hda, Hdb, to_Z_minus_one. cbn [eval]. ring.
    + intros rho [Hca Hcb]. unfold holds_all. apply Forall_app.
      split; [ apply Hsa | apply Hsb ]; assumption.
  - (* Scale *)
    destruct (to_affine e) as [ [fa sa] | ] eqn:Ha; [ | discriminate ].
    destruct (Affine.scale_checked k fa) as [ f' | ] eqn:Hf; [ | discriminate ].
    injection H as <- <-.
    destruct (IHe _ _ eq_refl) as [Hwa [Hwsa [Hda Hsa]]].
    split; [ | split; [ | split ] ].
    + exact (proj2 (proj2 (scale_checked_spec (fun _ => 0) _ _ _ Hf)) Hwa).
    + exact Hwsa.
    + intros rho. destruct (scale_checked_spec rho _ _ _ Hf) as [Hd _].
      rewrite Hd, Hda. reflexivity.
    + intros rho Hc. apply Hsa. exact Hc.
  - (* Shr_atom *)
    destruct (to_affine e) as [ [fa sa] | ] eqn:Ha; [ | discriminate ].
    cbv zeta in H.
    destruct (Affine.scale_checked (- (one << bits))%sint63 (Affine.var atom))
      as [ m | ] eqn:Hm; [ | discriminate ].
    destruct (Affine.add_checked fa m) as [ s1 | ] eqn:Hs1; [ | discriminate ].
    destruct (Affine.scale_checked (one << bits)%sint63 (Affine.var atom))
      as [ p | ] eqn:Hp; [ | discriminate ].
    destruct (Affine.add_const_checked p ((one << bits) - one)%sint63)
      as [ pc | ] eqn:Hpc; [ | discriminate ].
    destruct (Affine.scale_checked minus_one fa) as [ nfa | ] eqn:Hnfa;
      [ | discriminate ].
    destruct (Affine.add_checked pc nfa) as [ s2 | ] eqn:Hs2;
      [ | discriminate ].
    injection H as <- <-.
    destruct (IHe _ _ eq_refl) as [Hwa [Hwsa [Hda Hsa]]].
    pose proof (proj2 (proj2 (scale_checked_spec (fun _ => 0) _ _ _ Hm))
                  (var_wf atom)) as Hwm.
    pose proof (proj2 (proj2 (add_checked_spec (fun _ => 0) _ _ _ Hwa Hwm Hs1)))
      as Hws1.
    pose proof (proj2 (proj2 (scale_checked_spec (fun _ => 0) _ _ _ Hp))
                  (var_wf atom)) as Hwp.
    pose proof (proj2 (proj2 (add_const_checked_spec (fun _ => 0) _ _ _ Hpc))
                  Hwp) as Hwpc.
    pose proof (proj2 (proj2 (scale_checked_spec (fun _ => 0) _ _ _ Hnfa)) Hwa)
      as Hwnfa.
    pose proof (proj2 (proj2 (add_checked_spec (fun _ => 0) _ _ _ Hwpc Hwnfa
                                Hs2))) as Hws2.
    split; [ apply var_wf | split; [ | split ] ].
    + apply Forall_cons; [ exact Hws1 | ]. apply Forall_cons; [ exact Hws2 | ].
      apply Forall_app. split; [ apply shr_range_facts_wf | exact Hwsa ].
    + intros rho. apply var_denote.
    + intros rho [Hc [Hb [Hx Hatom]]].
      pose proof (to_Z_lsl_one bits ltac:(lia)) as Hpow.
      pose proof (pow2_pos (to_Z bits) ltac:(lia)) as Hp2.
      pose proof (Z.pow_le_mono_r 2 (to_Z bits) 61 ltac:(lia) ltac:(lia))
        as Hp61.
      change (2 ^ 61) with 2305843009213693952 in Hp61.
      assert (Hnmin : (one << bits)%sint63 <> min_int).
      { intro C. apply (f_equal to_Z) in C. rewrite Hpow, to_Z_min_int in C.
        unfold two62 in C. lia. }
      apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_app; split ] ].
      * (* [fa - pow * v >= 0] *)
        unfold holds.
        destruct (add_checked_spec rho _ _ _ Hwa Hwm Hs1) as [Hd1 _].
        destruct (scale_checked_spec rho _ _ _ Hm) as [Hdm _].
        rewrite Hd1, Hdm, var_denote, Sint63.to_Z_opp by exact Hnmin.
        rewrite Hpow, Hda, Hatom.
        pose proof (Z.mul_div_le (eval rho e) (2 ^ to_Z bits) Hp2). lia.
      * (* [pow * v + (pow - 1) - fa >= 0] *)
        unfold holds.
        destruct (add_checked_spec rho _ _ _ Hwpc Hwnfa Hs2) as [Hd2 _].
        destruct (add_const_checked_spec rho _ _ _ Hpc) as [Hdpc _].
        destruct (scale_checked_spec rho _ _ _ Hp) as [Hdp _].
        destruct (scale_checked_spec rho _ _ _ Hnfa) as [Hdn _].
        rewrite Hd2, Hdpc, Hdp, Hdn, var_denote, to_Z_minus_one, Hda.
        rewrite Sint63.to_Z_sub
          by (rewrite Hpow, to_Z_one, to_Z_min_int, to_Z_max_int;
              unfold two62, two63 in *; lia).
        rewrite Hpow, to_Z_one, Hatom.
        pose proof (Z.mul_succ_div_gt (eval rho e) (2 ^ to_Z bits) Hp2). lia.
      * eapply shr_range_facts_signed_sound; [ lia | exact Hx | exact Hatom ].
      * apply Hsa. exact Hc.
  - (* Lsr_atom *)
    injection H as <- <-.
    split; [ apply var_wf | split; [ apply shr_range_facts_wf | split  ] ].
    + intros rho. apply var_denote.
    + intros rho [Hb [r [Hr Hatom]]].
      eapply shr_range_facts_logical_sound;
        [ exact Hb | exact Hr | exact Hatom ].
  - (* Or_atom *)
    destruct (to_affine e) as [ [fa sa] | ] eqn:Ha; [ | discriminate ].
    cbv zeta in H.
    destruct (Affine.scale_checked minus_one fa) as [ nfa | ] eqn:Hnfa;
      [ | discriminate ].
    destruct (Affine.add_checked (Affine.var atom) nfa) as [ s1 | ] eqn:Hs1;
      [ | discriminate ].
    destruct (Affine.add_const_checked fa mask) as [ fm | ] eqn:Hfm;
      [ | discriminate ].
    destruct (Affine.scale_checked minus_one (Affine.var atom)) as [ nv | ]
      eqn:Hnv; [ | discriminate ].
    destruct (Affine.add_checked fm nv) as [ s2 | ] eqn:Hs2; [ | discriminate ].
    injection H as <- <-.
    destruct (IHe _ _ eq_refl) as [Hwa [Hwsa [Hda Hsa]]].
    pose proof (proj2 (proj2 (scale_checked_spec (fun _ => 0) _ _ _ Hnfa)) Hwa)
      as Hwnfa.
    pose proof (proj2 (proj2 (add_checked_spec (fun _ => 0) _ _ _ (var_wf atom)
                                Hwnfa Hs1))) as Hws1.
    pose proof (proj2 (proj2 (add_const_checked_spec (fun _ => 0) _ _ _ Hfm))
                  Hwa) as Hwfm.
    pose proof (proj2 (proj2 (scale_checked_spec (fun _ => 0) _ _ _ Hnv))
                  (var_wf atom)) as Hwnv.
    pose proof (proj2 (proj2 (add_checked_spec (fun _ => 0) _ _ _ Hwfm Hwnv
                                Hs2))) as Hws2.
    split; [ apply var_wf | split; [ | split ] ].
    + apply Forall_cons; [ exact Hws1 | ]. apply Forall_cons; [ exact Hws2 | ].
      exact Hwsa.
    + intros rho. apply var_denote.
    + intros rho [Hc [Hmask Hatom]].
      pose proof (lor_bounds (eval rho e) (to_Z mask) Hmask) as Hor.
      apply Forall_cons; [ | apply Forall_cons; [ | apply Hsa; exact Hc ] ];
        unfold holds.
      * destruct (add_checked_spec rho _ _ _ (var_wf atom) Hwnfa Hs1)
          as [Hd1 _].
        destruct (scale_checked_spec rho _ _ _ Hnfa) as [Hdn _].
        rewrite Hd1, Hdn, var_denote, to_Z_minus_one, Hda, Hatom. lia.
      * destruct (add_checked_spec rho _ _ _ Hwfm Hwnv Hs2) as [Hd2 _].
        destruct (add_const_checked_spec rho _ _ _ Hfm) as [Hdfm _].
        destruct (scale_checked_spec rho _ _ _ Hnv) as [Hdnv _].
        rewrite Hd2, Hdfm, Hdnv, var_denote, to_Z_minus_one, Hda, Hatom. lia.
Qed.
Transparent shr_range_facts.

(* The form has the expression's value, and the side facts hold, whenever
   the atoms are consistent. [consistent] is only needed for the side
   facts: the value equation holds unconditionally. *)
Theorem to_affine_sound : forall rho e f sides,
  to_affine e = Some (f, sides) ->
  denote rho f = eval rho e
  /\ (consistent rho e -> holds_all rho sides).
Proof.
  intros rho e f sides H.
  destruct (to_affine_spec e f sides H) as [_ [_ [Hd Hs]]].
  split; [ apply Hd | apply Hs ].
Qed.

(* The form and the side facts are well-formed, as [entails] requires. *)
Theorem to_affine_wf : forall e f sides,
  to_affine e = Some (f, sides) -> wf f /\ Forall wf sides.
Proof.
  intros e f sides H. destruct (to_affine_spec e f sides H) as [Hw [Hws _]].
  split; assumption.
Qed.
