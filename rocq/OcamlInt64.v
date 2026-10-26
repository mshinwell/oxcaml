(* 64-bit machine integers: the arithmetic of a machine register, and
   OCaml's [Int64].

   The first half is pure mathematics on [Z]: two's-complement wrap-around
   and the signed/unsigned readings of a 64-bit value. The second half models
   OCaml's [Int64] as an abstract type whose operations are specified, as
   axioms, by that arithmetic. Rocq has no primitive 64-bit integer, so this
   is the trusted base for every model that computes in [Int64]; each axiom
   is the documented behaviour of the OCaml operation. *)

From Stdlib Require Import ZArith Lia Bool.
From OxcamlStdlib Require Import OcamlInt.

Local Open Scope Z_scope.

(* ---- 64-bit arithmetic on Z ------------------------------------------- *)

Definition two63 : Z := 9223372036854775808.
Definition two64 : Z := 18446744073709551616.

Lemma two63_pow : two63 = 2 ^ 63. Proof. reflexivity. Qed.
Lemma two64_pow : two64 = 2 ^ 64. Proof. reflexivity. Qed.

(* A 64-bit machine register, read as a signed integer. *)
Definition in_int64 (z : Z) : Prop := - two63 <= z < two63.

(* The same, as a boolean test. *)
Definition fits_int64 (z : Z) : bool := (- two63 <=? z) && (z <? two63).

Lemma fits_int64_true : forall z, fits_int64 z = true -> in_int64 z.
Proof.
  unfold fits_int64, in_int64. intros z H. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* 64-bit two's-complement wrap-around: the register holding [z]. *)
Definition wrap64 (z : Z) : Z := (z + two63) mod two64 - two63.

(* The unsigned reading of a signed 64-bit value. *)
Definition unsigned64 (z : Z) : Z := if z <? 0 then z + two64 else z.

Lemma unsigned64_bounds : forall z, in_int64 z -> 0 <= unsigned64 z < two64.
Proof.
  intros z Hz. unfold unsigned64, in_int64, two63, two64 in *.
  destruct (z <? 0) eqn:E; [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]; lia.
Qed.

(* [wrap64 z] differs from [z] by a multiple of 2^64 ... *)
Lemma wrap64_eq : forall z, exists k, wrap64 z = z - k * two64.
Proof.
  intro z. exists ((z + two63) / two64). unfold wrap64.
  pose proof (Z.div_mod (z + two63) two64 ltac:(unfold two64; lia)) as H.
  unfold two63, two64 in *. lia.
Qed.

(* ... and is a 64-bit value ... *)
Lemma wrap64_in_range : forall z, in_int64 (wrap64 z).
Proof.
  intro z. unfold in_int64, wrap64.
  pose proof (Z.mod_pos_bound (z + two63) two64 ltac:(unfold two64; lia)).
  unfold two63, two64 in *. lia.
Qed.

(* ... so it is the identity on 64-bit values. *)
Lemma wrap64_id : forall z, in_int64 z -> wrap64 z = z.
Proof.
  intros z Hz. destruct (wrap64_eq z) as [k Hk].
  pose proof (wrap64_in_range z) as Hr. rewrite Hk in Hr.
  unfold in_int64, two63, two64 in *.
  assert (k = 0) by lia. subst k. lia.
Qed.

(* The truncated quotient of a 64-bit value by a positive divisor is again
   a 64-bit value (its magnitude does not grow). *)
Lemma quot_abs_le : forall a b, 0 < b -> Z.abs (Z.quot a b) <= Z.abs a.
Proof.
  intros a b Hb.
  assert (Hpos : forall x, 0 <= x -> Z.quot x b <= x).
  { intros x Hx. apply Z.quot_le_upper_bound; [ exact Hb | nia ]. }
  destruct (Z_le_gt_dec 0 a) as [ Ha | Ha ].
  - pose proof (Z.quot_pos a b Ha Hb). pose proof (Hpos a Ha). lia.
  - pose proof (Z.quot_pos (- a) b ltac:(lia) Hb) as H1.
    pose proof (Hpos (- a) ltac:(lia)) as H2.
    rewrite Z.quot_opp_l in H1, H2 by lia. lia.
Qed.

Lemma quot_in_range : forall a b, 0 < b -> in_int64 a -> in_int64 (Z.quot a b).
Proof.
  intros a b Hb Ha. pose proof (quot_abs_le a b Hb).
  destruct (Z_le_gt_dec 0 a) as [ Ha0 | Ha0 ].
  - pose proof (Z.quot_pos a b Ha0 Hb). unfold in_int64 in *. lia.
  - pose proof (Z.quot_pos (- a) b ltac:(lia) Hb) as H1.
    rewrite Z.quot_opp_l in H1 by lia. unfold in_int64 in *. lia.
Qed.

(* ---- OCaml's [Int64] --------------------------------------------------- *)

(* The type and its operations are declared at top level and given their
   OCaml names by the abbreviations in [Module Int64] below, so that the
   models write [Int64.add a b] as the OCaml does, while extraction
   (OcamlExtract.v) maps each operation straight to OCaml's without
   emitting a module that would shadow OCaml's [Int64]. The axioms, which
   are not extracted, live in the module. *)

Parameter int64 : Type.
Parameter int64_to_Z : int64 -> Z.
Parameter int64_zero int64_one int64_minus_one int64_min_int int64_max_int
  : int64.
Parameter int64_of_int : int -> int64.
Parameter int64_to_int : int64 -> int.
Parameter int64_add int64_sub int64_mul int64_div int64_rem
  : int64 -> int64 -> int64.
Parameter int64_abs int64_neg : int64 -> int64.
Parameter int64_shift_right int64_shift_right_logical : int64 -> int -> int64.
Parameter int64_equal : int64 -> int64 -> bool.
Parameter int64_compare : int64 -> int64 -> int.

Module Int64.
  Abbreviation t := int64.
  Abbreviation to_Z := int64_to_Z.
  Abbreviation zero := int64_zero.
  Abbreviation one := int64_one.
  Abbreviation minus_one := int64_minus_one.
  Abbreviation min_int := int64_min_int.
  Abbreviation max_int := int64_max_int.
  Abbreviation of_int := int64_of_int.
  Abbreviation to_int := int64_to_int.
  Abbreviation add := int64_add.
  Abbreviation sub := int64_sub.
  Abbreviation mul := int64_mul.
  Abbreviation div := int64_div.
  Abbreviation rem := int64_rem.
  Abbreviation abs := int64_abs.
  Abbreviation neg := int64_neg.
  Abbreviation shift_right := int64_shift_right.
  Abbreviation shift_right_logical := int64_shift_right_logical.
  Abbreviation equal := int64_equal.
  Abbreviation compare := int64_compare.

  Axiom to_Z_bounded : forall x, in_int64 (to_Z x).
  Axiom to_Z_zero : to_Z zero = 0.
  Axiom to_Z_one : to_Z one = 1.
  Axiom to_Z_minus_one : to_Z minus_one = -1.
  Axiom to_Z_min_int : to_Z min_int = - two63.
  Axiom to_Z_max_int : to_Z max_int = two63 - 1.

  (* [Int64.of_int] is exact: every [int] is a 64-bit value. *)
  Axiom of_int_spec : forall i, to_Z (of_int i) = Sint63Axioms.to_Z i.

  (* [Int64.to_int] drops the top bit, so it is exact on the values that
     fit an [int]. *)
  Axiom to_int_exact : forall a,
    - two62 <= to_Z a <= two62 - 1 -> Sint63Axioms.to_Z (to_int a) = to_Z a.

  Axiom add_spec : forall a b, to_Z (add a b) = wrap64 (to_Z a + to_Z b).
  Axiom sub_spec : forall a b, to_Z (sub a b) = wrap64 (to_Z a - to_Z b).
  Axiom mul_spec : forall a b, to_Z (mul a b) = wrap64 (to_Z a * to_Z b).
  (* Division truncates toward zero; [min_int / -1] wraps to [min_int]. The
     OCaml raises [Division_by_zero] on a zero divisor, which the models
     never pass. *)
  Axiom div_spec : forall a b,
    to_Z b <> 0 -> to_Z (div a b) = wrap64 (Z.quot (to_Z a) (to_Z b)).
  Axiom rem_spec : forall a b,
    to_Z b <> 0 -> to_Z (rem a b) = Z.rem (to_Z a) (to_Z b).
  (* [Int64.abs min_int = min_int], and likewise [Int64.neg]. *)
  Axiom abs_spec : forall a, to_Z (abs a) = wrap64 (Z.abs (to_Z a)).
  Axiom neg_spec : forall a, to_Z (neg a) = wrap64 (- to_Z a).
  (* The right shifts, for amounts within the width (OCaml leaves the
     others unspecified): [shift_right] is the arithmetic shift, division
     by [2^n] rounding towards minus infinity, and [shift_right_logical]
     divides the unsigned reading of the value. *)
  Axiom shift_right_spec : forall a n,
    0 <= Sint63Axioms.to_Z n <= 63 ->
    to_Z (shift_right a n) = to_Z a / 2 ^ Sint63Axioms.to_Z n.
  Axiom shift_right_logical_spec : forall a n,
    0 <= Sint63Axioms.to_Z n <= 63 ->
    to_Z (shift_right_logical a n)
    = wrap64 (unsigned64 (to_Z a) / 2 ^ Sint63Axioms.to_Z n).
  Axiom equal_spec : forall a b, equal a b = true <-> to_Z a = to_Z b.
  (* OCaml's [Int64.compare] returns an [int] that is negative, zero or
     positive according as the first argument is less than, equal to or
     greater than the second. *)
  Axiom compare_spec : forall a b,
    (Sint63Axioms.to_Z (compare a b) < 0 <-> to_Z a < to_Z b)
    /\ (Sint63Axioms.to_Z (compare a b) = 0 <-> to_Z a = to_Z b).

  (* The tests the OCaml writes as [Int64.compare x y < 0], [> 0] and
     [>= 0], which the models write the same way. *)
  Lemma compare_lt : forall a b,
    (compare a b <? OcamlInt.zero)%sint63 = true <-> to_Z a < to_Z b.
  Proof.
    intros a b. rewrite ltb_int, OcamlInt.to_Z_zero.
    exact (proj1 (compare_spec a b)).
  Qed.

  Lemma compare_gt : forall a b,
    (OcamlInt.zero <? compare a b)%sint63 = true <-> to_Z b < to_Z a.
  Proof.
    intros a b. rewrite ltb_int, OcamlInt.to_Z_zero.
    destruct (compare_spec a b) as [Hlt Heq]. lia.
  Qed.

  Lemma compare_ge : forall a b,
    (OcamlInt.zero <=? compare a b)%sint63 = true <-> to_Z b <= to_Z a.
  Proof.
    intros a b. rewrite leb_int, OcamlInt.to_Z_zero.
    destruct (compare_spec a b) as [Hlt Heq]. lia.
  Qed.

  Lemma compare_le : forall a b,
    (compare a b <=? OcamlInt.zero)%sint63 = true <-> to_Z a <= to_Z b.
  Proof.
    intros a b. rewrite leb_int, OcamlInt.to_Z_zero.
    destruct (compare_spec a b) as [Hlt Heq]. lia.
  Qed.

  Lemma equal_false : forall a b, equal a b = false -> to_Z a <> to_Z b.
  Proof.
    intros a b H E. apply equal_spec in E. congruence.
  Qed.

  Lemma nonzero : forall b, equal b zero = false -> to_Z b <> 0.
  Proof.
    intros b H. rewrite <- to_Z_zero. apply equal_false. exact H.
  Qed.
End Int64.
