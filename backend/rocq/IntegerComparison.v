(* [Cmm.integer_comparison] (i.e. [Scalar.Integer_comparison.t]), its
   [negate] and [swap], and what a comparison computes on 64-bit machine
   values.

   The transcription is to be compared with typing/scalar.ml; the
   constructor order matters for extraction. *)

From Stdlib Require Import ZArith Lia.
From OxcamlStdlib Require Import OcamlInt64 ZTactics.

Local Open Scope Z_scope.

Inductive integer_comparison : Type :=
  | Ceq | Cne | Clt | Cgt | Cle | Cge | Cult | Cugt | Cule | Cuge.

(* [Scalar.Integer_comparison.negate] = [Cmm.negate_integer_comparison] *)
Definition negate (c : integer_comparison) : integer_comparison :=
  match c with
  | Ceq => Cne
  | Cne => Ceq
  | Clt => Cge
  | Cle => Cgt
  | Cgt => Cle
  | Cge => Clt
  | Cult => Cuge
  | Cule => Cugt
  | Cugt => Cule
  | Cuge => Cult
  end.

(* [Scalar.Integer_comparison.swap] = [Cmm.swap_integer_comparison] *)
Definition swap (c : integer_comparison) : integer_comparison :=
  match c with
  | Ceq => Ceq
  | Cne => Cne
  | Clt => Cgt
  | Cle => Cge
  | Cgt => Clt
  | Cge => Cle
  | Cult => Cugt
  | Cule => Cuge
  | Cugt => Cult
  | Cuge => Cule
  end.

(* What the machine computes for [a cmp b] on 64-bit signed values [a] and
   [b]: the signed comparisons compare the values, the unsigned ones compare
   their unsigned readings. *)
Definition eval (cmp : integer_comparison) (a b : Z) : bool :=
  match cmp with
  | Ceq => a =? b
  | Cne => negb (a =? b)
  | Clt => a <? b
  | Cgt => b <? a
  | Cle => a <=? b
  | Cge => b <=? a
  | Cult => unsigned64 a <? unsigned64 b
  | Cugt => unsigned64 b <? unsigned64 a
  | Cule => unsigned64 a <=? unsigned64 b
  | Cuge => unsigned64 b <=? unsigned64 a
  end.

(* [negate] computes the negation of a comparison. *)
Theorem negate_correct : forall cmp a b,
  eval (negate cmp) a b = negb (eval cmp a b).
Proof.
  intros cmp a b. destruct cmp; simpl; case_zcmp.
Qed.

(* [swap] computes the comparison with its operands exchanged. *)
Theorem swap_correct : forall cmp a b,
  eval (swap cmp) a b = eval cmp b a.
Proof.
  intros cmp a b. destruct cmp; simpl; case_zcmp.
Qed.
