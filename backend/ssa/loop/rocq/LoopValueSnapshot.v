(* A mathematical valuation for the affine analysis, constructed rather
   than assumed of a program execution.

   AffineSsa's arithmetic theorems use a total valuation of syntax. Here
   [snapshot_value] extends a register snapshot to all syntax by arithmetic
   interpretation, including fabricated expressions. It is not execution
   and is not extracted. [snapshot_agrees_available] proves agreement with
   actual register reads only for canonical available values. No invariance
   or execution meaning is assigned to fabricated expressions. *)

From Stdlib Require Import ZArith Lia List Bool.
From OxCamlStdlib Require Import OxCamlInt OxCamlInt64.
From OxCamlBackend Require Import Operation.
From OxCamlSsa Require Import SsaModel SsaSemantics SsaExecution.
From OxCamlLoop Require Import AffineExpr AffineSsa.
Import ListNotations.
Local Open Scope Z_scope.

Definition snapshot_atom (regs : registers) (v : value) : Z :=
  match regs (register_of_value v) with
  | Some word => wrap64 word
  | None => 0
  end.

Fixpoint snapshot_value (regs : registers) (v : value) : Z :=
  match v with
  | Res _ (Const_int constant) _ _ =>
    Int64.to_Z (Int64.of_nativeint constant)
  | Res _ (Intop Iadd) [lhs; rhs] _ =>
    wrap64 (snapshot_value regs lhs + snapshot_value regs rhs)
  | Res _ (Intop Isub) [lhs; rhs] _ =>
    wrap64 (snapshot_value regs lhs - snapshot_value regs rhs)
  | Res _ (Intop_imm Iadd constant) [arg] _ =>
    wrap64 (snapshot_value regs arg + to_Z constant)
  | Res _ (Intop_imm Isub constant) [arg] _ =>
    wrap64 (snapshot_value regs arg - to_Z constant)
  | Res _ (Intop_imm Ilsl bits) [arg] _ =>
    if Z.leb 0 (to_Z bits) && Z.leb (to_Z bits) 63
    then wrap64 (snapshot_value regs arg * 2 ^ to_Z bits)
    else snapshot_atom regs v
  | Res _ (Intop_imm Iasr bits) [arg] _ =>
    if Z.leb 0 (to_Z bits) && Z.leb (to_Z bits) 63
    then wrap64 (snapshot_value regs arg / 2 ^ to_Z bits)
    else snapshot_atom regs v
  | Res _ (Intop_imm Ilsr bits) [arg] _ =>
    if Z.leb 0 (to_Z bits) && Z.leb (to_Z bits) 63
    then wrap64 (unsigned64 (snapshot_value regs arg) / 2 ^ to_Z bits)
    else snapshot_atom regs v
  | Res _ (Intop_imm Ior mask) [arg] _ =>
    wrap64 (Z.lor (snapshot_value regs arg) (to_Z mask))
  | _ => snapshot_atom regs v
  end.

(* Unavailable atoms may be assigned defaults in the mathematical
   extension, but those defaults are not used by the execution semantics. *)
Lemma snapshot_atom_bounded : forall (regs : registers) (v : value),
  in_int64 (snapshot_atom regs v).
Proof.
  intros regs v. unfold snapshot_atom. destruct (regs (register_of_value v)).
  - apply wrap64_in_range.
  - unfold in_int64, two63. lia.
Qed.

(* The total mathematical extension is bounded even for unavailable or
   fabricated syntax. All interpreted arithmetic is explicitly wrapped. *)
Lemma snapshot_value_bounded : forall (regs : registers) (v : value),
  in_int64 (snapshot_value regs v).
Proof.
  intros regs [id op args index | b index];
    [ | apply snapshot_atom_bounded].
  destruct op; try apply snapshot_atom_bounded;
    try apply Int64.to_Z_bounded;
    try (destruct op; try apply snapshot_atom_bounded);
    destruct args as [ | lhs [ | rhs [ | extra rest]]];
    cbn [snapshot_value];
    try (destruct (Z.leb 0 (to_Z k) && Z.leb (to_Z k) 63));
    try apply snapshot_atom_bounded; apply wrap64_in_range.
Qed.

(* The extension satisfies the affine library's operation equations on
   all syntax. This universal fact is proved, not a machine/run premise. *)
Theorem snapshot_operation_semantics : forall (regs : registers) (v : value),
  op_semantics (snapshot_value regs) v.
Proof.
  intros regs [id op args index | b index]; [ | exact I].
  destruct op; try exact I; try reflexivity;
    try (destruct op; try exact I);
    destruct args as [ | lhs [ | rhs [ | extra rest]]];
    cbn [op_semantics snapshot_value]; try exact I; try reflexivity;
    try (intros Hshift;
      rewrite (proj2 (Z.leb_le _ _) (proj1 Hshift)),
        (proj2 (Z.leb_le _ _) (proj2 Hshift)); reflexivity).
  - apply wrap64_id, lor_in_int64.
    + apply snapshot_value_bounded.
    + pose proof (int_bounds k). unfold in_int64, two63, two62 in *. lia.
  - intros Hshift.
    rewrite (proj2 (Z.leb_le _ _) (proj1 Hshift)),
      (proj2 (Z.leb_le _ _) (proj2 Hshift)).
    apply wrap64_id.
    eapply in_range_int64. eapply shr_signed_sound;
      [exact Hshift | apply snapshot_value_bounded].
Qed.

(* A bound register's mathematical atom is exactly its stored word. *)
Lemma snapshot_atom_read : forall (regs : registers) (v : value) (word : Z),
  bounded_registers regs -> regs (register_of_value v) = Some word ->
  snapshot_atom regs v = word.
Proof.
  intros regs v word Hbounded Hread. unfold snapshot_atom. rewrite Hread.
  apply wrap64_id. eapply Hbounded. exact Hread.
Qed.

(* Pointwise agreement on actual operands gives the same argument list
   in the affine valuation as the instruction read from its registers. *)
Lemma read_values_snapshot : forall (regs : registers) (args : list value)
    (words : list Z),
  bounded_registers regs -> read_values regs args = Some words ->
  (forall (arg : value), In arg args ->
     snapshot_value regs arg = snapshot_atom regs arg) ->
  Forall2 (fun arg word => snapshot_value regs arg = word) args words.
Proof.
  intros regs args. induction args as [ | arg args IH];
    intros words Hbounded Hread Hagree; cbn [read_values] in Hread.
  - injection Hread as <-. constructor.
  - destruct (regs (register_of_value arg)) as [word |] eqn:Harg;
      [ | discriminate].
    destruct (read_values regs args) as [rest |] eqn:Hrest; [ | discriminate].
    injection Hread as <-. constructor.
    + rewrite (Hagree arg (or_introl eq_refl)).
      eapply snapshot_atom_read; eassumption.
    + eapply IH; [exact Hbounded | reflexivity |].
      intros value Hin. apply Hagree. right. exact Hin.
Qed.

(* For an actually evaluated operation, interpreting its operands in an
   agreeing snapshot computes the stored result. Comparisons and opaque
   syntax use their result register directly in the affine valuation. *)
Lemma snapshot_evaluated_result : forall (regs : registers) (id : instr_id)
    (op : operation) (args : list value) (index : int)
    (words : list Z) (result : Z),
  eval_operation op words = Some result ->
  Forall2 (fun arg word => snapshot_value regs arg = word) args words ->
  regs (Result id index) = Some result ->
  snapshot_value regs (Res id op args index)
    = snapshot_atom regs (Res id op args index).
Proof.
  intros regs id op args index words result Heval Hargs Hvalue.
  pose proof (eval_operation_bounded _ _ _ Heval) as Hbounded.
  destruct op; try discriminate;
    try solve [cbn [eval_operation] in Heval; injection Heval as <-;
      cbn [snapshot_value snapshot_atom register_of_value]; rewrite Hvalue;
      symmetry; apply wrap64_id, Int64.to_Z_bounded];
    try (destruct op; try discriminate);
    destruct words as [ | lhs [ | rhs [ | extra rest]]];
    cbn [eval_operation] in Heval; try discriminate;
    try (destruct (Z.leb 0 (to_Z k) && Z.leb (to_Z k) 63) eqn:Hshift;
      [ | discriminate]);
    repeat match goal with
    | H : Forall2 _ _ [] |- _ => inversion H; clear H; subst
    | H : Forall2 _ _ (_ :: _) |- _ => inversion H; clear H; subst
    end;
    cbn [snapshot_value]; try rewrite Hshift; try reflexivity;
    unfold snapshot_atom; cbn [register_of_value]; rewrite Hvalue;
    rewrite (wrap64_id _ Hbounded); injection Heval as <-; congruence.
Qed.

(* Syntax outside the exact operation model reads its register directly.
   In particular, no equation is assumed for a load or other opaque op. *)
Lemma snapshot_unmodeled : forall (regs : registers) (id : instr_id)
    (op : operation) (args : list value) (index : int),
  modeled_operation op args = false ->
  snapshot_value regs (Res id op args index)
    = snapshot_atom regs (Res id op args index).
Proof.
  intros regs id op args index Hmodeled.
  destruct op; try reflexivity; try discriminate;
    try (destruct op; try reflexivity; try discriminate);
    destruct args as [ | lhs [ | rhs [ | extra rest]]];
    cbn [modeled_operation snapshot_value] in *;
    try discriminate; try reflexivity; rewrite Hmodeled; reflexivity.
Qed.

(* Available actual values have their stored register value in the
   mathematical extension. The induction descends only through available
   canonical operands, whose equations follow from execution. *)
Theorem snapshot_agrees_available : forall (blocks : list block)
    (entry : block) (position : SsaDominance.point) (regs : registers),
  well_formed_ssa blocks entry -> coherent_at blocks entry regs position ->
  bounded_registers regs -> forall (v : value),
  available_value blocks entry position v ->
  snapshot_value regs v = snapshot_atom regs v.
Proof.
  intros blocks entry position regs Hwf Hcoherent Hbounded v.
  induction v as [id op args index IHargs | b index] using value_ind';
    intros Havailable; [ | reflexivity].
  destruct (modeled_operation op args) eqn:Hmodeled.
  2: { apply snapshot_unmodeled. exact Hmodeled. }
  specialize (Hcoherent _ Havailable).
  cbn [value_coherent] in Hcoherent. rewrite Hmodeled in Hcoherent.
  destruct Hcoherent as [words [result [Hread [Heval Hvalue]]]].
  eapply snapshot_evaluated_result; [exact Heval | | exact Hvalue].
  eapply read_values_snapshot; [exact Hbounded | exact Hread |].
  intros arg Hin. apply Forall_forall with (x := arg) in IHargs;
    [ | exact Hin].
  apply IHargs. eapply operand_available; eassumption.
Qed.

(* This is the bridge used by range proofs: no default or recomputation
   remains when the available value has an actual register reading. *)
Theorem snapshot_read_available : forall (blocks : list block) (entry : block)
    (position : SsaDominance.point) (regs : registers) (v : value) (word : Z),
  well_formed_ssa blocks entry -> coherent_at blocks entry regs position ->
  bounded_registers regs -> available_value blocks entry position v ->
  regs (register_of_value v) = Some word -> snapshot_value regs v = word.
Proof.
  intros blocks entry position regs v word Hwf Hcoherent Hbounded
    Havailable Hread.
  rewrite (snapshot_agrees_available _ _ _ _ Hwf Hcoherent Hbounded _
    Havailable).
  eapply snapshot_atom_read; eassumption.
Qed.
