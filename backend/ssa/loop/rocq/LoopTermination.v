(* Whether a loop terminates: its header's exit branch compares a basic
   induction variable with a loop-invariant bound in a way the variable's
   step must eventually make fail. The extraction of this file,
   LoopTermination.ml, is the implementation.

   See the reading guide at the top of LoopComparisons.v for the Rocq
   vocabulary; SsaModel.v for how the models see an SSA graph;
   NaturalLoop.v and InductionVar.v for the loops, their exit branches and
   the basic induction variables this file is given; LoopComparisons.v for
   the arithmetic termination argument; and AffineSsa.v for the facts a
   register bound is checked
   against. As there, the file has four parts: (1) the definitions, (2) the
   intended meaning, (3) stepping-stone lemmas, (4) the theorems. Review
   parts 1 and 2 and the theorem statements; Rocq checks the proofs.

   The type [t] here has the constructors [Terminates] and [Unknown], as
   does [LoopComparisons.termination]; the latter's are written qualified
   below.

   The read-back lemmas expose the accepted comparison and counter rule.
   LoopCounterExecution.v connects these to actual finite execution,
   including register bounds justified by affine entry guards. *)

From Stdlib Require Import ZArith Lia Bool List.
From OxCamlStdlib Require Import OxCamlOption OxCamlInt OxCamlInt64 OxCamlList.
From OxCamlBackend Require Import IntegerComparison Operation.
From OxCamlSsa Require Import SsaModel SsaGraph SsaDominance.
From OxCamlLoop Require Import FourierMotzkin LoopComparisons AffineExpr
  NaturalLoop AffineSsa InductionVar.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: the definitions                                                  *)
(* ======================================================================== *)

Local Open Scope sint63_scope.

(* The verdict. *)
Inductive t : Type :=
  | Terminates
  | Unknown.

(* The other operand of the exit comparison. *)
Inductive bound : Type :=
  | Value_bound (v : value)
  | Const_bound (k : int).

(* Whether the bound is in the range part 2 of LoopComparisons.v asks for:
   for a constant, by comparison; for a value, by asking whether the facts
   holding at the header (AffineSsa.v) entail it; [false] when an affine
   form overflows.

   A literal bound is an [int], so [k <= max_int] always holds and
   [- max_int <= k] fails only for [min_int]: for literal bounds the whole
   argument is in [continue_terminates]. A register bound needs the facts
   to pin it within [[- max_int, max_int]]; the affine constants are
   [int]s too, so a fact such as [b + 2^62 >= 0] cannot be written, and
   the lower bound of an arithmetic shift by one bit ([>>s 1], the shape
   of an untagged bound) is not available (AffineExpr.shr_range_facts).
   This is why a [downto] loop with such a bound is not deleted while the
   corresponding [to] loop is. *)
Definition bound_in_range (step : int) (header : block) (bound : bound)
    : bool :=
  match bound with
  | Const_bound k => if zero <? step then k <=? max_int else - max_int <=? k
  | Value_bound v =>
    let '((form, side), c) := linearize new_ctx [] v in
    let '((guards, side), c) := guards_at c side header in
    let facts := guards ++ side in
    let goal :=
      if zero <? step
      then
        let* f := Affine.scale_checked minus_one form in
        Affine.add_const_checked f max_int
      else Affine.add_const_checked form max_int
    in
    match goal with
    | Some goal => entails facts goal
    | None => false
    end
  end.

(* The comparison the exit branch tests, whether the induction variable
   is its left operand, and the other operand. *)
Definition extract_comparison (is_iv_val is_bound : value -> bool)
    (cond : value) : option (integer_comparison * bool * bound) :=
  match cond with
  | Res _ (Intop_imm (Icomp cmp) k) [x] _ =>
    if is_iv_val x then Some (cmp, true, Const_bound k) else None
  | Res _ (Intop (Icomp cmp)) [x; y] _ =>
    if is_iv_val x && is_bound y
    then Some (cmp, true, Value_bound y)
    else if is_iv_val y && is_bound x
    then Some (cmp, false, Value_bound x)
    else None
  | _ => None
  end.

(* Whether [biv]'s step must eventually make the exit comparison fail
   (LoopComparisons.v): then the loop terminates. Sound for a [biv]
   satisfying [biv_spec] (InductionVar.v): [biv_implies_termination_spec]
   reads it back. *)
Definition biv_implies_termination (op_def : op_def) (biv : biv) : bool :=
  match find_exit_branch biv.(InductionVar.loop), signed_step biv with
  | Some exit_info, Some step =>
    let header := biv.(InductionVar.loop).(header) in
    let is_self := is_param header biv.(param_index) in
    let is_iv_val v := is_self v || existsb (value_eqb v) biv.(update) in
    let is_bound v := is_loop_invariant op_def header v in
    match extract_comparison is_iv_val is_bound exit_info.(condition) with
    | None => false
    | Some (cmp, iv_is_left, bound) =>
      let continue_cmp :=
        oriented_continue_comparison iv_is_left
          exit_info.(continue_when_true) cmp
      in
      match continue_terminates step continue_cmp with
      | LoopComparisons.Terminates => true
      | LoopComparisons.Terminates_if_bound_in_range =>
        bound_in_range step header bound
      | LoopComparisons.Unknown => false
      end
    end
  | None, _ | Some _, None => false
  end.

(* Accept if one of the supplied induction variables proves termination.
   DeleteEmptyLoops.v connects these variables to loop discovery. *)
Definition analyze (op_def : op_def) (bivs : list biv) : t :=
  if existsb (biv_implies_termination op_def) bivs
  then Terminates
  else Unknown.

Local Close Scope sint63_scope.

(* ======================================================================== *)
(* Part 2: the intended meaning                                             *)
(* ======================================================================== *)

Local Open Scope Z_scope.

(* The machine value of a comparison: 1 for true, 0 for false. *)
Definition bool_to_Z (b : bool) : Z := if b then 1 else 0.

(* The value a bound stands for, given the values on entry to the loop. *)
Definition bound_value (iter0 : value -> Z) (bnd : bound) : Z :=
  match bnd with
  | Value_bound v => iter0 v
  | Const_bound k => to_Z k
  end.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

(* A literal-bound range check depends only on machine-int comparisons,
   not on a run, entry guards or a valuation of SSA expressions. *)
Lemma constant_bound_in_range : forall (step_size : int) (header : block)
    (limit : int),
  bound_in_range step_size header (Const_bound limit) = true ->
  LoopComparisons.bound_in_range (to_Z step_size) (to_Z limit) = true.
Proof.
  intros step_size header limit Hcheck.
  unfold bound_in_range in Hcheck. cbv zeta in Hcheck.
  rewrite zero_ltb_to_Z in Hcheck.
  unfold LoopComparisons.bound_in_range. rewrite Z.gtb_ltb.
  destruct (0 <? to_Z step_size)%Z.
  - apply leb_int in Hcheck. rewrite to_Z_max_int in Hcheck.
    apply Z.leb_le. exact Hcheck.
  - apply leb_int in Hcheck. rewrite Sint63.to_Z_opp in Hcheck.
    + rewrite to_Z_max_int in Hcheck. apply Z.leb_le.
      unfold ocaml_max_int. lia.
    + intros Heq. apply (f_equal to_Z) in Heq.
      rewrite to_Z_max_int, to_Z_min_int in Heq. unfold two62 in Heq. lia.
Qed.

Section Recognition.
  Variable op_def : op_def.
  Variable loop : natural_loop.

  (* --- The comparison the exit branch tests --- *)

  (* What [extract_comparison] found: [cond] compares a value [is_iv_val]
     accepts with a literal, or with a value [is_bound] accepts on either
     side, [iv_is_left] saying which. *)
  Lemma extract_comparison_spec :
    forall (is_iv_val is_bound : value -> bool) (cond : value)
      (cmp : integer_comparison) (iv_is_left : bool) (bnd : bound),
    extract_comparison is_iv_val is_bound cond = Some (cmp, iv_is_left, bnd) ->
    exists id i,
      (exists x k,
         cond = Res id (Intop_imm (Icomp cmp) k) [x] i
         /\ is_iv_val x = true /\ iv_is_left = true /\ bnd = Const_bound k)
      \/ (exists x y,
         cond = Res id (Intop (Icomp cmp)) [x; y] i
         /\ is_iv_val x = true /\ is_bound y = true
         /\ iv_is_left = true /\ bnd = Value_bound y)
      \/ (exists x y,
         cond = Res id (Intop (Icomp cmp)) [x; y] i
         /\ is_iv_val y = true /\ is_bound x = true
         /\ iv_is_left = false /\ bnd = Value_bound x).
  Proof.
    intros is_iv_val is_bound cond cmp iv_is_left bnd H.
    unfold extract_comparison in H.
    destruct cond as [id op args i | bl i]; [ | discriminate ].
    destruct op as [ | | | ? | ? | ? | ? | ? | ? | ? | ? | ? | ? | ? ? ? | iop
                   | ? | iop k | ? | ? ? | ? | ? | ? | ? | | | | ? | ? | | | |
                   | | ? ];
      try discriminate; destruct iop; try discriminate;
      destruct args as [ | x [ | y [ | ? ? ] ] ]; try discriminate.
    - (* Intop (Icomp cmp'), [x; y] *)
      destruct (is_iv_val x && is_bound y) eqn:H1.
      + injection H as <- <- <-. apply andb_true_iff in H1.
        destruct H1 as [Hx Hy].
        exists id, i. right. left. exists x, y.
        repeat split; try reflexivity; assumption.
      + destruct (is_iv_val y && is_bound x) eqn:H2; [ | discriminate ].
        injection H as <- <- <-. apply andb_true_iff in H2.
        destruct H2 as [Hy Hx].
        exists id, i. right. right. exists x, y.
        repeat split; try reflexivity; assumption.
    - (* Intop_imm (Icomp cmp') k, [x] *)
      destruct (is_iv_val x) eqn:Hx; [ | discriminate ].
      injection H as <- <- <-.
      exists id, i. left. exists x, k.
      repeat split; try reflexivity; assumption.
  Qed.

  (* --- The induction variable's update --- *)

  (* A constant step comes from [self + c] or [self - c]. *)
  Lemma classify_update_const :
    forall (is_self : value -> bool) (c : int) (sign : biv_sign) (u : value),
    classify_update is_self op_def loop.(header) u
      = Some (Step_const c, sign) ->
    exists id i x,
      is_self x = true
      /\ ((sign = Add /\ u = Res id (Intop_imm Iadd c) [x] i)
          \/ (sign = Sub /\ u = Res id (Intop_imm Isub c) [x] i)).
  Proof.
    intros is_self c sign u H. unfold classify_update in H.
    destruct u as [id op args i | bl i]; [ | discriminate ].
    destruct op as [ | | | ? | ? | ? | ? | ? | ? | ? | ? | ? | ? | ? ? ? | iop
                   | ? | iop c0 | ? | ? ? | ? | ? | ? | ? | | | | ? | ? | | | |
                   | | ? ];
      try discriminate; destruct iop; try discriminate;
      destruct args as [ | x [ | y [ | ? ? ] ] ]; try discriminate.
    - destruct (is_self x && _); [ discriminate | ].
      destruct (is_self y && _); discriminate.
    - destruct (is_self x && _); discriminate.
    - destruct (is_self x) eqn:Hx; [ | discriminate ].
      injection H as <- <-. exists id, i, x. split; [ exact Hx | ].
      left. split; reflexivity.
    - destruct (is_self x) eqn:Hx; [ | discriminate ].
      injection H as <- <-. exists id, i, x. split; [ exact Hx | ].
      right. split; reflexivity.
  Qed.

(* ======================================================================== *)
(* Part 4: theorems                                                         *)
(* ======================================================================== *)

  (* What [biv_implies_termination] accepting [biv], a BIV of [loop], says:
     the header has an exit branch [exit_info], [biv] a literal step, the
     exit comparison the shape [extract_comparison] reads, and the verdict
     of LoopComparisons.v on them is [Terminates], or
     [Terminates_if_bound_in_range] with the bound checked in range. *)
  Lemma biv_implies_termination_spec : forall (biv : biv),
    biv.(InductionVar.loop) = loop ->
    biv_implies_termination op_def biv = true ->
    exists exit_info step cmp iv_is_left bnd,
      find_exit_branch loop = Some exit_info
      /\ signed_step biv = Some step
      /\ extract_comparison
           (fun v => is_param loop.(header) biv.(param_index) v
                     || existsb (value_eqb v) biv.(update))
           (is_loop_invariant op_def loop.(header)) exit_info.(condition)
         = Some (cmp, iv_is_left, bnd)
      /\ (continue_terminates step
            (oriented_continue_comparison iv_is_left
               exit_info.(continue_when_true) cmp)
          = LoopComparisons.Terminates
          \/ (continue_terminates step
                (oriented_continue_comparison iv_is_left
                   exit_info.(continue_when_true) cmp)
              = LoopComparisons.Terminates_if_bound_in_range
              /\ bound_in_range step loop.(header) bnd = true)).
  Proof.
    intros b Hl Hb. unfold biv_implies_termination in Hb. rewrite Hl in Hb.
    destruct (find_exit_branch loop) as [eb | ] eqn:Hexit; [ | discriminate ].
    destruct (signed_step b) as [step | ] eqn:Hstep; [ | discriminate ].
    cbv iota zeta beta in Hb.
    destruct (extract_comparison _ _ eb.(condition))
      as [[[cmp iv_is_left] bnd] | ] eqn:Hext; [ | discriminate ].
    cbv zeta in Hb.
    exists eb, step, cmp, iv_is_left, bnd.
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ first [ reflexivity | exact Hext ] | ].
    destruct (continue_terminates step
                (oriented_continue_comparison iv_is_left
                   eb.(continue_when_true) cmp)) eqn:Hct; cbv iota in Hb.
    - left. reflexivity.
    - right. split; [ reflexivity | exact Hb ].
    - discriminate.
  Qed.

End Recognition.
