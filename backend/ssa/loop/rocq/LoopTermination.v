(* Whether a loop terminates: its header's exit branch compares a basic
   induction variable with a loop-invariant bound in a way the variable's
   step must eventually make fail. The extraction of this file,
   LoopTermination.ml, is the implementation.

   See the reading guide at the top of LoopComparisons.v for the Rocq
   vocabulary; SsaModel.v for how the models see an SSA graph;
   NaturalLoop.v and InductionVar.v for the loops, their exit branches and
   the basic induction variables this file is given; LoopComparisons.v for
   the termination
   argument about a comparison and an induction variable, which this file
   applies; and AffineSsa.v for the facts a register bound is checked
   against. As there, the file has four parts: (1) the definitions, (2) the
   intended meaning, (3) stepping-stone lemmas, (4) the theorems. Parts 1
   and 2 are the part to check by eye.

   The type [t] here has the constructors [Terminates] and [Unknown], as
   does [LoopComparisons.termination]; the latter's are written qualified
   below.

   The result, in part 4, is [analyze_Terminates]: when the analysis says
   that a loop terminates, no run of the loop visits its header for ever.
   Part 2 says what a run is: the machine value of every SSA value at each
   visit of the header ([iter]), with what the loop passes rely on about
   the graph stated as hypotheses: what the recognised operations compute,
   that loop-invariant values do not change between visits, that the
   header's branch goes where its index says and that the next visit comes
   over a back edge whose [Goto] sets the header's parameters, and that
   the branches dominating the header went the way their dominating edges
   require. A run satisfying all of that for ever contradicts a
   [Terminates] verdict.

   The argument: by InductionVar.v the parameter the verdict rests on is
   updated by the same constant on every back edge, so its values at the
   visits form the sequence [iv] of LoopComparisons.v; the comparison the
   header tests compares that sequence (or its next value) with a bound
   that does not change; [loop_exits] there then gives a visit at which
   the test sends the run out of the loop, provided a literal bound is in
   range, which is checked directly, or a register bound is, which the
   facts gathered by [guards_at] entail ([guards_at_sound] makes them true
   on entry, [entails_sound] makes the goal follow). *)

From Stdlib Require Import ZArith Lia Bool List.
From OxCamlStdlib Require Import OxCamlOption OxCamlInt OxCamlInt64 OxCamlList.
From OxCamlBackend Require Import IntegerComparison.
From OxCamlSsa Require Import SsaModel SsaGraph.
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
   form overflows. *)
Definition bound_in_range (step : int) (header : block) (bound : bound)
    : bool :=
  match bound with
  | Const_bound k => if zero <? step then k <=? max_int else - max_int <=? k
  | Value_bound v =>
    let '((form, side), c) := linearize new_ctx [] (tree_of_value v) in
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
  match view_value cond with
  | Res _ (Op_comp_imm cmp x k) =>
    if is_iv_val x then Some (cmp, true, Const_bound k) else None
  | Res _ (Op_comp cmp x y) =>
    if is_iv_val x && is_bound y
    then Some (cmp, true, Value_bound y)
    else if is_iv_val y && is_bound x
    then Some (cmp, false, Value_bound x)
    else None
  | _ => None
  end.

(* Whether [biv]'s step must eventually make the exit comparison fail
   (LoopComparisons.v): then the loop terminates. *)
Definition biv_implies_termination (op_def : op_def) (biv : biv) : bool :=
  match find_exit_branch biv.(loop), signed_step biv with
  | Some exit_info, Some step =>
    let header := biv.(loop).(header) in
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

(* The verdict for the loop of [bivs], its basic induction variables: it
   terminates if one of them shows that it does. *)
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
Definition bound_value (iter0 : value -> Z) (b : bound) : Z :=
  match b with
  | Value_bound v => iter0 v
  | Const_bound k => to_Z k
  end.

(* A run of the loop [l] that visits the header for ever. [iter n v] is
   the machine value of the SSA value [v] as the run computes it during
   its [n]-th visit of the header (for a value defined before the loop,
   its value when the loop was entered). The fields are what the loop
   passes rely on about the graph; they are the trusted meaning of the
   views of SsaModel.v in one run.

   An execution that visits the header infinitely often gives such an
   [iter]. An execution stuck in an inner cycle need not do so:
   DeleteEmptyLoops.v separately checks that the body without the header
   is acyclic. For the visits described here, the header's parameters, the
   values of the body's blocks and the values of the blocks dominating the
   header take the values the execution computes (a value of an inner loop,
   computed several times between two visits, takes the first). Every other
   value is one the execution does not compute during the run (it is defined
   after the
   loop, or on another path); it is given the value of its operation on
   the values of its arguments when [iter_op] or [tree_sound] says what
   that is, and any 64-bit value otherwise. Nothing else constrains
   these: [iter_invariant] speaks only of values defined in blocks that
   strictly dominate the header. *)
Record infinite_header_run (op_def : op_def) (l : natural_loop)
    (iter : nat -> value -> Z) : Prop :=
  { (* Values are 64-bit registers. *)
    iter_bounded : forall n v, in_int64 (iter n v);

    (* What the recognised operations compute: addition and subtraction
       wrap at 64 bits, and a comparison is 1 or 0. *)
    iter_op : forall n v,
      match view_value v with
      | Res _ (Op_add x y) => iter n v = wrap64 (iter n x + iter n y)
      | Res _ (Op_sub x y) => iter n v = wrap64 (iter n x - iter n y)
      | Res _ (Op_add_imm x c) => iter n v = wrap64 (iter n x + to_Z c)
      | Res _ (Op_sub_imm x c) => iter n v = wrap64 (iter n x - to_Z c)
      | Res _ (Op_comp cmp x y) =>
        iter n v
        = bool_to_Z (IntegerComparison.eval cmp (iter n x) (iter n y))
      | Res _ (Op_comp_imm cmp x k) =>
        iter n v = bool_to_Z (IntegerComparison.eval cmp (iter n x) (to_Z k))
      | _ => True
      end;

    (* A value [is_loop_invariant] says is a constant, or is defined in a
       block strictly dominating the header, has the same value at every
       visit: such a block is not in the body, where the run stays between
       two visits ([run_continues], [run_back_edge]), so it does not run
       again. *)
    iter_invariant : forall n v,
      is_loop_invariant op_def l.(header) v = true ->
      iter n v = iter 0%nat v;

    (* The trees of [tree_of_value] are truthful of the values on entry
       (AffineSsa.v), and the branches dominating the header went the way
       their dominating edges require ([guards_taken], there). *)
    iter_trees : forall v, tree_sound (iter 0%nat) (tree_of_value v);
    iter_guards : guards_taken (iter 0%nat) l.(header);

    (* The atom counter of AffineSsa.v cannot wrap: the trees are small. *)
    trees_small : forall v,
      size (tree_of_value v) + 1 + guards_size l.(header) <= ocaml_max_int;

    (* The run goes on: at every visit, the header's [Switch] (control
       goes to [targets.(index)]) sends it into the loop body ... *)
    run_continues : forall n index targets,
      terminator l.(header) = Terminator.Switch index targets ->
      exists target,
        nth_error targets (Z.to_nat (iter n index)) = Some target
        /\ set_mem target l.(body) = true;

    (* ... and the next visit arrives over a back edge, whose [Goto]
       passes the header its parameters: the value of each parameter at
       the next visit is the value of the corresponding argument at this
       one. *)
    run_back_edge : forall n,
      exists s args,
        In s l.(back_edges) /\ In s (predecessors l.(header))
        /\ goto_args l.(header) s = Some args
        /\ forall i u, arg_value args i = Some u ->
             iter (S n) (param l.(header) i) = iter n u }.

Arguments iter_bounded {op_def l iter}.
Arguments iter_op {op_def l iter}.
Arguments iter_invariant {op_def l iter}.
Arguments iter_trees {op_def l iter}.
Arguments iter_guards {op_def l iter}.
Arguments trees_small {op_def l iter}.
Arguments run_continues {op_def l iter}.
Arguments run_back_edge {op_def l iter}.

Section Run.
  Variable op_def : op_def.
  Variable l : natural_loop.
  Variable iter : nat -> value -> Z.
  Hypothesis run : infinite_header_run op_def l iter.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

  (* --- The comparison the exit branch tests --- *)

  Lemma extract_comparison_spec :
    forall is_iv_val is_bound cond cmp iv_is_left bnd,
    extract_comparison is_iv_val is_bound cond = Some (cmp, iv_is_left, bnd) ->
    exists id,
      (exists x k, view_value cond = Res id (Op_comp_imm cmp x k)
         /\ is_iv_val x = true /\ iv_is_left = true /\ bnd = Const_bound k)
      \/ (exists x y, view_value cond = Res id (Op_comp cmp x y)
         /\ is_iv_val x = true /\ is_bound y = true
         /\ iv_is_left = true /\ bnd = Value_bound y)
      \/ (exists x y, view_value cond = Res id (Op_comp cmp x y)
         /\ is_iv_val y = true /\ is_bound x = true
         /\ iv_is_left = false /\ bnd = Value_bound x).
  Proof.
    intros is_iv_val is_bound cond cmp iv_is_left bnd H.
    unfold extract_comparison in H.
    destruct (view_value cond) as [id op | bl i] eqn:Hv; [ | discriminate ].
    destruct op as [ | x y | x y | x c | x c | cmp' x y | cmp' x k | ];
      try discriminate.
    - (* Op_comp *)
      destruct (is_iv_val x && is_bound y) eqn:H1.
      + injection H as <- <- <-. apply andb_true_iff in H1.
        destruct H1 as [Hx Hy].
        exists id. right. left. exists x, y.
        repeat split; try reflexivity; assumption.
      + destruct (is_iv_val y && is_bound x) eqn:H2; [ | discriminate ].
        injection H as <- <- <-. apply andb_true_iff in H2.
        destruct H2 as [Hy Hx].
        exists id. right. right. exists x, y.
        repeat split; try reflexivity; assumption.
    - (* Op_comp_imm *)
      destruct (is_iv_val x) eqn:Hx; [ | discriminate ].
      injection H as <- <- <-.
      exists id. left. exists x, k.
      repeat split; try reflexivity; assumption.
  Qed.

  (* --- The induction variable's values along the run --- *)

  (* A constant step comes from [self + c] or [self - c]. *)
  Lemma classify_update_const : forall is_self c sign u,
    classify_update is_self op_def l.(header) u = Some (Step_const c, sign) ->
    exists id x,
      is_self x = true
      /\ ((sign = Add /\ view_value u = Res id (Op_add_imm x c))
          \/ (sign = Sub /\ view_value u = Res id (Op_sub_imm x c))).
  Proof.
    intros is_self c sign u H. unfold classify_update in H.
    destruct (view_value u) as [id op | bl i] eqn:Hv; [ | discriminate ].
    destruct op as [ | x y | x y | x c0 | x c0 | cmp x y | cmp x k | ];
      try discriminate.
    - destruct (is_self x && _); [ discriminate | ].
      destruct (is_self y && _); discriminate.
    - destruct (is_self x && _); discriminate.
    - destruct (is_self x) eqn:Hx; [ | discriminate ].
      injection H as <- <-. exists id, x. split; [ exact Hx | ].
      left. split; reflexivity.
    - destruct (is_self x) eqn:Hx; [ | discriminate ].
      injection H as <- <-. exists id, x. split; [ exact Hx | ].
      right. split; reflexivity.
  Qed.

  (* Each update value is the parameter plus the signed step. *)
  Lemma biv_update_value : forall b st u n,
    biv_spec op_def l b -> signed_step b = Some st -> In u b.(update) ->
    iter n u
    = wrap64 (iter n (param l.(header) b.(param_index)) + to_Z st).
  Proof.
    intros b st u n Hspec Hstep Hu.
    destruct Hspec as [_ [_ [Hupd _]]].
    destruct (Hupd u Hu) as [step' [sign' [Hcl [Hss Hsg]]]].
    unfold signed_step in Hstep.
    destruct b.(step) as [c | w] eqn:Hbs; [ | discriminate ].
    destruct step' as [c' | w']; cbn [step_same] in Hss; [ | discriminate ].
    apply eqb_int in Hss. subst c'.
    destruct (classify_update_const _ _ _ _ Hcl) as [id [x [Hx Hcase]]].
    unfold is_param in Hx. apply value_eqb_spec in Hx. subst x.
    pose proof (run.(iter_op) n u) as Hop.
    destruct b.(sign) eqn:Hsign.
    - (* Add *)
      injection Hstep as <-.
      destruct sign'; cbn [sign_same] in Hsg; [ | discriminate ].
      destruct Hcase as [[_ Hv] | [Hab _]]; [ | discriminate ].
      rewrite Hv in Hop. cbv iota in Hop. exact Hop.
    - (* Sub *)
      destruct (c =? min_int)%sint63 eqn:Hmin; [ discriminate | ].
      injection Hstep as <-.
      destruct sign'; cbn [sign_same] in Hsg; [ discriminate | ].
      destruct Hcase as [[Hab _] | [_ Hv]]; [ discriminate | ].
      rewrite Hv in Hop. cbv iota in Hop. rewrite Hop.
      rewrite Sint63.to_Z_opp by (apply eqb_int_false; exact Hmin).
      f_equal; ring.
  Qed.

  (* The parameter's values at the visits are the sequence [iv]. *)
  Lemma self_sequence : forall b step,
    biv_spec op_def l b -> signed_step b = Some step ->
    forall n, iter n (param l.(header) b.(param_index))
              = iv (iter 0 (param l.(header) b.(param_index))) (to_Z step) n.
  Proof.
    intros b step Hspec Hstep n. induction n as [ | n IH ].
    - reflexivity.
    - destruct (run.(run_back_edge) n)
        as [s [args [Hs [Hpred [Hargs Hnext]]]]].
      pose proof Hspec as [_ [_ [_ [Hback _]]]].
      destruct (Hback s Hs Hpred) as [args' [u [Hargs' [Hu Hin]]]].
      rewrite Hargs in Hargs'. injection Hargs' as <-.
      rewrite (Hnext _ _ Hu). cbn [iv]. rewrite <- IH.
      apply biv_update_value; assumption.
  Qed.

  (* So are those of any value [is_iv_val] accepts: the
     parameter itself, or one of its updates (the sequence from its next
     value). *)
  Lemma iv_val_sequence : forall b step x,
    biv_spec op_def l b -> signed_step b = Some step ->
    is_param l.(header) b.(param_index) x
      || existsb (value_eqb x) b.(update) = true ->
    exists v0, in_int64 v0 /\ forall n, iter n x = iv v0 (to_Z step) n.
  Proof.
    intros b step x Hspec Hstep Hx. apply orb_true_iff in Hx.
    destruct Hx as [Hself | Hupd].
    - unfold is_param in Hself. apply value_eqb_spec in Hself.
      subst x.
      exists (iter 0 (param l.(header) b.(param_index))).
      split; [ apply run.(iter_bounded) | ].
      intros n. apply self_sequence; assumption.
    - apply existsb_exists in Hupd. destruct Hupd as [u [Hin Hequ]].
      apply value_eqb_spec in Hequ. subst x.
      exists (wrap64 (iter 0 (param l.(header) b.(param_index)) + to_Z step)).
      split; [ apply wrap64_in_range | ].
      intros n. rewrite <- iv_shift. cbn [iv].
      rewrite <- (self_sequence b step Hspec Hstep n).
      apply biv_update_value; assumption.
  Qed.

  (* --- The bound --- *)

  (* The facts [bound_in_range] checks a register bound against hold
     under a valuation that reads the bound's form as its value. *)
  Lemma value_bound_facts : forall v form side1 c1 guards side2 c2,
    linearize new_ctx [] (tree_of_value v) = ((form, side1), c1) ->
    guards_at c1 side1 l.(header) = ((guards, side2), c2) ->
    exists rho,
      denote rho form = iter 0 v
      /\ Forall wf (guards ++ side2) /\ wf form
      /\ holds_all rho (guards ++ side2).
  Proof.
    intros v form side1 c1 guards side2 c2 Hlin Hg.
    assert (Heqb : forall v w, value_eqb v w = true -> iter 0 v = iter 0 w).
    { intros v' w E. apply value_eqb_spec in E. subst w. reflexivity. }
    assert (Hwf0 : ctx_wf new_ctx).
    { split; [ constructor | intros id w Hin; destruct Hin ]. }
    assert (Hn0 : to_Z new_ctx.(next) = 0) by exact to_Z_zero.
    pose proof (run.(trees_small) v) as Hsmall.
    assert (Hgs : 0 <= guards_size l.(header)) by apply guards_sum_nonneg.
    pose proof (size_pos (tree_of_value v)) as Hsz.
    destruct (linearize_sound (iter 0) (run.(iter_bounded) 0) Heqb
                (tree_of_value v) new_ctx [] form side1 c1 (run.(iter_trees) v)
                Hwf0 ltac:(lia) Hlin)
      as [Hwf1 [_ [Hn1 [Hwff [Hwfs1 Hrho1]]]]].
    destruct (guards_at_sound (iter 0) (run.(iter_bounded) 0) Heqb l.(header)
                c1 side1 guards side2 c2 run.(iter_trees) Hwf1 ltac:(lia) Hg)
      as [Hwf2 [He12 [_ [Hwfg [Hwfs2 Hrho2]]]]].
    destruct (agrees_exists (iter 0) c2 Hwf2) as [rho Hrho].
    destruct (Hrho2 rho Hrho) as [Hs2 Hg2].
    destruct (Hrho1 rho (agrees_extends _ _ _ _ He12 Hrho)) as [Hden Hs1].
    rewrite tree_of_value_root in Hden.
    exists rho. split; [ exact Hden | ].
    split; [ apply Forall_app; split; [ exact Hwfg | ] | ].
    { apply Hwfs2, Hwfs1. exact (Forall_nil _). }
    split; [ exact Hwff | ].
    unfold holds_all. apply Forall_app. split.
    - apply Hg2, run.(iter_guards).
    - apply Hs2, Hs1. exact (Forall_nil _).
  Qed.

  (* [bound_in_range] establishes the side condition of
     LoopComparisons.v on the bound's value. *)
  Lemma bound_in_range_sound : forall step bnd,
    bound_in_range step l.(header) bnd = true ->
    LoopComparisons.bound_in_range (to_Z step) (bound_value (iter 0) bnd)
    = true.
  Proof.
    intros step bnd H.
    unfold LoopComparisons.bound_in_range. rewrite Z.gtb_ltb.
    assert (Hpos : (zero <? step)%sint63 = (0 <? to_Z step)).
    { destruct (zero <? step)%sint63 eqn:E; symmetry.
      - apply Z.ltb_lt. rewrite <- to_Z_zero. apply ltb_int. exact E.
      - apply Z.ltb_ge.
        destruct (Z.lt_ge_cases 0 (to_Z step)) as [C | C]; [ | exact C ].
        exfalso. rewrite <- to_Z_zero in C. apply ltb_int in C.
        rewrite C in E. discriminate. }
    unfold bound_in_range in H. cbv zeta in H. rewrite Hpos in H.
    destruct bnd as [v | k]; cbn [bound_value].
    - (* Value_bound *)
      destruct (linearize new_ctx [] (tree_of_value v))
        as [[form side1] c1] eqn:Hlin.
      destruct (guards_at c1 side1 l.(header)) as [[guards side2] c2] eqn:Hg.
      destruct (value_bound_facts v form side1 c1 guards side2 c2 Hlin Hg)
        as [rho [Hden [Hwffacts [Hwff Hfacts]]]].
      destruct (0 <? to_Z step) eqn:Hp; cbv iota in H.
      + destruct (Affine.scale_checked minus_one form) as [nf | ] eqn:Hsc;
          [ | discriminate ].
        cbv iota in H.
        destruct (Affine.add_const_checked nf max_int) as [goal | ] eqn:Hac;
          [ | discriminate ].
        cbv iota in H.
        destruct (scale_checked_spec rho _ _ _ Hsc) as [Hd1 [_ Hwf1]].
        destruct (add_const_checked_spec rho _ _ _ Hac) as [Hd2 [_ Hwf2]].
        pose proof (entails_sound _ _ Hwffacts (Hwf2 (Hwf1 Hwff)) H rho Hfacts)
          as Hgoal.
        rewrite Hd2, Hd1, to_Z_minus_one, to_Z_max_int, Hden in Hgoal.
        apply Z.leb_le. unfold ocaml_max_int. lia.
      + destruct (Affine.add_const_checked form max_int) as [goal | ] eqn:Hac;
          [ | discriminate ].
        cbv iota in H.
        destruct (add_const_checked_spec rho _ _ _ Hac) as [Hd2 [_ Hwf2]].
        pose proof (entails_sound _ _ Hwffacts (Hwf2 Hwff) H rho Hfacts)
          as Hgoal.
        rewrite Hd2, to_Z_max_int, Hden in Hgoal.
        apply Z.leb_le. unfold ocaml_max_int. lia.
    - (* Const_bound *)
      destruct (0 <? to_Z step).
      + apply leb_int in H. rewrite to_Z_max_int in H.
        apply Z.leb_le. exact H.
      + apply leb_int in H. rewrite Sint63.to_Z_opp in H.
        * rewrite to_Z_max_int in H. apply Z.leb_le.
          unfold ocaml_max_int. lia.
        * intros E. apply (f_equal to_Z) in E.
          rewrite to_Z_max_int, to_Z_min_int in E. unfold two62 in E. lia.
  Qed.

(* ======================================================================== *)
(* Part 4: theorems                                                         *)
(* ======================================================================== *)

  (* No run of a loop the analysis says terminates visits the header for
     ever: the hypotheses of this section, together with a [Terminates]
     verdict for the loop's basic induction variables (any list of which
     the meaning of InductionVar.v holds), are contradictory. *)
  Theorem analyze_Terminates : forall bivs,
    (forall b, In b bivs -> biv_spec op_def l b) ->
    analyze op_def bivs = Terminates -> False.
  Proof.
    intros bivs Hbivs H. unfold analyze in H.
    destruct (existsb (biv_implies_termination op_def) bivs) eqn:He;
      [ | discriminate ].
    apply existsb_exists in He. destruct He as [b [Hin Hb]].
    specialize (Hbivs b Hin). pose proof Hbivs as Hspec.
    destruct Hbivs as [Hl _].
    unfold biv_implies_termination in Hb. rewrite Hl in Hb.
    destruct (find_exit_branch l) as [eb | ] eqn:Hexit; [ | discriminate ].
    destruct (signed_step b) as [step | ] eqn:Hstep; [ | discriminate ].
    cbv iota zeta beta in Hb.
    destruct (extract_comparison _ _ eb.(condition))
      as [[[cmp iv_is_left] bnd] | ] eqn:Hext; [ | discriminate ].
    cbv zeta in Hb.
    destruct (find_exit_branch_spec l eb Hexit)
      as [ifnot [ifso [Ht [Hso Hnot]]]].
    (* The verdict, with its side condition discharged. *)
    assert (Hverdict :
      continue_terminates step
        (oriented_continue_comparison iv_is_left eb.(continue_when_true) cmp)
      = LoopComparisons.Terminates
      \/ (continue_terminates step
            (oriented_continue_comparison iv_is_left eb.(continue_when_true)
               cmp)
          = LoopComparisons.Terminates_if_bound_in_range
          /\ LoopComparisons.bound_in_range (to_Z step)
               (bound_value (iter 0) bnd) = true)).
    { destruct (continue_terminates step
                  (oriented_continue_comparison iv_is_left
                     eb.(continue_when_true) cmp)) eqn:Hct; cbv iota in Hb.
      - left. reflexivity.
      - right. split; [ reflexivity | apply bound_in_range_sound; exact Hb ].
      - discriminate. }
    (* The comparison tested at each visit, on the sequence [iv]. *)
    destruct (extract_comparison_spec _ _ _ _ _ _ Hext) as [id Hcases].
    assert (Hseq : exists v0, in_int64 v0
      /\ forall n, iter n eb.(condition)
           = bool_to_Z
               (if iv_is_left
                then IntegerComparison.eval cmp (iv v0 (to_Z step) n)
                       (bound_value (iter 0) bnd)
                else IntegerComparison.eval cmp (bound_value (iter 0) bnd)
                       (iv v0 (to_Z step) n))).
    { destruct Hcases
        as [ [x [k [Hv [Hx [-> ->]]]]]
           | [ [x [y [Hv [Hx [Hy [-> ->]]]]]]
             | [x [y [Hv [Hy [Hx [-> ->]]]]]] ] ].
      - destruct (iv_val_sequence b step x Hspec Hstep Hx) as [v0 [Hv0 Hiter]].
        exists v0. split; [ exact Hv0 | ]. intros n.
        pose proof (run.(iter_op) n eb.(condition)) as Hop.
        rewrite Hv in Hop. cbv iota in Hop.
        rewrite Hop, Hiter. reflexivity.
      - destruct (iv_val_sequence b step x Hspec Hstep Hx) as [v0 [Hv0 Hiter]].
        exists v0. split; [ exact Hv0 | ]. intros n.
        pose proof (run.(iter_op) n eb.(condition)) as Hop.
        rewrite Hv in Hop. cbv iota in Hop.
        rewrite Hop, Hiter, (run.(iter_invariant) n y Hy). reflexivity.
      - destruct (iv_val_sequence b step y Hspec Hstep Hy) as [v0 [Hv0 Hiter]].
        exists v0. split; [ exact Hv0 | ]. intros n.
        pose proof (run.(iter_op) n eb.(condition)) as Hop.
        rewrite Hv in Hop. cbv iota in Hop.
        rewrite Hop, Hiter, (run.(iter_invariant) n x Hx). reflexivity. }
    destruct Hseq as [v0 [Hv0 Hiter]].
    assert (Hbnd : in_int64 (bound_value (iter 0) bnd)).
    { destruct bnd as [v | k]; cbn [bound_value];
        [ apply run.(iter_bounded) | ].
      pose proof (int_bounds k). unfold in_int64, two62, two63 in *. lia. }
    (* LoopComparisons.v: a visit at which the test fails ... *)
    destruct (loop_exits iv_is_left eb.(continue_when_true) cmp step v0
                (bound_value (iter 0) bnd) Hv0 Hbnd Hverdict) as [n Hn].
    (* ... which the run says sends it into the loop body. *)
    destruct (run.(run_continues) n eb.(condition) [ifnot; ifso] Ht)
      as [target [Hnth Htarget]].
    rewrite Hiter in Hnth. unfold loop_continues in Hn. cbv zeta in Hn.
    destruct eb.(continue_when_true) eqn:Hcwt.
    - rewrite Hn in Hnth. cbn in Hnth. injection Hnth as <-.
      rewrite Htarget in Hnot. discriminate.
    - apply negb_false_iff in Hn. rewrite Hn in Hnth. cbn in Hnth.
      injection Hnth as <-.
      rewrite Htarget in Hso. discriminate.
  Qed.

  (* The same for the basic induction variables InductionVar.v reports
     for the loop. *)
  Theorem analyze_Terminates_of_graph : forall blocks bivs,
    In (l, bivs) (InductionVar.analyze op_def blocks) ->
    analyze op_def bivs = Terminates -> False.
  Proof.
    intros blocks bivs Hin H.
    destruct (analyze_spec _ _ _ _ Hin) as [_ [_ Hbivs]].
    exact (analyze_Terminates bivs Hbivs H).
  Qed.

End Run.
