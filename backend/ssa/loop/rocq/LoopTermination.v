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
   that a loop terminates, no run of the loop goes on for ever. Part 2
   says what a run is and what it means for one to go on for ever
   ([infinite_header_run]): the machine value of every SSA value at each
   visit of the header ([iter]), with what the loop passes rely on about
   the graph stated as hypotheses, in three groups: what the machine
   computes ([machine_values]); how the loop was entered, with the values
   from outside it fixed ([loop_entry]); and that the run never leaves,
   the header's branch going into the body and the next visit arriving
   over a back edge ([stays_in_loop]). A run satisfying all of that for
   ever contradicts a [Terminates] verdict.

   The argument, as the lemmas of part 3 cut it: by InductionVar.v the
   parameter the verdict rests on is updated by the same constant on every
   back edge, so its values at the visits form the sequence [iv] of
   LoopComparisons.v, and the exit comparison tests that sequence (or its
   next value) against a bound that does not change
   ([exit_test_sequence]); [loop_exits] there gives a visit at which the
   test fails, provided a literal bound is in range, which is checked
   directly, or a register bound is, which the facts gathered by
   [guards_at] entail ([bound_in_range_sound]); but at every visit of a
   run the test comes out the continuing way ([run_test_continues]). *)

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
  | Res _ (Intop_imm (Operation.Icomp cmp) k) [x] =>
    if is_iv_val x then Some (cmp, true, Const_bound k) else None
  | Res _ (Intop (Operation.Icomp cmp)) [x; y] =>
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
   terminates if one of them shows that it does. Sound only when [bivs]
   are basic induction variables of one loop ([bivs_of_loop], part 2), as
   the lists [InductionVar.analyze] builds are: [analyze_Terminates]. *)
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

(* The precondition of [analyze]: [bivs] are basic induction variables of
   the loop [l], in the sense of InductionVar.v. [InductionVar.analyze_spec]
   establishes it for the lists that analysis builds. *)
Definition bivs_of_loop (op_def : op_def) (l : natural_loop)
    (bivs : list biv) : Prop :=
  forall b, In b bivs -> biv_spec op_def l b.

(* --- A run of the loop that goes on for ever --- *)

(* A run of the loop [l] is a sequence of consecutive visits of its header
   between which control stays in the body of [l]: it starts when the
   header is entered from outside the loop and ends when the header's
   branch leaves the body (a later visit of the header belongs to another
   run). The loop does not terminate when some run never ends. Because the
   body minus the header is acyclic (DeleteEmptyLoops.v checks it), such a
   run visits the header infinitely often, and is described by [iter]:
   [iter n v] is the machine value of the SSA value [v] during the [n]-th
   visit of the header. For the header's parameters, the values of the
   body's blocks and the values of the blocks dominating the header, that
   is the value the execution computes (for a value defined before the
   loop, its value when the loop was entered). Every other value is one
   the execution does not compute during the run (it is defined after the
   loop, or on another path); it is given the value of its operation on
   the values of its arguments when the hypotheses below say what that is,
   and any 64-bit value otherwise.

   [infinite_header_run] states what is then true of [iter], in three
   groups. It is the trusted meaning of the views of SsaModel.v in one
   run: a reviewer checks that each hypothesis holds of a real execution
   that never leaves [l]; the model proves that no [iter] satisfies them
   all for a loop [analyze] says terminates ([analyze_Terminates]). *)

(* What the machine computes, at every visit. *)
Record machine_values (iter : nat -> value -> Z) : Prop :=
  { (* Values are 64-bit registers. *)
    iter_bounded : forall n v, in_int64 (iter n v);

    (* The recognised operations: addition and subtraction wrap at 64
       bits, and a comparison is 1 or 0. *)
    iter_op : forall n v,
      match view_value v with
      | Res _ (Intop Operation.Iadd) [x; y] =>
        iter n v = wrap64 (iter n x + iter n y)
      | Res _ (Intop Operation.Isub) [x; y] =>
        iter n v = wrap64 (iter n x - iter n y)
      | Res _ (Intop_imm Operation.Iadd c) [x] =>
        iter n v = wrap64 (iter n x + to_Z c)
      | Res _ (Intop_imm Operation.Isub c) [x] =>
        iter n v = wrap64 (iter n x - to_Z c)
      | Res _ (Intop (Operation.Icomp cmp)) [x; y] =>
        iter n v
        = bool_to_Z (IntegerComparison.eval cmp (iter n x) (iter n y))
      | Res _ (Intop_imm (Operation.Icomp cmp) k) [x] =>
        iter n v = bool_to_Z (IntegerComparison.eval cmp (iter n x) (to_Z k))
      | _ => True
      end }.

(* How the run entered the loop, [entry] being the graph's entry block:
   what held of the values on entry, and still holds at every visit of
   the values from outside the loop. *)
Record loop_entry (entry : block) (op_def : op_def) (l : natural_loop)
    (iter : nat -> value -> Z) : Prop :=
  { (* [dominates] means what SsaDominance.v says it means. *)
    run_dominance : dominance_semantics entry;

    (* The trees of [tree_of_value] are truthful of the values on entry
       (AffineSsa.v). *)
    iter_trees : forall v, tree_sound (iter 0%nat) (tree_of_value v);

    (* The branch of a block [d] whose terminator is [Switch index [ifnot;
       ifso]] goes to [ifso] when the comparison [index] holds and to
       [ifnot] when it fails. When every path from the entry to the header
       takes the edge to [ifso] (or, [negate], the edge to [ifnot]), the
       execution took it, so the comparison held (failed) on entry. *)
    iter_branches : forall d index ifnot ifso (negate : bool),
      terminator d = Terminator.Switch index [ifnot; ifso] ->
      (forall p, path entry p l.(header) ->
         edge_on p d (if negate then ifnot else ifso)) ->
      test_result (iter 0%nat) negate (tree_of_value index);

    (* A loop-invariant value (InductionVar.v: a constant, or one defined
       in a block that dominates the header and is not it) has the same
       value at every visit: its block is not in the body, where the run
       stays between two visits, so it does not run again. *)
    iter_invariant : forall n v,
      loop_invariant_value op_def l.(header) v -> iter n v = iter 0%nat v }.

(* The run never leaves the loop. *)
Record stays_in_loop (l : natural_loop) (iter : nat -> value -> Z) : Prop :=
  { (* At every visit the header's [Switch] (control goes to
       [targets.(index)]) sends the run into the body ... *)
    run_continues : forall n index targets,
      terminator l.(header) = Terminator.Switch index targets ->
      exists target,
        nth_error targets (Z.to_nat (iter n index)) = Some target
        /\ set_mem target l.(body) = true;

    (* ... and the next visit arrives over a back edge, whose terminator
       is a [Goto] to the header: the value of each parameter at the next
       visit is the value of the corresponding argument at this one. Every
       block of the body is dominated by the header (it reaches a back
       edge without passing through the header, so a path to it avoiding
       the header would give one to that back edge), so an edge from the
       body into the header is a back edge, and a run that stays in the
       body can arrive no other way. *)
    run_back_edge : forall n,
      exists s args,
        In s l.(back_edges) /\ In s (predecessors l.(header))
        /\ terminator s = Terminator.Continue (Goto l.(header)) args
        /\ forall i u, nth_int args i = Some (Terminator.Arg u) ->
             iter (S n) (param l.(header) i) = iter n u }.

(* A bound on the graph, not on the run: the atom counter of AffineSsa.v,
   an OxCaml [int], cannot wrap while the bound and the header's guards
   are linearized. [Ssa_view.tree_of_value] builds at most 256 nodes, so
   this only fails for a header with some 2^53 dominators. *)
Definition atom_counter_fits (l : natural_loop) : Prop :=
  forall v,
    size (tree_of_value v) + 1 + guards_size l.(header) <= ocaml_max_int.

Record infinite_header_run (entry : block) (op_def : op_def)
    (l : natural_loop) (iter : nat -> value -> Z) : Prop :=
  { run_machine : machine_values iter;
    run_entry : loop_entry entry op_def l iter;
    run_stays : stays_in_loop l iter;
    run_atoms_fit : atom_counter_fits l }.

Arguments iter_bounded {iter}.
Arguments iter_op {iter}.
Arguments run_dominance {entry op_def l iter}.
Arguments iter_trees {entry op_def l iter}.
Arguments iter_branches {entry op_def l iter}.
Arguments iter_invariant {entry op_def l iter}.
Arguments run_continues {l iter}.
Arguments run_back_edge {l iter}.
Arguments run_machine {entry op_def l iter}.
Arguments run_entry {entry op_def l iter}.
Arguments run_stays {entry op_def l iter}.
Arguments run_atoms_fit {entry op_def l iter}.

Section Run.
  Variable entry : block.
  Variable op_def : op_def.
  Variable l : natural_loop.
  Variable iter : nat -> value -> Z.
  Hypothesis run : infinite_header_run entry op_def l iter.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

  (* --- The comparison the exit branch tests --- *)

  Lemma extract_comparison_spec :
    forall is_iv_val is_bound cond cmp iv_is_left bnd,
    extract_comparison is_iv_val is_bound cond = Some (cmp, iv_is_left, bnd) ->
    exists id,
      (exists x k,
         view_value cond = Res id (Intop_imm (Operation.Icomp cmp) k) [x]
         /\ is_iv_val x = true /\ iv_is_left = true /\ bnd = Const_bound k)
      \/ (exists x y,
         view_value cond = Res id (Intop (Operation.Icomp cmp)) [x; y]
         /\ is_iv_val x = true /\ is_bound y = true
         /\ iv_is_left = true /\ bnd = Value_bound y)
      \/ (exists x y,
         view_value cond = Res id (Intop (Operation.Icomp cmp)) [x; y]
         /\ is_iv_val y = true /\ is_bound x = true
         /\ iv_is_left = false /\ bnd = Value_bound x).
  Proof.
    intros is_iv_val is_bound cond cmp iv_is_left bnd H.
    unfold extract_comparison in H.
    destruct (view_value cond) as [id op args | bl i] eqn:Hv;
      [ | discriminate ].
    destruct op as [ | | | ? | ? | ? | ? | ? | ? | ? | ? | ? | ? | ? ? ? | iop
                   | ? | iop k | ? | ? ? | ? | ? | ? | ? | | | | ? | ? | | | |
                   | | ? ];
      try discriminate; destruct iop; try discriminate;
      destruct args as [ | x [ | y [ | ? ? ] ] ]; try discriminate.
    - (* Intop (Operation.Icomp cmp'), [x; y] *)
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
    - (* Intop_imm (Operation.Icomp cmp') k, [x] *)
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
      /\ ((sign = Add
           /\ view_value u = Res id (Intop_imm Operation.Iadd c) [x])
          \/ (sign = Sub
              /\ view_value u = Res id (Intop_imm Operation.Isub c) [x])).
  Proof.
    intros is_self c sign u H. unfold classify_update in H.
    destruct (view_value u) as [id op args | bl i] eqn:Hv; [ | discriminate ].
    destruct op as [ | | | ? | ? | ? | ? | ? | ? | ? | ? | ? | ? | ? ? ? | iop
                   | ? | iop c0 | ? | ? ? | ? | ? | ? | ? | | | | ? | ? | | | |
                   | | ? ];
      try discriminate; destruct iop; try discriminate;
      destruct args as [ | x [ | y [ | ? ? ] ] ]; try discriminate.
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
    pose proof (run.(run_machine).(iter_op) n u) as Hop.
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
    - destruct (run.(run_stays).(run_back_edge) n)
        as [s [args [Hs [Hpred [Hterm Hnext]]]]].
      pose proof Hspec as [_ [_ [_ [Hback _]]]].
      destruct (Hback s Hs Hpred) as [args' [u [Hargs' [Hu Hin]]]].
      apply goto_args_terminator in Hargs'. rewrite Hterm in Hargs'.
      injection Hargs' as <-.
      rewrite (Hnext _ _ (arg_value_nth _ _ _ Hu)). cbn [iv]. rewrite <- IH.
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
      split; [ apply run.(run_machine).(iter_bounded) | ].
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

  (* The branches [guards_at] takes facts from went the way it assumes
     ([guards_taken], AffineSsa.v): each is one whose edge
     [edge_dominates] accepts, which by [edge_dominates_sound] is on every
     path from the entry to the header, so [iter_branches] applies. *)
  Lemma guards_taken_of_run : guards_taken (iter 0%nat) l.(header).
  Proof.
    intros d _ index negate Hg. unfold guard_test in Hg.
    destruct (terminator d) as [ | index' targets | | ] eqn:Ht;
      try discriminate.
    destruct targets as [ | ifnot [ | ifso [ | ? ? ] ] ]; try discriminate.
    cbv iota beta in Hg.
    pose proof run.(run_entry).(run_dominance) as Hdom.
    destruct (edge_dominates d ifso l.(header)) eqn:Hso.
    - injection Hg as <- <-.
      apply (run.(run_entry).(iter_branches) d _ ifnot ifso _ Ht).
      intros p Hp.
      exact (edge_dominates_sound entry Hdom d ifso l.(header) Hso p Hp).
    - destruct (edge_dominates d ifnot l.(header)) eqn:Hnot;
        [ | discriminate ].
      injection Hg as <- <-.
      apply (run.(run_entry).(iter_branches) d _ ifnot ifso _ Ht).
      intros p Hp.
      exact (edge_dominates_sound entry Hdom d ifnot l.(header) Hnot p Hp).
  Qed.

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
    pose proof (run.(run_atoms_fit) v) as Hsmall.
    assert (Hgs : 0 <= guards_size l.(header)) by apply guards_sum_nonneg.
    pose proof (size_pos (tree_of_value v)) as Hsz.
    destruct (linearize_sound (iter 0) (run.(run_machine).(iter_bounded) 0)
                Heqb (tree_of_value v) new_ctx [] form side1 c1
                (run.(run_entry).(iter_trees) v) Hwf0 ltac:(lia) Hlin)
      as [Hwf1 [_ [Hn1 [Hwff [Hwfs1 Hrho1]]]]].
    destruct (guards_at_sound (iter 0) (run.(run_machine).(iter_bounded) 0)
                Heqb l.(header) c1 side1 guards side2 c2
                run.(run_entry).(iter_trees) Hwf1 ltac:(lia) Hg)
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
    - apply Hg2, guards_taken_of_run.
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

  (* --- The verdict against the run --- *)

  (* What [biv_implies_termination] accepting [b], a BIV of [l], says: the
     header has an exit branch [eb], [b] a literal step, the exit
     comparison the shape [extract_comparison] reads, and the verdict of
     LoopComparisons.v on them is [Terminates], or
     [Terminates_if_bound_in_range] with the bound checked in range. *)
  Lemma biv_implies_termination_spec : forall b,
    b.(loop) = l -> biv_implies_termination op_def b = true ->
    exists eb step cmp iv_is_left bnd,
      find_exit_branch l = Some eb
      /\ signed_step b = Some step
      /\ extract_comparison
           (fun v => is_param l.(header) b.(param_index) v
                     || existsb (value_eqb v) b.(update))
           (is_loop_invariant op_def l.(header)) eb.(condition)
         = Some (cmp, iv_is_left, bnd)
      /\ (continue_terminates step
            (oriented_continue_comparison iv_is_left eb.(continue_when_true)
               cmp)
          = LoopComparisons.Terminates
          \/ (continue_terminates step
                (oriented_continue_comparison iv_is_left
                   eb.(continue_when_true) cmp)
              = LoopComparisons.Terminates_if_bound_in_range
              /\ bound_in_range step l.(header) bnd = true)).
  Proof.
    intros b Hl Hb. unfold biv_implies_termination in Hb. rewrite Hl in Hb.
    destruct (find_exit_branch l) as [eb | ] eqn:Hexit; [ | discriminate ].
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

  (* At every visit the exit comparison tests the sequence [iv] of
     LoopComparisons.v (the induction variable's values, from its value or
     its updated value at the first visit) against a bound fixed at entry. *)
  Lemma exit_test_sequence : forall b step cond cmp iv_is_left bnd,
    biv_spec op_def l b -> signed_step b = Some step ->
    extract_comparison
      (fun v => is_param l.(header) b.(param_index) v
                || existsb (value_eqb v) b.(update))
      (is_loop_invariant op_def l.(header)) cond
    = Some (cmp, iv_is_left, bnd) ->
    exists v0, in_int64 v0
      /\ forall n, iter n cond
           = bool_to_Z
               (if iv_is_left
                then IntegerComparison.eval cmp (iv v0 (to_Z step) n)
                       (bound_value (iter 0) bnd)
                else IntegerComparison.eval cmp (bound_value (iter 0) bnd)
                       (iv v0 (to_Z step) n)).
  Proof.
    intros b step cond cmp iv_is_left bnd Hspec Hstep Hext.
    destruct (extract_comparison_spec _ _ _ _ _ _ Hext) as [id Hcases].
    destruct Hcases
      as [ [x [k [Hv [Hx [-> ->]]]]]
         | [ [x [y [Hv [Hx [Hy [-> ->]]]]]]
           | [x [y [Hv [Hy [Hx [-> ->]]]]]] ] ].
    - destruct (iv_val_sequence b step x Hspec Hstep Hx) as [v0 [Hv0 Hiter]].
      exists v0. split; [ exact Hv0 | ]. intros n.
      pose proof (run.(run_machine).(iter_op) n cond) as Hop.
      rewrite Hv in Hop. cbv iota in Hop.
      rewrite Hop, Hiter. reflexivity.
    - destruct (iv_val_sequence b step x Hspec Hstep Hx) as [v0 [Hv0 Hiter]].
      exists v0. split; [ exact Hv0 | ]. intros n.
      pose proof (run.(run_machine).(iter_op) n cond) as Hop.
      rewrite Hv in Hop. cbv iota in Hop.
      rewrite Hop, Hiter.
      rewrite (run.(run_entry).(iter_invariant) n y
                 (is_loop_invariant_spec _ _ _ Hy)).
      reflexivity.
    - destruct (iv_val_sequence b step y Hspec Hstep Hy) as [v0 [Hv0 Hiter]].
      exists v0. split; [ exact Hv0 | ]. intros n.
      pose proof (run.(run_machine).(iter_op) n cond) as Hop.
      rewrite Hv in Hop. cbv iota in Hop.
      rewrite Hop, Hiter.
      rewrite (run.(run_entry).(iter_invariant) n x
                 (is_loop_invariant_spec _ _ _ Hx)).
      reflexivity.
  Qed.

  (* At every visit of a run the exit test comes out the way that
     continues the loop: the header's [Switch] goes into the body, and of
     its two targets only one is in it. *)
  Lemma run_test_continues : forall eb n (test : bool),
    find_exit_branch l = Some eb ->
    iter n eb.(condition) = bool_to_Z test ->
    test = eb.(continue_when_true).
  Proof.
    intros eb n test Hexit Htest.
    destruct (find_exit_branch_spec l eb Hexit)
      as [ifnot [ifso [Ht [Hso Hnot]]]].
    destruct (run.(run_stays).(run_continues) n eb.(condition)
                [ifnot; ifso] Ht)
      as [target [Hnth Htarget]].
    rewrite Htest in Hnth.
    destruct test; cbn in Hnth; injection Hnth as <-.
    - rewrite Htarget in Hso. exact Hso.
    - rewrite Htarget in Hnot.
      destruct eb.(continue_when_true) eqn:Hcwt; [ | reflexivity ].
      try rewrite Hcwt in Hnot. discriminate.
  Qed.

(* ======================================================================== *)
(* Part 4: theorems                                                         *)
(* ======================================================================== *)

  (* No run of a loop the analysis says terminates goes on for ever: the
     hypotheses of this section, together with a [Terminates] verdict for
     the loop's basic induction variables, are contradictory. *)
  Theorem analyze_Terminates : forall bivs,
    bivs_of_loop op_def l bivs ->
    analyze op_def bivs = Terminates -> False.
  Proof.
    intros bivs Hbivs H. unfold analyze in H.
    destruct (existsb (biv_implies_termination op_def) bivs) eqn:He;
      [ | discriminate ].
    apply existsb_exists in He. destruct He as [b [Hin Hb]].
    pose proof (Hbivs b Hin) as Hspec. pose proof Hspec as [Hl _].
    destruct (biv_implies_termination_spec b Hl Hb)
      as [eb [step [cmp [iv_is_left [bnd [Hexit [Hstep [Hext Hverdict]]]]]]]].
    destruct (exit_test_sequence b step eb.(condition) cmp iv_is_left bnd
                Hspec Hstep Hext) as [v0 [Hv0 Hiter]].
    assert (Hbnd : in_int64 (bound_value (iter 0) bnd)).
    { destruct bnd as [v | k]; cbn [bound_value];
        [ apply run.(run_machine).(iter_bounded) | ].
      pose proof (int_bounds k). unfold in_int64, two62, two63 in *. lia. }
    (* LoopComparisons.v: a visit at which the test fails (the side
       condition on the bound lifted by [bound_in_range_sound]) ... *)
    destruct (loop_exits iv_is_left eb.(continue_when_true) cmp step v0
                (bound_value (iter 0) bnd) Hv0 Hbnd
                (match Hverdict with
                 | or_introl Ht => or_introl Ht
                 | or_intror (conj Ht Hr) =>
                   or_intror (conj Ht (bound_in_range_sound _ _ Hr))
                 end)) as [n Hn].
    (* ... at which the run says it came out the continuing way. *)
    pose proof (run_test_continues eb n _ Hexit (Hiter n)) as Hcont.
    unfold loop_continues in Hn. cbv zeta in Hn. rewrite Hcont in Hn.
    destruct eb.(continue_when_true) eqn:Hcwt; try rewrite Hcwt in Hn;
      discriminate.
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
