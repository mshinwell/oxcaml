(* Connecting the loop certificates to instruction-by-instruction SSA
   execution. Unlike [infinite_header_run], an [infinite_execution] here
   is made of actual [SsaSemantics.step] transitions.

   [execution_revisits] accounts for the finite instruction sequence in
   each block before applying the CFG acyclicity theorem. Graph observer
   contracts are [control_edges]: ordinary transfers appear among the
   successors, and successor/predecessor views agree. No arithmetic or
   loop invariant is assumed by that theorem. *)

From Stdlib Require Import ZArith Lia List.
From OxCamlStdlib Require Import OxCamlInt OxCamlList.
From OxCamlSsa Require Import SsaModel SsaGraph SsaDominance SsaSemantics
  SsaExecution.
From OxCamlLoop Require Import NaturalLoop InductionVar DeleteEmptyLoops.
Import ListNotations.
Local Open Scope nat_scope.

(* An infinite execution never gets stuck: every state has its actual
   next instruction or terminator step. No assertion is made that every
   arbitrary initial state admits such an execution. *)
Definition infinite_execution (trace : nat -> state) : Prop :=
  forall (time : nat), SsaSemantics.step (trace time) (trace (S time)).

Definition stays_in_region (region : blockset) (trace : nat -> state)
    : Prop :=
  forall (time : nat), set_mem (current_block (trace time)) region = true.

(* Every finite prefix of an infinite execution is a finite execution
   in the same operational semantics. *)
Lemma execution_prefix : forall (trace : nat -> state),
  infinite_execution trace -> forall (time : nat),
  steps (trace 0) (trace time).
Proof.
  intros trace Htrace time. induction time as [ | time IH].
  - constructor.
  - eapply steps_trans; [exact IH |].
    eapply Steps_cons; [apply Htrace | constructor].
Qed.

(* The values available anywhere on a reachable infinite execution obey
   their actual operations. Only structural SSA well-formedness is needed,
   not the machine-values field of the old abstract run record. *)
Theorem reachable_execution_values : control_edges ->
  forall (blocks : list block) (entry : block) (initial_regs : registers)
    (trace : nat -> state),
  well_formed_ssa blocks entry ->
  steps (enter entry initial_regs) (trace 0) -> infinite_execution trace ->
  forall (time : nat),
    coherent_at blocks entry (current_registers (trace time))
      (state_point (trace time)).
Proof.
  intros Hedges blocks entry initial_regs trace Hwf Hprefix Htrace time.
  eapply execution_values_coherent; [exact Hedges | exact Hwf |].
  eapply steps_trans; [exact Hprefix | apply execution_prefix; exact Htrace].
Qed.

(* The basic machine invariants hold at every point of an infinite
   execution when they hold initially. *)
Lemma infinite_execution_invariants : forall (trace : nat -> state),
  infinite_execution trace -> valid_position (trace 0) ->
  bounded_registers (current_registers (trace 0)) ->
  forall (time : nat), valid_position (trace time)
    /\ bounded_registers (current_registers (trace time)).
Proof.
  intros trace Htrace Hposition Hbounded time. induction time as [ | time IH].
  - auto.
  - destruct IH as [Hposition' Hbounded']. split.
    + eapply step_valid_position; [exact Hposition' | apply Htrace].
    + eapply step_bounded; [exact Hbounded' | apply Htrace].
Qed.

(* Registers defined outside the region are genuinely fixed throughout
   execution. This is a theorem about reads and writes, not an invariance
   axiom indexed by arbitrary syntactic expressions. *)
Theorem region_register_constant : parameter_layout ->
  forall (region : blockset) (trace : nat -> state) (reg : register),
  infinite_execution trace -> stays_in_region region trace ->
  valid_position (trace 0) -> ~ defined_in_region region reg ->
  forall (time : nat),
    current_registers (trace time) reg = current_registers (trace 0) reg.
Proof.
  intros Hlayout region trace reg Htrace Hregion Hposition Houtside.
  assert (Hpositions : forall (time : nat), valid_position (trace time)).
  { intros time. induction time as [ | time IH]; [exact Hposition |].
    eapply step_valid_position; [exact IH | apply Htrace]. }
  intros time. induction time as [ | time IH]; [reflexivity |].
  rewrite <- IH. eapply step_region_frame;
    try eassumption; [apply Hpositions | apply Hregion | apply Hregion |
      apply Htrace].
Qed.

(* A visit is sampled at the header terminator, after its instructions
   have executed. Visits occur arbitrarily late in instruction time. *)
Definition execution_visits (header : block) (trace : nat -> state) : Prop :=
  forall (start : nat), exists (visit : nat),
    start <= visit /\ current_block (trace visit) = header
    /\ remaining (trace visit) = [].

(* Moving past a block takes its remaining instructions plus one
   terminator step. This sampling function needs no choice axiom. *)
Fixpoint block_time (trace : nat -> state) (n : nat) : nat :=
  match n with
  | O => O
  | S n =>
    let t := block_time trace n in t + length (remaining (trace t)) + 1
  end.

(* An instruction step consumes one instruction without changing blocks. *)
Lemma instruction_step_position :
  forall (before after : state) (insn : instr) (rest : list instr),
  SsaSemantics.step before after -> remaining before = insn :: rest ->
  current_block after = current_block before /\ remaining after = rest.
Proof.
  intros s s' insn rest H Hremaining.
  destruct H; cbn in *; try discriminate. injection Hremaining as -> ->.
  auto.
Qed.

(* An infinite execution reaches the current block's terminator after
   exactly the number of instructions remaining in that block. *)
Lemma reaches_terminator : forall (trace : nat -> state),
  infinite_execution trace -> forall (start insns_left : nat),
  length (remaining (trace start)) = insns_left ->
  current_block (trace (start + insns_left)) = current_block (trace start)
  /\ remaining (trace (start + insns_left)) = [].
Proof.
  intros trace Htrace n k. generalize dependent n.
  induction k as [ | k IH ]; intros n Hlength.
  - rewrite Nat.add_0_r. split; [reflexivity |].
    apply length_zero_iff_nil. exact Hlength.
  - destruct (remaining (trace n)) as [ | insn rest] eqn:E;
      [discriminate |].
    injection Hlength as Hlength.
    destruct (instruction_step_position _ _ _ _ (Htrace n) E)
      as [Hblock Hrest].
    destruct (IH (S n) ltac:(rewrite Hrest; exact Hlength))
      as [Hblock' Hend].
    replace (n + S k) with (S n + k) by lia.
    rewrite Hblock', Hblock. auto.
Qed.

(* A terminator step follows a graph edge and starts the target's body. *)
Lemma terminator_step_edge : control_edges -> forall (before after : state),
  remaining before = [] -> SsaSemantics.step before after ->
  In (current_block after) (all_successors (current_block before))
  /\ remaining after = block_body (current_block after).
Proof.
  intros Hedges s s' Hremaining Hstep.
  destruct Hstep; cbn in *; try discriminate; split; try reflexivity.
  - eapply goto_successor; eassumption.
  - eapply switch_successor; [exact Hedges | eassumption |].
    eapply nth_error_In. eassumption.
Qed.

(* Successive block samples are adjacent in the CFG. *)
Lemma block_time_edge : control_edges -> forall (trace : nat -> state),
  infinite_execution trace -> forall (visit : nat),
  In (current_block (trace (block_time trace (S visit))))
    (all_successors (current_block (trace (block_time trace visit)))).
Proof.
  intros Hedges trace Htrace n. cbn [block_time].
  set (t := block_time trace n).
  destruct (reaches_terminator trace Htrace t
    (length (remaining (trace t))) eq_refl) as [Hblock Hend].
  pose proof (terminator_step_edge Hedges _ _ Hend
    (Htrace (t + length (remaining (trace t))))) as [Hedge _].
  replace (t + length (remaining (trace t)) + 1)
    with (S (t + length (remaining (trace t)))) by lia.
  rewrite Hblock in Hedge. exact Hedge.
Qed.

(* Block samples cannot accumulate in a finite prefix of instruction time. *)
Lemma block_time_ge : forall (trace : nat -> state) (visit : nat),
  visit <= block_time trace visit.
Proof.
  intros trace n. induction n; cbn [block_time]; lia.
Qed.

(* The existing CFG revisit certificate now applies to actual small-step
   executions, not just an assumed sequence of adjacent blocks. *)
Theorem execution_revisits : control_edges ->
  forall (region : blockset) (header : block) (trace : nat -> state),
  revisits region header -> infinite_execution trace ->
  stays_in_region region trace -> execution_visits header trace.
Proof.
  intros Hedges region header trace Hrevisits Htrace Hregion n.
  assert (Hblocks : forall k,
    set_mem (current_block (trace (block_time trace k))) region = true
    /\ In (current_block (trace (block_time trace (S k))))
         (all_successors (current_block (trace (block_time trace k))))).
  { intros k. split; [apply Hregion | apply block_time_edge; assumption]. }
  destruct (Hrevisits (fun k => current_block (trace (block_time trace k)))
    Hblocks n) as [m [Hnm Hheader]].
  pose proof (block_time_ge trace m) as Htime.
  destruct (reaches_terminator trace Htrace (block_time trace m)
    (length (remaining (trace (block_time trace m)))) eq_refl)
    as [Hblock Hend].
  exists (block_time trace m
    + length (remaining (trace (block_time trace m)))).
  split; [lia |]. rewrite Hblock, Hheader. auto.
Qed.

(* Every selected loop has the operational revisit property. The graph
   observation contract is the only premise beyond membership in the
   extracted analysis's result. *)
Theorem find_deletions_execution_visits : control_edges ->
  forall (defs : op_def) (blocks : list block) (loop_header exit : block),
  In (loop_header, exit) (find_deletions defs blocks) ->
  exists (loop : natural_loop) (bivs : list biv),
    In (loop, bivs) (InductionVar.analyze defs blocks)
    /\ loop_header = loop.(header)
    /\ forall (trace : nat -> state),
         infinite_execution trace -> stays_in_region loop.(body) trace ->
         execution_visits loop_header trace.
Proof.
  intros Hedges defs blocks h exit Hin.
  destruct (find_deletions_spec _ _ _ _ Hin) as [l [bivs [Hl [Hh Hcert]]]].
  exists l, bivs. split; [exact Hl |]. split; [exact Hh |].
  intros trace Htrace Hregion. subst h.
  destruct Hcert as [_ [_ [Hrevisits _]]].
  eapply execution_revisits; eassumption.
Qed.

(* Structural facts of the particular loop record returned by discovery.
   In particular, completeness refers to this record, not to an unknown
   second loop with the same header. *)
Record loop_graph_properties (blocks : list block) (entry : block)
    (loop : natural_loop) : Prop :=
  { loop_header_in_body : set_mem loop.(header) loop.(body) = true;
    loop_header_in_graph : In loop.(header) blocks;
    loop_body_in_graph : forall (b : block),
      set_mem b loop.(body) = true -> In b blocks;
    loop_header_dominates_body : forall (b : block),
      set_mem b loop.(body) = true ->
      forall (p : list block), path entry p b -> In loop.(header) p;
    loop_back_edges_complete : forall (source : block),
      set_mem source loop.(body) = true ->
      In loop.(header) (all_successors source) ->
      In source loop.(back_edge_sources) }.

Section Graph.
  Variable blocks : list block.
  Variable entry : block.
  Hypothesis predecessors_closed : forall (b pred : block),
    In b blocks -> In pred (predecessors b) -> In pred blocks.
  Hypothesis successors_closed : forall (b succ : block),
    In b blocks -> In succ (all_successors b) -> In succ blocks.
  Hypothesis dominance : dominance_semantics entry.
  Hypothesis dominance_complete : forall (dominator target : block),
    In dominator blocks -> In target blocks ->
    (forall (p : list block), path entry p target -> In dominator p) ->
    dominator --dom--> target.

  (* Graph closure and correct dominance observations suffice to prove
     the natural-loop structural properties used by execution proofs. *)
  Theorem found_loop_graph_properties : forall (loop : natural_loop),
    In loop (find_loops blocks) -> loop_graph_properties blocks entry loop.
  Proof.
    intros l Hl.
    destruct (find_loops_blocks blocks predecessors_closed successors_closed
      l Hl) as [Hheader Hbody].
    pose proof (find_loops_body_dominated blocks entry l dominance Hl)
      as Hdom.
    constructor; try assumption.
    - pose proof Hl as Hrecord. apply find_loops_In in Hrecord.
      destruct Hrecord as [h [sources [Hin ->]]].
      apply natural_loop_body_header.
    - intros source Hsource Hedge.
      eapply find_loops_back_edges_complete;
        [exact Hl | apply Hbody; exact Hsource | exact Hedge |].
      apply dominance_complete; [exact Hheader | apply Hbody; exact Hsource |].
      apply Hdom. exact Hsource.
  Qed.

  (* Compose graph discovery with the actual deletion decision. These
     properties no longer need to be assembled manually by a reviewer. *)
  Theorem find_deletions_graph_properties :
    forall (defs : op_def) (loop_header exit : block),
    In (loop_header, exit) (find_deletions defs blocks) ->
    exists (loop : natural_loop) (bivs : list biv),
      loop_header = loop.(header) /\ deletable defs blocks loop bivs exit
      /\ loop_graph_properties blocks entry loop.
  Proof.
    intros defs h exit Hin.
    destruct (find_deletions_spec _ _ _ _ Hin)
      as [l [bivs [Hl [Hheader Hcert]]]].
    exists l, bivs. split; [exact Hheader |]. split; [exact Hcert |].
    apply found_loop_graph_properties.
    exact (proj1 (InductionVar.analyze_spec _ _ _ _ Hl)).
  Qed.
End Graph.

(* A return to the header from the loop body is one of the analyzed
   back-edge Gotos, and it passes the actual argument-register values to
   the header's parameters. This derives the control-flow and binding
   content of [run_back_edge] from a single operational transition. *)
Theorem loop_back_edge_step : forall (blocks : list block) (entry : block)
    (defs : op_def) (loop : natural_loop) (bivs : list biv) (exit : block),
  control_edges -> parameter_layout ->
  loop_graph_properties blocks entry loop ->
  deletable defs blocks loop bivs exit ->
  forall (before after : state),
    remaining before = [] ->
    set_mem (current_block before) loop.(body) = true ->
    SsaSemantics.step before after -> current_block after = loop.(header) ->
    exists (args : list Terminator.arg),
      In (current_block before) loop.(back_edge_sources)
      /\ In (current_block before) (predecessors loop.(header))
      /\ terminator (current_block before)
           = Terminator.Continue (Goto loop.(header)) args
      /\ forall (index : int) (arg : value),
           nth_int args index = Some (Terminator.Arg arg) ->
           current_registers after
             (register_of_value (param loop.(header) index))
           = current_registers before (register_of_value arg).
Proof.
  intros blocks entry defs l bivs exit Hedges Hparams Hgraph Hcert
    s s' Hremaining Hin Hstep Hheader.
  destruct (terminator_step_edge Hedges _ _ Hremaining Hstep)
    as [Hedge _]. rewrite Hheader in Hedge.
  assert (Hback : In (current_block s) l.(back_edge_sources)).
  { eapply loop_back_edges_complete; eassumption. }
  assert (Hpred : In (current_block s) (predecessors l.(header))).
  { apply (proj2 (predecessor_successor Hedges _ _)). exact Hedge. }
  destruct Hcert as [_ [_ [_ [[_ Hspecs] [_ [_ Hnonempty]]]]]].
  destruct bivs as [ | biv bivs]; [contradiction |].
  destruct (Hspecs biv (or_introl eq_refl)) as [Hspec _].
  destruct Hspec as [_ [_ [_ [Hargs _]]]].
  destruct (Hargs _ Hback Hpred) as [args [v [Hgoto _]]].
  apply goto_args_terminator in Hgoto.
  exists args. repeat split; try assumption.
  exact (proj2 (proj2
    (goto_step_parameter Hparams _ _ _ _ Hremaining Hgoto Hstep))).
Qed.
