(* Connecting the loop certificates to instruction-by-instruction SSA
   execution. Unlike [infinite_header_run], an [infinite_execution] here
   is made of actual [SsaSemantics.step] transitions.

   [execution_revisits] accounts for the finite instruction sequence in
   each block before applying the CFG acyclicity theorem. Graph observer
   contracts are [control_edges]: ordinary transfers appear among the
   successors, and successor/predecessor views agree. No arithmetic or
   loop invariant is assumed by that theorem. *)

From Stdlib Require Import ZArith Lia List Classical_Prop.
From OxCamlStdlib Require Import OxCamlInt OxCamlList.
From OxCamlSsa Require Import SsaModel SsaGraph SsaDominance SsaSemantics
  SsaExecution SsaProgress SsaContext.
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

(* This excludes infinite execution confined to the region. It does not
   identify stuck states with successful exits or claim progress for
   arbitrary initial register environments. *)
Definition no_infinite_execution_in (region : blockset) (start : state)
    : Prop :=
  forall (trace : nat -> state), trace 0 = start ->
    infinite_execution trace -> stays_in_region region trace -> False.

(* A finite region segment may leave the region only on its final step.
   Requiring only its source states to be inside includes the exiting edge. *)
Inductive region_steps (region : blockset) : state -> state -> Prop :=
  | Region_refl : forall (s : state), region_steps region s s
  | Region_cons : forall (before middle after : state),
      set_mem (current_block before) region = true ->
      SsaSemantics.step before middle -> region_steps region middle after ->
      region_steps region before after.

(* Region segments are executions in the same original graph. *)
Lemma region_steps_execution : forall (region : blockset)
    (before after : state),
  region_steps region before after -> steps before after.
Proof.
  intros region before after Hregion. induction Hregion.
  - constructor.
  - eapply Steps_cons; eassumption.
Qed.

(* Region segments compose when the second segment can start: its own
   source-state conditions prevent continuing after an earlier exit. *)
Lemma region_steps_trans : forall (region : blockset)
    (before middle after : state),
  region_steps region before middle -> region_steps region middle after ->
  region_steps region before after.
Proof.
  intros region before middle after Hprefix.
  induction Hprefix as [s | before middle last Hinside Hstep Hrest IH];
    intros Hsuffix; [exact Hsuffix |].
  eapply Region_cons; [exact Hinside | exact Hstep | apply IH; exact Hsuffix].
Qed.

(* Executing a block body inside the region remains in that region and
   ends before taking its terminator. *)
Lemma executes_insns_region : forall (region : blockset) (b : block)
    (insns : list instr) (before after : registers),
  set_mem b region = true -> executes_insns before insns after ->
  region_steps region
    {| current_block := b; remaining := insns; current_registers := before |}
    {| current_block := b; remaining := []; current_registers := after |}.
Proof.
  intros region b insns before after Hinside Hbody. induction Hbody.
  - constructor.
  - eapply Region_cons; [exact Hinside | constructor; exact H | exact IHHbody].
Qed.

(* A finite exit must first execute the current block's remaining body.
   Extracting this prefix needs no separate progress assumption. *)
Lemma region_exit_body_prefix : forall (region : blockset) (b : block)
    (insns : list instr) (before : registers) (after : state),
  set_mem b region = true -> set_mem (current_block after) region = false ->
  region_steps region
    {| current_block := b; remaining := insns; current_registers := before |}
    after ->
  exists (body_regs : registers), executes_insns before insns body_regs /\
    region_steps region
      {| current_block := b; remaining := []; current_registers := body_regs |}
      after.
Proof.
  intros region b insns. induction insns as [ | insn rest IH];
    intros before after Hinside Houtside Hsegment.
  - exists before. split; [constructor | exact Hsegment].
  - inversion Hsegment as [s | s middle last Hsource Hstep Hrest]; subst.
    + cbn in Houtside. congruence.
    + inversion Hstep as [source current suffix regs regs' Hexec |
        source target args regs values regs' Hterm Hread Hbind |
        source index targets regs word target Hterm Hread Hnonneg Hnth
          Hparams];
        subst.
      destruct (IH regs' after Hinside Houtside Hrest)
        as [body_regs [Hbody Hsuffix]].
      exists body_regs. split; [econstructor; eassumption | exact Hsuffix].
Qed.

(* Outside registers remain unchanged through the exiting edge as well:
   the final block has no parameters, so entering it writes no register. *)
Theorem region_steps_frame : parameter_layout -> forall (region : blockset)
    (before after : state) (reg : register),
  region_steps region before after -> valid_position before ->
  params (current_block after) = [] -> ~ defined_in_region region reg ->
  current_registers after reg = current_registers before reg.
Proof.
  intros Hlayout region before after reg Hsegment.
  induction Hsegment as [s | before middle after Hinside Hstep Hrest IH];
    intros Hposition Hparams Houtside; [reflexivity |].
  destruct (set_mem (current_block middle) region) eqn:Hmiddle.
  - rewrite (IH ltac:(eapply step_valid_position; eassumption)
      Hparams Houtside).
    eapply step_region_frame; eassumption.
  - inversion Hrest; subst; [ | congruence].
    assert (Hfinished : remaining before = []).
    { destruct Hstep; cbn in *; try reflexivity. congruence. }
    rewrite (step_to_parameterless_frame _ _ Hfinished Hparams Hstep).
    reflexivity.
Qed.

(* A finite segment reaching outside the region rules out an infinite
   confined execution from the same state, using step determinism. *)
Theorem region_exit_not_infinite : forall (region : blockset)
    (before after : state),
  region_steps region before after ->
  set_mem (current_block after) region = false ->
  no_infinite_execution_in region before.
Proof.
  intros region before after Hsegment Houtside.
  induction Hsegment as [s | before middle after Hinside Hstep Hrest IH];
    intros trace Hstart Htrace Hregion.
  - specialize (Hregion 0). rewrite Hstart, Houtside in Hregion. discriminate.
  - apply (IH Houtside (fun time => trace (S time))).
    + symmetry. eapply step_deterministic; [exact Hstep |].
      rewrite <- Hstart. apply Htrace.
    + intros time. apply Htrace.
    + intros time. apply Hregion.
Qed.

(* A finite exit witness also rules out getting stuck earlier. Every
   other finite confined prefix follows the same deterministic steps. *)
Theorem region_exit_progress : forall (region : blockset)
    (before after : state),
  region_steps region before after ->
  set_mem (current_block after) region = false ->
  forall (reached : state), region_steps region before reached ->
  set_mem (current_block reached) region = true ->
  exists (next : state), SsaSemantics.step reached next.
Proof.
  intros region before after Hexit.
  induction Hexit as [s | before middle after Hinside Hstep Hrest IH];
    intros Houtside reached Hprefix Hreached.
  - inversion Hprefix; subst; cbn in *; congruence.
  - inversion Hprefix as [s | s middle' last Hsource Hnext Hsuffix]; subst.
    + exists middle. exact Hstep.
    + assert (middle = middle') by (eapply step_deterministic; eassumption).
      subst middle'. eapply IH; eassumption.
Qed.

(* Iterate the proof-only successor function. A stuck state repeats; the
   progress argument below proves that repetition is never used inside
   the region. This is not a modified machine semantics. *)
Fixpoint successor_trace (start : state) (time : nat) : state :=
  match time with
  | O => start
  | S previous =>
    let current := successor_trace start previous in
    match next_state current with Some next => next | None => current end
  end.

(* Nondivergence plus separately proved progress gives a finite first
   exit. Classical reasoning is used only to obtain a finite witness;
   the infinite trace in the contradiction is explicitly constructed. *)
Theorem region_finite_exit : forall (region : blockset) (start : state),
  no_infinite_execution_in region start ->
  (forall (reached : state), region_steps region start reached ->
    set_mem (current_block reached) region = true ->
    exists (next : state), SsaSemantics.step reached next) ->
  exists (reached : state), region_steps region start reached
    /\ set_mem (current_block reached) region = false.
Proof.
  intros region start Hfinite Hprogress. apply NNPP. intros Hnoexit.
  assert (Hinside : forall (reached : state),
    region_steps region start reached ->
    set_mem (current_block reached) region = true).
  { intros reached Hprefix.
    destruct (set_mem (current_block reached) region) eqn:Hmem;
      [reflexivity |]. exfalso. apply Hnoexit. exists reached. auto. }
  assert (Hprefix : forall (time : nat),
    region_steps region start (successor_trace start time)).
  { intros time. induction time as [ | time IH]; [constructor |].
    destruct (Hprogress _ IH (Hinside _ IH)) as [next Hstep].
    cbn [successor_trace]. rewrite (next_state_complete _ _ Hstep).
    eapply region_steps_trans; [exact IH |].
    eapply Region_cons; [apply Hinside; exact IH | exact Hstep | constructor]. }
  apply (Hfinite (successor_trace start) eq_refl).
  - intros time.
    destruct (Hprogress _ (Hprefix time) (Hinside _ (Hprefix time)))
      as [next Hstep].
    cbn [successor_trace]. rewrite (next_state_complete _ _ Hstep). exact Hstep.
  - intros time. apply Hinside, Hprefix.
Qed.

(* Leaving a region is a block transfer, not an instruction. The new
   state is exactly the target's entry, before any exit instruction runs. *)
Lemma step_exits_region : control_edges -> forall (region : blockset)
    (before after : state),
  set_mem (current_block before) region = true ->
  set_mem (current_block after) region = false ->
  SsaSemantics.step before after ->
  In (current_block after) (all_successors (current_block before))
    /\ after = enter (current_block after) (current_registers after).
Proof.
  intros Hedges region before after Hinside Houtside Hstep.
  destruct Hstep; cbn in *; [congruence | |]; split; try reflexivity.
  - eapply goto_successor; eassumption.
  - eapply switch_successor;
      [exact Hedges | eassumption | eapply nth_error_In; eassumption].
Qed.

(* When a region has one designated exit, its finite first exit reaches
   that block's entry. No instructions in the exit block are included. *)
Theorem region_exit_target : control_edges -> forall (loop : natural_loop)
    (exit : block) (before after : state),
  exits_only_to loop exit ->
  set_mem (current_block before) loop.(body) = true ->
  region_steps loop.(body) before after ->
  set_mem (current_block after) loop.(body) = false ->
  exists (regs : registers), after = enter exit regs.
Proof.
  intros Hedges loop exit before after Honly Hinside Hrun.
  revert Hinside.
  induction Hrun as [s | before middle after Hsource Hstep Hrest IH];
    intros Hinside Houtside; [congruence |].
  destruct (set_mem (current_block middle) loop.(body)) eqn:Hmiddle.
  - apply IH; [reflexivity | exact Houtside].
  - assert (Hsame : middle = after).
    { inversion Hrest; subst; [reflexivity | congruence]. }
    subst after.
    destruct (step_exits_region Hedges _ _ _ Hsource Hmiddle Hstep)
      as [Hsucc Hentry].
    destruct (Honly _ Hsource _ Hsucc) as [Hin | Hexit]; [congruence |].
    exists (current_registers middle). rewrite <- Hexit. exact Hentry.
Qed.

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
  context_steps (enter entry initial_regs) (trace 0) ->
  infinite_execution trace ->
  forall (time : nat),
    coherent_at blocks entry (current_registers (trace time))
      (state_point (trace time)).
Proof.
  intros Hedges blocks entry initial_regs trace Hwf Hprefix Htrace time.
  eapply context_execution_values_coherent; [exact Hedges | exact Hwf |].
  eapply context_steps_trans; [exact Hprefix |].
  apply context_of_steps, execution_prefix. exact Htrace.
Qed.

(* Instruction-position validity propagates along an execution. *)
Lemma execution_positions : forall (trace : nat -> state),
  infinite_execution trace -> valid_position (trace 0) ->
  forall (time : nat), valid_position (trace time).
Proof.
  intros trace Htrace Hposition time. induction time as [ | time IH].
  - exact Hposition.
  - eapply step_valid_position; [exact IH | apply Htrace].
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

(* The instruction sequence leading to a block's terminator preserves
   every block parameter, even when executing inside that same block. *)
Lemma parameters_through_body : forall (trace : nat -> state),
  infinite_execution trace -> forall (b : block) (index : int)
    (start insns_left : nat),
  length (remaining (trace start)) = insns_left ->
  current_registers (trace (start + insns_left)) (Param b index)
    = current_registers (trace start) (Param b index).
Proof.
  intros trace Htrace b index start insns_left. generalize dependent start.
  induction insns_left as [ | insns_left IH]; intros start Hlength.
  - rewrite Nat.add_0_r. reflexivity.
  - destruct (remaining (trace start)) as [ | insn rest] eqn:E;
      [discriminate |].
    injection Hlength as Hlength.
    destruct (instruction_step_position _ _ _ _ (Htrace start) E)
      as [_ Hrest].
    replace (start + S insns_left) with (S start + insns_left) by lia.
    rewrite (IH (S start) ltac:(rewrite Hrest; exact Hlength)).
    eapply instruction_parameter_frame;
      [apply Htrace | rewrite E; discriminate].
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

(* Every block sample after the first is an actual block-entry state. *)
Lemma block_time_entry : control_edges -> forall (trace : nat -> state),
  infinite_execution trace -> forall (visit : nat),
  at_entry (current_block (trace (block_time trace (S visit))))
    (trace (block_time trace (S visit))).
Proof.
  intros Hedges trace Htrace visit. split; [reflexivity |].
  cbn [block_time]. set (start := block_time trace visit).
  destruct (reaches_terminator trace Htrace start
    (length (remaining (trace start))) eq_refl) as [_ Hfinished].
  pose proof (terminator_step_edge Hedges _ _ Hfinished
    (Htrace (start + length (remaining (trace start))))) as [_ Hentry].
  replace (start + length (remaining (trace start)) + 1)
    with (S (start + length (remaining (trace start)))) by lia.
  exact Hentry.
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

(* An infinite confined execution has a later entry to the header, not
   merely a later instruction in the same visit. *)
Lemma later_header_entry : control_edges ->
  forall (region : blockset) (header : block) (trace : nat -> state),
  revisits region header -> infinite_execution trace ->
  stays_in_region region trace -> forall (start : nat),
  exists (visit : nat), start < visit /\ at_entry header (trace visit).
Proof.
  intros Hedges region header trace Hrevisits Htrace Hregion start.
  assert (Hblocks : forall (visit : nat),
    set_mem (current_block (trace (block_time trace visit))) region = true
    /\ In (current_block (trace (block_time trace (S visit))))
         (all_successors (current_block (trace (block_time trace visit))))).
  { intros visit. split; [apply Hregion | apply block_time_edge; assumption]. }
  destruct (Hrevisits (fun visit =>
    current_block (trace (block_time trace visit))) Hblocks (S start))
    as [visit [Hlater Hheader]].
  pose proof (block_time_ge trace visit) as Htime.
  exists (block_time trace visit). split; [lia |].
  destruct visit as [ | visit]; [lia |].
  rewrite <- Hheader. apply block_time_entry; assumption.
Qed.

(* A decidable event occurring at a known finite time has a first
   occurrence. This avoids any choice axiom when selecting header visits. *)
Lemma first_event : forall (test : nat -> bool) (limit : nat),
  test limit = true ->
  exists (first : nat), first <= limit /\ test first = true
    /\ forall (earlier : nat), earlier < first -> test earlier = false.
Proof.
  intros test limit. generalize dependent test.
  induction limit as [ | limit IH]; intros test Hlimit;
    destruct (test 0) eqn:Hfirst.
  - exists 0. repeat split; try assumption; lia.
  - discriminate.
  - exists 0. repeat split; try assumption; lia.
  - destruct (IH (fun time => test (S time)) Hlimit)
      as [first [Hbound [Htest Hminimal]]].
    exists (S first). split; [lia |]. split; [exact Htest |].
    intros [ | earlier] Hearlier; [exact Hfirst |].
    apply Hminimal. lia.
Qed.

(* Select consecutive header entries. The earlier time returned is the
   terminator immediately before the next entry, so the recurrence can
   use the actual back-edge transition. *)
Theorem next_header_entry : control_edges ->
  forall (region : blockset) (header : block) (trace : nat -> state),
  revisits region header -> infinite_execution trace ->
  stays_in_region region trace -> valid_position (trace 0) ->
  forall (start : nat), exists (back_time : nat),
    start <= back_time /\ at_entry header (trace (S back_time))
    /\ forall (between : nat), start < between <= back_time ->
         ~ at_entry header (trace between).
Proof.
  intros Hedges region header trace Hrevisits Htrace Hregion Hposition start.
  pose proof (execution_positions trace Htrace Hposition) as Hpositions.
  destruct (later_header_entry Hedges region header trace
    Hrevisits Htrace Hregion start) as [later [Hlater Hentry]].
  set (test := fun offset => entry_test header (trace (start + S offset))).
  assert (Htest : test (later - start - 1) = true).
  { unfold test. replace (start + S (later - start - 1)) with later by lia.
    apply (entry_test_spec _ _ (Hpositions later)). exact Hentry. }
  destruct (first_event test _ Htest)
    as [offset [Hbound [Hfirst Hminimal]]].
  exists (start + offset). split; [lia |]. split.
  - apply (entry_test_spec _ _ (Hpositions (S (start + offset)))).
    unfold test in Hfirst. replace (start + S offset) with (S (start + offset))
      in Hfirst by lia. exact Hfirst.
  - intros between Hbetween Hentry_between.
    pose proof (Hminimal (between - start - 1) ltac:(lia)) as Hfalse.
    unfold test in Hfalse.
    replace (start + S (between - start - 1)) with between in Hfalse by lia.
    apply (entry_test_spec _ _ (Hpositions between)) in Hentry_between.
    congruence.
Qed.

(* Header parameters stay fixed until the next entry, including during
   the header's own instruction sequence. *)
Lemma parameter_between_entries : parameter_layout ->
  forall (trace : nat -> state) (header : block) (index : int)
    (start distance : nat),
  infinite_execution trace ->
  (forall (offset : nat), 0 < offset <= distance ->
     ~ at_entry header (trace (start + offset))) ->
  current_registers (trace (start + distance)) (Param header index)
    = current_registers (trace start) (Param header index).
Proof.
  intros Hlayout trace header index start distance Htrace.
  induction distance as [ | distance IH]; intros Hno_entry.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite <- (IH ltac:(intros offset Hoffset; apply Hno_entry; lia)).
    replace (start + S distance) with (S (start + distance)) by lia.
    eapply step_parameter_frame_unless_entry; [exact Hlayout | apply Htrace |].
    replace (S (start + distance)) with (start + S distance) by lia.
    apply Hno_entry. lia.
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
    loop_body_predecessors : forall (source target : block),
      set_mem target loop.(body) = true -> target <> loop.(header) ->
      In source (predecessors target) -> set_mem source loop.(body) = true;
    loop_back_edge_in_body : forall (source : block),
      In source loop.(back_edge_sources) -> set_mem source loop.(body) = true;
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
    - intros source target Htarget Hnot_header Hedge.
      apply (proj2 (find_loops_body blocks predecessors_closed
        successors_closed
        l source Hl)).
      destruct (block_eqb source l.(header)) eqn:E.
      + left. apply block_eqb_spec. exact E.
      + right. eapply reaches_pred; [ | exact Hedge |].
        * apply (proj1 (find_loops_body blocks predecessors_closed
            successors_closed l target Hl)) in Htarget.
          destruct Htarget as [Heq | Hreaches];
            [contradiction | exact Hreaches].
        * intros Heq. subst source. rewrite block_eqb_refl in E. discriminate.
    - intros source Hsource.
      apply (proj2 (find_loops_body blocks predecessors_closed
        successors_closed
        l source Hl)).
      destruct (block_eqb source l.(header)) eqn:E.
      + left. apply block_eqb_spec. exact E.
      + right. constructor; [exact Hsource |].
        intros Heq. subst source. rewrite block_eqb_refl in E. discriminate.
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
      In (loop, bivs) (InductionVar.analyze defs blocks)
      /\ loop_header = loop.(header)
      /\ deletion_certificate defs blocks loop bivs exit
      /\ loop_graph_properties blocks entry loop.
  Proof.
    intros defs h exit Hin.
    destruct (find_deletions_spec _ _ _ _ Hin)
      as [l [bivs [Hl [Hheader Hcert]]]].
    exists l, bivs. split; [exact Hl |].
    split; [exact Hheader |]. split; [exact Hcert |].
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
  deletion_certificate defs blocks loop bivs exit ->
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
  destruct (certificate_counter _ _ _ _ _ Hcert)
    as [biv [Hcounter_in [Hspec _]]].
  destruct Hspec as [_ [_ [_ [Hargs _]]]].
  destruct (Hargs _ Hback Hpred) as [args [v [Hgoto _]]].
  apply goto_args_terminator in Hgoto.
  exists args. repeat split; try assumption.
  exact (proj2 (proj2
    (goto_step_parameter Hparams _ _ _ _ Hremaining Hgoto Hstep))).
Qed.
