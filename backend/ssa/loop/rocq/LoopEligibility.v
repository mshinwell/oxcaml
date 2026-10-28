(* Semantic eligibility for bypassing a loop, stated on the original graph.

   [eligible_entry] is the target property, not a record of analysis
   answers. It requires a finite normal exit, and equality with the first
   header execution on every register read before its next definition.
   The retained header is executed, not skipped. Determinism makes the
   finite execution witness exclude a different divergent execution.

   This is still the integer/control-flow semantics of SsaSemantics.v.
   [find_deletions_finite_exit_eligible] discharges live-out agreement for
   every accepted loop that has a finite exit. Establishing that exit for
   every valid reachable entry remains unfinished. No post-deletion graph,
   renaming or pruning is modelled here, and eligibility is not assumed
   as a compiler or builder contract. Nothing in this file is extracted. *)

From Stdlib Require Import List.
From OxCamlSsa Require Import SsaModel SsaGraph SsaDominance SsaSemantics
  SsaExecution SsaLiveness.
From OxCamlLoop Require Import NaturalLoop InductionVar DeleteEmptyLoops
  LoopExecution LoopLiveOut.
Import ListNotations.

(* A valid bypass retains the first header body, then replaces only its
   terminator by a jump to the parameterless exit. All execution relations
   here refer to the unchanged original graph. The region segment contains
   its first exiting edge and cannot execute any instruction after it. *)
Definition eligible_entry (loop : natural_loop) (exit : block)
    (header_regs : registers) : Prop :=
  set_mem loop.(header) loop.(body) = true
  /\ set_mem exit loop.(body) = false
  /\ params exit = []
  /\ exists (first_header_regs exit_regs : registers),
       executes_insns header_regs (block_body loop.(header)) first_header_regs
       /\ region_steps loop.(body)
            {| current_block := loop.(header); remaining := [];
               current_registers := first_header_regs |}
            (enter exit exit_regs)
       /\ agree_on_live (entry_point exit) first_header_regs exit_regs.

(* Eligibility entails an actual finite execution reaching the exit, and
   rules out an infinite execution confined to the loop. Thus its finite
   witness is not merely one good path among bad nondeterministic paths. *)
Theorem eligible_entry_execution : forall (loop : natural_loop) (exit : block)
    (header_regs : registers),
  eligible_entry loop exit header_regs ->
  (exists (exit_regs : registers),
     region_steps loop.(body) (enter loop.(header) header_regs)
       (enter exit exit_regs))
  /\ no_infinite_execution_in loop.(body) (enter loop.(header) header_regs).
Proof.
  intros loop exit header_regs
    [Hinside [Houtside [Hparams [first [last [Hbody [Hrest Hagree]]]]]]].
  assert (Hrun : region_steps loop.(body) (enter loop.(header) header_regs)
    (enter exit last)).
  { eapply region_steps_trans; [ | exact Hrest].
    eapply executes_insns_region; eassumption. }
  split; [exists last; exact Hrun |].
  eapply region_exit_not_infinite; [exact Hrun | exact Houtside].
Qed.

(* Eligibility cannot hide a finite stuck execution before the exit.
   This follows from the finite witness and determinism, not a separate
   assumption that instructions or branches always make progress. *)
Theorem eligible_entry_progress : forall (loop : natural_loop) (exit : block)
    (header_regs : registers),
  eligible_entry loop exit header_regs -> forall (reached : state),
  region_steps loop.(body) (enter loop.(header) header_regs) reached ->
  set_mem (current_block reached) loop.(body) = true ->
  exists (next : state), SsaSemantics.step reached next.
Proof.
  intros loop exit header_regs Heligible reached Hprefix Hinside.
  destruct (proj1 (eligible_entry_execution _ _ _ Heligible))
    as [exit_regs Hrun].
  pose proof Heligible as [_ [Houtside Hrest]].
  eapply region_exit_progress; eassumption.
Qed.

(* A loop that exits on this first header visit already has the required
   value agreement: the parameterless transfer modifies no register.
   The theorem includes the header's actual computations and their values. *)
Theorem first_visit_exit_eligible : forall (loop : natural_loop) (exit : block)
    (header_regs first_header_regs exit_regs : registers),
  set_mem loop.(header) loop.(body) = true ->
  set_mem exit loop.(body) = false -> params exit = [] ->
  executes_insns header_regs (block_body loop.(header)) first_header_regs ->
  SsaSemantics.step
    {| current_block := loop.(header); remaining := [];
       current_registers := first_header_regs |}
    (enter exit exit_regs) ->
  eligible_entry loop exit header_regs.
Proof.
  intros loop exit header_regs first exit_regs Hinside Houtside Hparams
    Hbody Hstep.
  split; [exact Hinside |]. split; [exact Houtside |].
  split; [exact Hparams |]. exists first, exit_regs.
  split; [exact Hbody |]. split.
  - eapply Region_cons; [exact Hinside | exact Hstep | constructor].
  - pose proof (step_to_parameterless_frame
      {| current_block := loop.(header); remaining := [];
         current_registers := first |} (enter exit exit_regs)
      eq_refl Hparams Hstep) as Heq.
    cbn in Heq. subst exit_regs. intros reg Hlive. reflexivity.
Qed.

(* For an accepted loop, a finite original execution to its exit suffices:
   the first header computation and live-out agreement are both derived.
   No equality of dead counter values is required. *)
Theorem certificate_finite_exit_eligible : control_edges ->
  forall (blocks : list block) (entry : block) (defs : op_def)
    (loop : natural_loop) (bivs : list biv) (exit : block)
    (initial_regs header_regs exit_regs : registers),
  well_formed_ssa blocks entry -> loop_graph_properties blocks entry loop ->
  deletion_certificate defs blocks loop bivs exit ->
  steps (enter entry initial_regs) (enter loop.(header) header_regs) ->
  region_steps loop.(body) (enter loop.(header) header_regs)
    (enter exit exit_regs) ->
  eligible_entry loop exit header_regs.
Proof.
  intros Hedges blocks entry defs loop bivs exit initial_regs header_regs
    exit_regs Hwf Hgraph Hcertificate Hprefix Hrun.
  pose proof Hcertificate as [[exit_info [Hexit [Htarget Hparams]]] Hrest].
  destruct (find_exit_branch_exit loop exit_info Hexit) as [Houtside Htargets].
  rewrite Htarget in Houtside.
  pose proof (loop_header_in_body _ _ _ Hgraph) as Hinside.
  destruct (region_exit_body_prefix loop.(body) loop.(header)
    (block_body loop.(header)) header_regs (enter exit exit_regs)
    Hinside Houtside Hrun) as [first [Hbody Hsegment]].
  split; [exact Hinside |]. split; [exact Houtside |].
  split; [exact Hparams |]. exists first, exit_regs.
  split; [exact Hbody |]. split; [exact Hsegment |].
  eapply finite_exit_live_agreement; eassumption.
Qed.

Section GraphEligibility.
  Variable blocks : list block.
  Variable entry : block.
  Hypothesis predecessors_closed : forall (b pred : block),
    In b blocks -> In pred (predecessors b) -> In pred blocks.
  Hypothesis successors_closed : forall (b succ : block),
    In b blocks -> In succ (all_successors b) -> In succ blocks.
  Hypothesis dominance : dominance_semantics entry.
  Hypothesis dominance_complete : forall (dominator target : block),
    In dominator blocks -> In target blocks ->
    (forall (path : list block), SsaDominance.path entry path target ->
       In dominator path) -> dominator --dom--> target.

  (* The actual deletion decision now guarantees live-out safety for all
     its accepted shapes. Finite exit remains an explicit premise, rather
     than being silently identified with the existing no-infinite results. *)
  Theorem find_deletions_finite_exit_eligible : control_edges ->
    forall (defs : op_def) (header exit : block),
    well_formed_ssa blocks entry ->
    In (header, exit) (find_deletions defs blocks) ->
    exists (loop : natural_loop) (bivs : list biv),
      In (loop, bivs) (InductionVar.analyze defs blocks)
      /\ header = loop.(NaturalLoop.header)
      /\ forall (initial_regs header_regs exit_regs : registers),
           steps (enter entry initial_regs) (enter header header_regs) ->
           region_steps loop.(body) (enter header header_regs)
             (enter exit exit_regs) -> eligible_entry loop exit header_regs.
  Proof.
    intros Hedges defs header exit Hwf Hin.
    destruct (find_deletions_graph_properties blocks entry predecessors_closed
      successors_closed dominance dominance_complete defs header exit Hin)
      as [loop [bivs [Hloop [Hheader [Hcertificate Hgraph]]]]].
    exists loop, bivs. split; [exact Hloop |]. split; [exact Hheader |].
    intros initial_regs header_regs exit_regs Hprefix Hrun. subst header.
    eapply certificate_finite_exit_eligible; eassumption.
  Qed.
End GraphEligibility.
