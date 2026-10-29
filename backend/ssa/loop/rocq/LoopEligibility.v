(* Semantic eligibility for bypassing a loop, stated on the original graph.

   [eligible_entry] is the target property, not a record of analysis
   answers. It requires a finite normal exit, and equality with the first
   header execution on every register read before its next definition.
   The retained header is executed, not skipped. Determinism makes the
   finite execution witness exclude a different divergent execution.

   Start review with [eligible_entry] and [find_deletions_eligible]. The
   latter proves finite first exit and live-out agreement for every
   accepted counter shape. Its premises are graph metadata, bound function
   inputs, a reached header, and the language's defined-index condition
   [switches_in_range]. The extracted gate checks graph size and prefix
   instruction coverage; [find_deletions_supported] proves these checks.
   It assumes no recurrence, invariant bound, guard outcome or finite exit.

   The loop executes in SsaSemantics.v. Its unchanged prefix uses
   SsaContext.v's word-observation overapproximation, so loads, calls and
   other opaque computations need not be given full memory semantics.
   Review that abstraction and the graph contracts in SsaExecution.v,
   SsaGraph.v and SsaProgress.v alongside the extraction veneer. Finite exit
   follows directly by iteration; definedness uses classical case splits.
   Neither introduces semantic axioms.

   No post-deletion graph, renaming or pruning is modelled here, and
   eligibility is not assumed as a compiler contract. The step from
   [eligible_entry], per loop and per header entry, to the rewritten
   function behaving like the original is the usual liveness simulation;
   it is written out in ROCQ-REVIEWER-OBLIGATIONS.md, section 7. Its one
   non-obvious point: a register live at the exit's entry is live at the
   header's terminator, because the exit is a successor of the header and
   has no parameters, so nothing is defined on entering it. Nothing is
   extracted. *)

From Stdlib Require Import List Bool.
From OxCamlSsa Require Import SsaModel SsaGraph SsaDominance SsaSemantics
  SsaExecution SsaLiveness SsaProgress SsaContext.
From OxCamlLoop Require Import NaturalLoop InductionVar DeleteEmptyLoops
  LoopExecution LoopLiveOut LoopCounterExecution LoopRangeExecution.
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

(* For an accepted loop, a finite original execution to its exit suffices:
   the first header computation and live-out agreement are both derived.
   No equality of dead counter values is required. *)
Theorem certificate_finite_exit_eligible : control_edges ->
  forall (blocks : list block) (entry : block) (defs : op_def)
    (loop : natural_loop) (bivs : list biv) (exit : block)
    (initial_regs header_regs exit_regs : registers),
  well_formed_ssa blocks entry -> loop_graph_properties blocks entry loop ->
  deletion_certificate defs blocks loop bivs exit ->
  context_steps (enter entry initial_regs) (enter loop.(header) header_regs) ->
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

(* Progress inside an accepted loop follows from the instruction
   whitelist and ordinary SSA input/argument definedness. The only dynamic
   side condition is the language's defined-index rule for Switch. *)
Theorem certificate_region_progress : control_edges ->
  forall (blocks : list block) (entry : block) (defs : op_def)
    (loop : natural_loop) (bivs : list biv) (exit : block)
    (initial_regs header_regs : registers),
  well_formed_ssa blocks entry -> control_layout blocks ->
  loop_graph_properties blocks entry loop ->
  deletion_certificate defs blocks loop bivs exit ->
  live_registers_bound (entry_point entry) initial_regs ->
  switches_in_range (enter loop.(header) header_regs) ->
  context_steps (enter entry initial_regs) (enter loop.(header) header_regs) ->
  forall (reached : state),
  region_steps loop.(body) (enter loop.(header) header_regs) reached ->
  set_mem (current_block reached) loop.(body) = true ->
  exists (next : state), SsaSemantics.step reached next.
Proof.
  intros Hedges blocks entry defs loop bivs exit initial_regs header_regs
    Hwf Hlayout Hgraph Hcertificate Hinputs Hswitches Hprefix reached
    Hsegment Hinside.
  assert (Hrun : context_steps (enter entry initial_regs) reached).
  { eapply context_steps_trans; [exact Hprefix |].
    apply context_of_steps. exact (region_steps_execution _ _ _ Hsegment). }
  eapply supported_state_progress; [exact Hwf | exact Hlayout | | | | |].
  - eapply context_steps_valid_position;
      [exact Hrun | apply enter_valid_position].
  - apply (loop_body_in_graph _ _ _ Hgraph). exact Hinside.
  - eapply context_execution_live_registers_bound; eassumption.
  - destruct Hcertificate as [_ [_ [_ [_ [Hsupported _]]]]].
    destruct (Hsupported _ Hinside) as [Hinsns Hterm].
    unfold supported_block. apply andb_true_iff. split; [ | exact Hterm].
    apply forallb_forall. exact Hinsns.
  - intros index targets word Hremaining Hterm Hword.
    eapply Hswitches; [exact (region_steps_execution _ _ _ Hsegment) |
      exact Hremaining | exact Hterm | exact Hword].
Qed.

(* Full semantic eligibility in the integer/control-flow semantics.
   Finite exit is a conclusion, as are the actual counter recurrence,
   bound constancy, entry guards, range facts and live-out agreement.
   No post-deletion graph is needed. *)
Theorem certificate_entry_eligible : control_edges ->
  forall (blocks : list block) (entry : block) (defs : op_def)
    (loop : natural_loop) (bivs : list biv) (exit : block)
    (initial_regs header_regs : registers),
  well_formed_ssa blocks entry -> control_layout blocks ->
  loop_graph_properties blocks entry loop -> dominance_semantics entry ->
  op_def_correct defs blocks ->
  (forall (dominator target : block),
    In dominator blocks -> In target blocks ->
    (forall (path : list block), SsaDominance.path entry path target ->
       In dominator path) -> dominator --dom--> target) ->
  switch_edge_multiplicity -> graph_size_supported blocks ->
  NoDup (strict_dominators loop.(header)) ->
  (forall (dominator : block),
     In dominator (strict_dominators loop.(header)) -> In dominator blocks) ->
  deletion_certificate defs blocks loop bivs exit ->
  bounded_registers initial_regs ->
  live_registers_bound (entry_point entry) initial_regs ->
  switches_in_range (enter loop.(header) header_regs) ->
  context_steps (enter entry initial_regs) (enter loop.(header) header_regs) ->
  eligible_entry loop exit header_regs.
Proof.
  intros Hedges blocks entry defs loop bivs exit initial_regs header_regs
    Hwf Hlayout Hgraph Hdominance Hdefs Hcomplete Hmultiplicity Hsize Hnodup
    Hmembers Hcertificate Hbounded Hinputs Hswitches Hprefix.
  assert (Hprogress : forall (reached : state),
    region_steps loop.(body) (enter loop.(header) header_regs) reached ->
    set_mem (current_block reached) loop.(body) = true ->
    exists (next : state), SsaSemantics.step reached next).
  { eapply certificate_region_progress; eassumption. }
  destruct (accepted_loop_finite_exit blocks entry defs loop bivs exit
    initial_regs header_regs Hedges Hwf Hgraph Hcertificate Hprefix
    Hprogress Hdominance Hdefs Hcomplete Hmultiplicity Hsize Hnodup Hmembers
    Hbounded) as [reached [Hrun Houtside]].
  pose proof Hcertificate as [_ [_ [_ [_ [_ Honly]]]]].
  destruct (region_exit_target Hedges loop exit
    (enter loop.(header) header_regs) reached Honly
    (loop_header_in_body _ _ _ Hgraph) Hrun Houtside) as [exit_regs Heq].
  subst reached. eapply certificate_finite_exit_eligible; eassumption.
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

  (* The public theorem starts from the actual deletion decision. Its
     graph premises concern builder metadata only;
     its input premises are ordinary bound arguments and defined Switch
     indices. No loop recurrence or termination premise remains. *)
  Theorem find_deletions_eligible : control_edges ->
    forall (defs : op_def) (header exit : block),
    well_formed_ssa blocks entry -> control_layout blocks ->
    op_def_correct defs blocks -> switch_edge_multiplicity ->
    NoDup (strict_dominators header) ->
    (forall (dominator : block), In dominator (strict_dominators header) ->
       In dominator blocks) ->
    In (header, exit) (find_deletions defs blocks) ->
    exists (loop : natural_loop) (bivs : list biv),
      In (loop, bivs) (InductionVar.analyze defs blocks)
      /\ header = loop.(NaturalLoop.header)
      /\ forall (initial_regs header_regs : registers),
           bounded_registers initial_regs ->
           live_registers_bound (entry_point entry) initial_regs ->
           switches_in_range (enter header header_regs) ->
           context_steps (enter entry initial_regs)
             (enter header header_regs) ->
           eligible_entry loop exit header_regs.
  Proof.
    intros Hedges defs header exit Hwf Hlayout Hdefs Hmultiplicity
      Hnodup Hmembers Hin.
    pose proof (proj1 (find_deletions_supported _ _ _ _ Hin)) as Hsize.
    destruct (find_deletions_graph_properties blocks entry predecessors_closed
      successors_closed dominance dominance_complete defs header exit Hin)
      as [loop [bivs [Hloop [Hheader [Hcertificate Hgraph]]]]].
    exists loop, bivs. split; [exact Hloop |]. split; [exact Hheader |].
    intros initial_regs header_regs Hbounded Hinputs Hswitches Hprefix.
    subst header. eapply certificate_entry_eligible; eassumption.
  Qed.
End GraphEligibility.
