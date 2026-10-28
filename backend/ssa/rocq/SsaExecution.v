(* SSA well-formedness and the values available during execution.

   The well-formedness conditions below concern definitions, instruction
   positions and graph paths only. They contain no valuations, execution
   invariants or loop-analysis verdicts. The purpose of this layer is to
   derive operation equations at their actual uses, rather than assume
   equations for every freely constructed [value] term. The execution
   language is still the restricted fragment of SsaSemantics.v; these
   theorems do not assign semantics to unsupported operations. *)

From Stdlib Require Import ZArith Lia List.
From OxCamlStdlib Require Import OxCamlInt OxCamlInt64 OxCamlList.
From OxCamlBackend Require Import Operation.
From OxCamlSsa Require Import SsaModel SsaGraph SsaDominance SsaSemantics.
Import ListNotations.

Definition state_point (s : state) : point :=
  (current_block s, length (remaining s)).

(* The point immediately after an instruction is its definition site. *)
Definition result_definition (id : instr_id) (op : operation)
    (args : list value) (result_count : int) (site : point) : Prop :=
  exists (prefix suffix : list instr),
    block_body (fst site) = prefix ++ Op id op args result_count :: suffix
    /\ snd site = length suffix.

(* A reference carries the actual definition's payload, not just its ID.
   Parameters are available at entry; operation results after execution. *)
Definition value_definition (v : value) (site : point) : Prop :=
  match v with
  | Res id op args index =>
    exists (result_count : int),
      result_definition id op args result_count site
      /\ (0 <= to_Z index < to_Z result_count)%Z
  | Block_param b index =>
    site = entry_point b /\ nth_int (params b) index = Some v
  end.

Record well_formed_ssa (blocks : list block) (entry : block) : Prop :=
  { entry_in_graph : In entry blocks;
    (* Finished graphs contain only reachable blocks. This is structural
       reachability through program points, not a claim that operations
       execute successfully or that branches are dynamically feasible. *)
    graph_blocks_reachable : forall (b : block), In b blocks ->
      point_reachable entry (b, 0%nat);
    graph_successors_closed : forall (source target : block),
      In source blocks -> In target (all_successors source) ->
      In target blocks;
    graph_parameters : parameter_layout;
    result_sites_unique : forall (id : instr_id) (op op' : operation)
      (args args' : list value) (count count' : int) (site site' : point),
      In (fst site) blocks -> In (fst site') blocks ->
      result_definition id op args count site ->
      result_definition id op' args' count' site' -> site = site';
    operand_definitions : forall (id : instr_id) (op : operation)
      (args : list value) (count : int) (site : point),
      In (fst site) blocks -> result_definition id op args count site ->
      forall (arg : value), In arg args ->
      exists (arg_site : point),
        value_definition arg arg_site /\ In (fst arg_site) blocks
        /\ point_dominates entry arg_site site /\ arg_site <> site;
    terminator_definitions : forall (b : block) (args : list value),
      In b blocks -> In args (terminator_args (terminator b)) ->
      forall (arg : value), In arg args ->
      exists (arg_site : point),
        value_definition arg arg_site /\ In (fst arg_site) blocks
        /\ point_dominates entry arg_site (b, 0%nat) }.

(* Equations for actual instruction results. Parameters have no defining
   operation. Unbound parameters are allowed here; attempting to read one
   still gets stuck in the operational semantics. *)
Definition value_coherent (regs : registers) (v : value) : Prop :=
  match v with
  | Res id op args index =>
    exists (arg_values : list Z) (result : Z),
      read_values regs args = Some arg_values
      /\ eval_operation op arg_values = Some result
      /\ regs (Result id index) = Some result
  | Block_param _ _ => True
  end.

(* Availability is structural: a canonical definition in this graph
   dominates the program point. Merely sharing an instruction ID is not
   sufficient, and a definition later in the block is not available. *)
Definition available_value (blocks : list block) (entry : block)
    (position : point) (v : value) : Prop :=
  exists (site : point), value_definition v site /\ In (fst site) blocks
    /\ point_dominates entry site position.

(* Only available values are asserted coherent. Values from another
   branch, later instructions and stale results from a previous loop
   iteration need not satisfy any operation equation. *)
Definition coherent_at (blocks : list block) (entry : block)
    (regs : registers) (position : point) : Prop :=
  forall (v : value), available_value blocks entry position v ->
    value_coherent regs v.

(* Operands of an available result are available as well. *)
Lemma operand_available : forall (blocks : list block) (entry : block)
    (position : point) (id : instr_id) (op : operation) (args : list value)
    (index : int) (arg : value),
  well_formed_ssa blocks entry ->
  available_value blocks entry position (Res id op args index) ->
  In arg args -> available_value blocks entry position arg.
Proof.
  intros blocks entry position id op args index arg Hwf
    [site [[count [Hdefinition Hindex]] [Hsite Hdominates]]] Hin.
  destruct (operand_definitions _ _ Hwf id op args count site
    Hsite Hdefinition arg Hin) as [arg_site [Harg [Hargsite [Hdom _]]]].
  exists arg_site. split; [exact Harg |]. split; [exact Hargsite |].
  eapply point_dominance_transitive; eassumption.
Qed.

(* A terminator's operands are available when that terminator executes. *)
Lemma terminator_operand_available : forall (blocks : list block)
    (entry : block) (s : state) (args : list value) (arg : value),
  well_formed_ssa blocks entry -> In (current_block s) blocks ->
  remaining s = [] ->
  In args (terminator_args (terminator (current_block s))) -> In arg args ->
  available_value blocks entry (state_point s) arg.
Proof.
  intros blocks entry s args arg Hwf Hblock Hremaining Hargs Hin.
  destruct (terminator_definitions _ _ Hwf _ _ Hblock Hargs arg Hin)
    as [site [Hdefinition [Hsite Hdominates]]].
  exists site. split; [exact Hdefinition |]. split; [exact Hsite |].
  unfold state_point. rewrite Hremaining. exact Hdominates.
Qed.

(* A result site is strictly inside its block, never at block entry. *)
Lemma result_definition_not_entry : forall (id : instr_id) (op : operation)
    (args : list value) (result_count : int) (b : block),
  ~ result_definition id op args result_count (entry_point b).
Proof.
  intros id op args result_count b [prefix [suffix [Hbody Hlength]]].
  unfold entry_point in *. cbn in *.
  rewrite Hbody, length_app in Hlength. cbn in Hlength. lia.
Qed.

(* Two instructions at one definition point are the same instruction. *)
Lemma result_definition_at_point : forall (id id' : instr_id)
    (op op' : operation) (args args' : list value)
    (count count' : int) (site : point),
  result_definition id op args count site ->
  result_definition id' op' args' count' site ->
  Op id op args count = Op id' op' args' count'.
Proof.
  intros id id' op op' args args' count count' site
    [prefix [suffix [Hbody Hlength]]]
    [prefix' [suffix' [Hbody' Hlength']]].
  eapply same_position_element; [rewrite <- Hbody, <- Hbody'; reflexivity |].
  congruence.
Qed.

(* Canonical available references sharing a register share the complete
   value payload. The two references may be available at different points. *)
Lemma available_value_identity : forall (blocks : list block) (entry : block)
    (first second : point) (v w : value),
  well_formed_ssa blocks entry -> available_value blocks entry first v ->
  available_value blocks entry second w ->
  register_of_value v = register_of_value w -> v = w.
Proof.
  intros blocks entry first second
    [id op args index | b index] [id' op' args' index' | b' index'] Hwf
    [site [Hdefinition [Hsite Hdom]]]
    [site' [Hdefinition' [Hsite' Hdom']]] Hreg;
    cbn [register_of_value] in Hreg; try discriminate;
    inversion Hreg; subst.
  - destruct Hdefinition as [count [Hdefinition Hindex]].
    destruct Hdefinition' as [count' [Hdefinition' Hindex']].
    assert (site = site') by (eapply result_sites_unique; eassumption).
    subst site'.
    pose proof (result_definition_at_point _ _ _ _ _ _ _ _ _
      Hdefinition Hdefinition') as Hsame.
    injection Hsame as -> -> ->. reflexivity.
  - reflexivity.
Qed.

(* An instruction in a block has a definition site at the suffix after it. *)
Lemma result_definition_of_membership : forall (b : block) (id : instr_id)
    (op : operation) (args : list value) (count : int),
  In (Op id op args count) (block_body b) ->
  exists (site : point), fst site = b /\
    result_definition id op args count site.
Proof.
  intros b id op args count Hin. apply in_split in Hin.
  destruct Hin as [prefix [suffix Hbody]].
  exists (b, length suffix). split; [reflexivity |].
  exists prefix, suffix. auto.
Qed.

(* An available reference to a single-result instruction is its unique
   result, with the actual payload. Sharing an ID alone is not enough. *)
Lemma single_result_reference : forall (blocks : list block) (entry : block)
    (position : point) (b : block) (id : instr_id) (op : operation)
    (args : list value) (v : value),
  well_formed_ssa blocks entry -> In b blocks ->
  In (Op id op args one) (block_body b) ->
  available_value blocks entry position v ->
  instr_defines_value (Op id op args one) v = true ->
  v = Res id op args zero.
Proof.
  intros blocks entry position b id op args [actual_id actual_op actual_args
    index | parameter_block index] Hwf Hblock Hin
    [site [Hdefinition [Hsite Hdom]]] Hdefines; [ | discriminate].
  cbn [instr_defines_value] in Hdefines.
  apply instr_id_eqb_spec in Hdefines. subst actual_id.
  destruct Hdefinition as [count [Hdefinition Hindex]].
  destruct (result_definition_of_membership _ _ _ _ _ Hin)
    as [actual_site [Hactual_block Hactual]].
  assert (site = actual_site) as Heq.
  { eapply result_sites_unique;
      [exact Hwf | exact Hsite | | exact Hdefinition | exact Hactual].
    rewrite Hactual_block. exact Hblock. }
  subst site.
  pose proof (result_definition_at_point _ _ _ _ _ _ _ _ _
    Hdefinition Hactual) as Hsame.
  injection Hsame as -> -> ->.
  assert (index = zero) as ->.
  { apply Sint63.to_Z_inj. rewrite to_Z_zero, to_Z_one in *. lia. }
  reflexivity.
Qed.

(* A canonical definition outside a region cannot share its register
   with a definition inside. Unique sites rule out borrowed IDs. *)
Lemma definition_outside_region : forall (blocks : list block) (entry : block)
    (region : blockset) (v : value) (site : point),
  well_formed_ssa blocks entry ->
  (forall (b : block), set_mem b region = true -> In b blocks) ->
  value_definition v site -> In (fst site) blocks ->
  set_mem (fst site) region = false ->
  ~ defined_in_region region (register_of_value v).
Proof.
  intros blocks entry region [id op args index | b index] site Hwf Hmembers
    Hdefinition Hsite Houtside Hinside.
  - destruct Hdefinition as [count [Hdefinition Hindex]].
    destruct Hinside as [b [actual_op [actual_args [actual_count
      [Hblock Hmember]]]]].
    destruct (result_definition_of_membership _ _ _ _ _ Hmember)
      as [actual_site [Hactual_block Hactual]].
    assert (site = actual_site) as Heq.
    { eapply result_sites_unique;
        [exact Hwf | exact Hsite | | exact Hdefinition | exact Hactual].
      rewrite Hactual_block. apply Hmembers. exact Hblock. }
    rewrite Heq, Hactual_block in Houtside. congruence.
  - destruct Hdefinition as [-> Hparameter]. cbn in *. congruence.
Qed.

(* An executable instruction position corresponds to its actual body
   suffix. The successor point is precisely that instruction's site. *)
Lemma executing_result_definition : forall (b : block) (id : instr_id)
    (op : operation) (args : list value) (count : int) (rest : list instr)
    (regs : registers),
  valid_position
    {| current_block := b; remaining := Op id op args count :: rest;
       current_registers := regs |} ->
  result_definition id op args count (b, length rest).
Proof.
  intros b id op args count rest regs [prefix Hbody].
  exists prefix, rest. auto.
Qed.

(* Actual transitions project to structural program-point edges. *)
Theorem step_point_edge : control_edges -> forall (before after : state),
  valid_position before -> step before after ->
  point_edge (state_point before) (state_point after).
Proof.
  intros Hedges before after Hposition Hstep.
  destruct Hstep; unfold state_point; cbn.
  - apply Point_instruction. destruct Hposition as [prefix Hbody].
    cbn in Hbody. rewrite Hbody, length_app. cbn. lia.
  - apply Point_transfer. eapply goto_successor; eassumption.
  - apply Point_transfer. eapply switch_successor;
      [exact Hedges | eassumption | eapply nth_error_In; eassumption].
Qed.

(* A step preserves membership in a successor-closed graph. *)
Theorem step_in_graph : control_edges -> forall (blocks : list block)
    (entry : block) (before after : state),
  well_formed_ssa blocks entry -> In (current_block before) blocks ->
  step before after -> In (current_block after) blocks.
Proof.
  intros Hedges blocks entry before after Hwf Hin Hstep.
  destruct Hstep; cbn in *; [exact Hin | |].
  - eapply graph_successors_closed; [exact Hwf | exact Hin |].
    eapply goto_successor; eassumption.
  - eapply graph_successors_closed; [exact Hwf | exact Hin |].
    eapply switch_successor;
      [exact Hedges | eassumption | eapply nth_error_In; eassumption].
Qed.

(* Reachability follows the same structural edges used by dominance. *)
Lemma step_point_reachable : control_edges -> forall (entry : block)
    (before after : state),
  valid_position before -> point_reachable entry (state_point before) ->
  step before after -> point_reachable entry (state_point after).
Proof.
  intros Hedges entry before after Hposition [points Hpath] Hstep.
  exists (points ++ [state_point after]).
  eapply point_path_snoc; [exact Hpath |].
  eapply step_point_edge; eassumption.
Qed.

(* A finite execution extends a reachable program-point path. *)
Lemma steps_point_reachable : control_edges -> forall (entry : block)
    (before after : state),
  steps before after -> valid_position before ->
  point_reachable entry (state_point before) ->
  point_reachable entry (state_point after).
Proof.
  intros Hedges entry before after Hsteps. induction Hsteps;
    intros Hposition Hreachable.
  - exact Hreachable.
  - apply IHHsteps.
    + eapply step_valid_position; eassumption.
    + eapply step_point_reachable; eassumption.
Qed.

(* Registers of definitions at other sites cannot be changed by this
   step. For results this uses unique instruction identities; for
   parameters it uses the actual parameter layout of the target. *)
Theorem step_definition_frame :
  forall (blocks : list block) (entry : block) (before after : state)
    (v : value) (site : point),
  well_formed_ssa blocks entry -> valid_position before ->
  In (current_block before) blocks ->
  value_definition v site -> In (fst site) blocks ->
  site <> state_point after -> step before after ->
  current_registers after (register_of_value v)
    = current_registers before (register_of_value v).
Proof.
  intros blocks entry before after v site Hwf Hposition Hbefore
    Hdefinition Hsite Hneq Hstep.
  destruct v as [id op args index | b index].
  - destruct Hdefinition as [count [Hdefinition Hindex]].
    destruct Hstep as [source insn rest regs regs' Hexec |
      source target arguments regs values regs' Hterm Hread Hbind |
      source condition targets regs value target Hterm Hvalue Hpos Hnth
        Hparams];
      cbn in *.
    + destruct insn as [defined_id defined_op defined_args results | |];
        try discriminate.
      eapply execute_instruction_frame; [exact Hexec |].
      intros Heq. inversion Heq; subst.
      apply Hneq. eapply result_sites_unique;
        [exact Hwf | exact Hsite | exact Hbefore | exact Hdefinition |].
      eapply executing_result_definition. exact Hposition.
    + eapply bind_parameters_frame; [exact Hbind |].
      intros Hin. apply in_map_iff in Hin.
      destruct Hin as [parameter [Hreg Hin]].
      destruct (parameters_local (graph_parameters _ _ Hwf)
        target parameter Hin) as [param_index ->]. discriminate.
    + reflexivity.
  - destruct Hdefinition as [Hentry Hparam]. subst site.
    destruct Hstep as [source insn rest regs regs' Hexec |
      source target arguments regs values regs' Hterm Hread Hbind |
      source condition targets regs value target Hterm Hvalue Hpos Hnth
        Hparams];
      cbn in *.
    + destruct insn as [id op args results | |]; try discriminate.
      eapply execute_instruction_frame; [exact Hexec | discriminate].
    + eapply bind_parameters_frame; [exact Hbind |].
      intros Hin. apply in_map_iff in Hin.
      destruct Hin as [parameter [Hreg Hin]].
      destruct (parameters_local (graph_parameters _ _ Hwf)
        target parameter Hin) as [param_index ->].
      cbn in Hreg. inversion Hreg; subst.
      apply Hneq. reflexivity.
    + reflexivity.
Qed.

(* If a result's definition site is the new program point, this very step
   executed its instruction. A transfer cannot manufacture such a result
   because instruction result sites are never block-entry points. *)
Lemma step_new_result : forall (before after : state) (id : instr_id)
    (op : operation) (args : list value) (index : int),
  valid_position before -> step before after ->
  value_definition (Res id op args index) (state_point after) ->
  index = zero /\
  execute_instruction (current_registers before) (Op id op args one)
    = Some (current_registers after).
Proof.
  intros before after id op args index Hposition Hstep
    [count [Hdefinition Hindex]].
  destruct Hstep as [source insn rest regs regs' Hexec |
    source target arguments regs values regs' Hterm Hread Hbind |
    source condition targets regs value target Hterm Hvalue Hpos Hnth Hparams];
    cbn in *.
  - destruct insn as [actual_id actual_op actual_args actual_count | |];
      try discriminate.
    pose proof (executing_result_definition _ _ _ _ _ _ _ Hposition)
      as Hactual.
    pose proof (result_definition_at_point _ _ _ _ _ _ _ _ _
      Hdefinition Hactual) as Heq.
    injection Heq as -> -> -> ->.
    destruct (execute_instruction_result _ _ _ _ _ _ Hexec) as [Hcount _].
    subst actual_count. split; [ | exact Hexec].
    apply Sint63.to_Z_inj. rewrite to_Z_zero.
    rewrite to_Z_one in Hindex. lia.
  - exfalso. eapply result_definition_not_entry. exact Hdefinition.
  - exfalso. eapply result_definition_not_entry. exact Hdefinition.
Qed.

(* Operands of an available result cannot be rebound at the current
   point: their sites strictly dominate the result's site. Were an operand
   being rebound here, mutual dominance would contradict that strictness. *)
Lemma available_operands_frame :
  forall (blocks : list block) (entry : block) (before after : state)
    (id : instr_id) (op : operation) (args : list value)
    (count : int) (site : point),
  well_formed_ssa blocks entry -> valid_position before ->
  In (current_block before) blocks ->
  point_reachable entry (state_point after) ->
  result_definition id op args count site -> In (fst site) blocks ->
  point_dominates entry site (state_point after) -> step before after ->
  read_values (current_registers after) args
    = read_values (current_registers before) args.
Proof.
  intros blocks entry before after id op args count site Hwf Hposition
    Hbefore Hreachable Hdefinition Hsite Hdominates Hstep.
  apply read_values_ext. intros arg Hin.
  destruct (operand_definitions _ _ Hwf id op args count site
    Hsite Hdefinition arg Hin) as [arg_site [Harg [Hargsite [Hdom Hstrict]]]].
  eapply step_definition_frame; try eassumption.
  intros Heq. subst arg_site.
  assert (site = state_point after) by
    (eapply point_dominance_antisymmetric; eassumption).
  congruence.
Qed.

(* Available result equations are preserved by execution. New results
   satisfy them because the instruction just executed; other results and
   their operands are unchanged. No equation is assumed for a value whose
   definition is not yet available. *)
Theorem step_values_coherent : control_edges ->
  forall (blocks : list block) (entry : block) (before after : state),
  well_formed_ssa blocks entry -> valid_position before ->
  In (current_block before) blocks ->
  point_reachable entry (state_point before) ->
  coherent_at blocks entry (current_registers before) (state_point before) ->
  step before after ->
  coherent_at blocks entry (current_registers after) (state_point after).
Proof.
  intros Hedges blocks entry before after Hwf Hposition Hbefore Hreachable
    Hcoherent Hstep v [site [Hdefinition [Hsite Hdominates]]].
  destruct v as [id op args index | b index]; [ | exact I].
  pose proof Hdefinition as [count [Hresult Hindex]].
  assert (Hreachable_after : point_reachable entry (state_point after)).
  { eapply step_point_reachable; eassumption. }
  assert (Hargs : read_values (current_registers after) args
    = read_values (current_registers before) args).
  { eapply available_operands_frame; eassumption. }
  destruct (point_eqb site (state_point after)) eqn:E.
  - apply point_eqb_spec in E. subst site.
    destruct (step_new_result _ _ _ _ _ _ Hposition Hstep Hdefinition)
      as [Hindex_zero Hexec]. subst index.
    destruct (execute_instruction_result _ _ _ _ _ _ Hexec)
      as [_ [arg_values [result [Hread [Heval Hregs]]]]].
    exists arg_values, result. split; [rewrite Hargs; exact Hread |].
    split; [exact Heval |]. rewrite Hregs. apply write_register_same.
  - assert (Hneq : site <> state_point after).
    { intros Heq. assert (point_eqb site (state_point after) = true)
        by (apply point_eqb_spec; exact Heq). congruence. }
    assert (Hdominates_before :
      point_dominates entry site (state_point before)).
    { eapply point_dominates_predecessor;
        [exact Hdominates | exact Hneq |].
      eapply step_point_edge; eassumption. }
    assert (Havailable_before : available_value blocks entry
      (state_point before) (Res id op args index)).
    { exists site. auto. }
    destruct (Hcoherent _ Havailable_before)
      as [arg_values [result [Hread [Heval Hvalue]]]].
    exists arg_values, result. split; [rewrite Hargs; exact Hread |].
    split; [exact Heval |]. rewrite <- Hvalue.
    exact (step_definition_frame _ _ _ _ _ _ Hwf Hposition Hbefore
      Hdefinition Hsite Hneq Hstep).
Qed.

(* No instruction result is available at function entry. Consequently
   initial coherence holds for arbitrary input-register values; it is not
   an assumption about a valuation or a real execution. *)
Lemma entry_values_coherent : forall (blocks : list block) (entry : block)
    (initial_regs : registers),
  coherent_at blocks entry initial_regs (entry_point entry).
Proof.
  intros blocks entry initial_regs v
    [site [Hdefinition [Hsite Hdominates]]].
  destruct v as [id op args index | b index]; [ | exact I].
  pose proof (Hdominates [entry_point entry] (Point_path_one _)) as Hin.
  destruct Hin as [Heq | []]. subst site.
  destruct Hdefinition as [count [Hresult _]].
  exfalso. eapply result_definition_not_entry. exact Hresult.
Qed.

(* Operation equations for every available actual value follow from a
   finite execution and structural SSA well-formedness. This replaces a
   global machine-valuation premise with an operational theorem. *)
Theorem execution_values_coherent : control_edges ->
  forall (blocks : list block) (entry : block) (initial_regs : registers)
    (reached : state),
  well_formed_ssa blocks entry -> steps (enter entry initial_regs) reached ->
  coherent_at blocks entry (current_registers reached) (state_point reached).
Proof.
  intros Hedges blocks entry initial_regs reached Hwf Hrun.
  assert (forall before after, steps before after ->
    valid_position before -> In (current_block before) blocks ->
    point_reachable entry (state_point before) ->
    coherent_at blocks entry (current_registers before) (state_point before) ->
    coherent_at blocks entry (current_registers after) (state_point after))
    as Hsteps.
  { intros before after Hsteps. induction Hsteps;
      intros Hposition Hin Hreachable Hcoherent.
    - exact Hcoherent.
    - apply IHHsteps.
      + eapply step_valid_position; eassumption.
      + eapply step_in_graph; eassumption.
      + eapply step_point_reachable; eassumption.
      + eapply step_values_coherent; eassumption. }
  eapply Hsteps; [exact Hrun | apply enter_valid_position | | |].
  - apply (entry_in_graph _ _ Hwf).
  - exists [entry_point entry]. constructor.
  - apply entry_values_coherent.
Qed.
