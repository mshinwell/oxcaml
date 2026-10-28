(* Defined operands and progress for the supported SSA fragment.

   [control_layout] formalizes ordinary builder guarantees: Goto arguments
   match parameters, omitted arguments feed globally unused parameters,
   and Switch targets have no parameters. [switches_in_range] is the
   standard defined-input condition for SSA Switch (out-of-range indices
   are undefined behavior); it asserts neither progress nor termination.
   All instruction definedness below follows from liveness and execution.
   This module is proof-only. *)

From Stdlib Require Import ZArith Lia Bool List Classical_Prop.
From OxCamlStdlib Require Import OxCamlInt OxCamlList.
From OxCamlSsa Require Import SsaModel SsaGraph SsaDominance SsaSemantics
  SsaExecution SsaLiveness.
Import ListNotations.
Local Open Scope Z_scope.

Definition register_used (blocks : list block) (reg : register) : Prop :=
  exists (position : point) (v : value), In (fst position) blocks
    /\ operand_at position v /\ register_of_value v = reg.

Record control_layout (blocks : list block) : Prop :=
  { goto_parameter_layout : forall (source target : block)
      (args : list Terminator.arg),
      In source blocks ->
      terminator source = Terminator.Continue (Goto target) args ->
      Forall2 (fun (arg : Terminator.arg) (parameter : value) =>
        match arg with
        | Terminator.Arg _ => True
        | Terminator.Omitted_since_unused =>
          ~ register_used blocks (register_of_value parameter)
        end) args (params target);
    switch_parameterless : forall (source : block) (index : value)
      (targets : list block) (target : block),
      In source blocks -> terminator source = Terminator.Switch index targets ->
      In target targets -> params target = [] }.

Definition live_registers_bound (position : point) (regs : registers) : Prop :=
  forall (reg : register), live_at position reg ->
    exists (word : Z), regs reg = Some word.

Definition switches_in_range (initial : state) : Prop :=
  forall (reached : state) (index : value) (targets : list block) (word : Z),
  steps initial reached -> remaining reached = [] ->
  terminator (current_block reached) = Terminator.Switch index targets ->
  current_registers reached (register_of_value index) = Some word ->
  0 <= word < Z.of_nat (length targets).

(* Liveness witnesses a real operand somewhere in the successor-closed
   graph, even when the read is several blocks away. *)
Lemma live_register_used : forall (blocks : list block) (entry : block)
    (position : point) (reg : register),
  well_formed_ssa blocks entry -> In (fst position) blocks ->
  live_at position reg -> register_used blocks reg.
Proof.
  intros blocks entry position reg Hwf Hin Hlive. revert Hin.
  induction Hlive; intros Hin.
  - exists position, v. auto.
  - apply IHHlive. eapply point_edge_in_graph; eassumption.
Qed.

(* Reading a list succeeds when every referenced register is bound. *)
Lemma read_values_bound : forall (regs : registers) (args : list value),
  (forall (arg : value), In arg args ->
    exists (word : Z), regs (register_of_value arg) = Some word) ->
  exists (words : list Z), read_values regs args = Some words.
Proof.
  intros regs args. induction args as [ | arg args IH]; intros Hbound.
  - exists []. reflexivity.
  - destruct (Hbound arg (or_introl eq_refl)) as [word Hword].
    destruct (IH ltac:(intros v Hin; apply Hbound; right; exact Hin))
      as [words Hwords].
    exists (word :: words). cbn [read_values]. rewrite Hword, Hwords.
    reflexivity.
Qed.

(* A used parameter cannot receive an omitted argument. The actual read
   and simultaneous binding therefore give it a concrete word. *)
Lemma used_parameter_bound : forall (blocks : list block)
    (args : list Terminator.arg) (parameters : list value)
    (before after : registers) (words : list (option Z)),
  Forall2 (fun (arg : Terminator.arg) (parameter : value) =>
    match arg with
    | Terminator.Arg _ => True
    | Terminator.Omitted_since_unused =>
      ~ register_used blocks (register_of_value parameter)
    end) args parameters ->
  read_arguments before args = Some words ->
  Forall2 (fun (parameter : value) (word : option Z) =>
    after (register_of_value parameter) = word) parameters words ->
  forall (parameter : value), In parameter parameters ->
  register_used blocks (register_of_value parameter) ->
  exists (word : Z), after (register_of_value parameter) = Some word.
Proof.
  intros blocks args parameters before after words Hlayout.
  revert words. induction Hlayout as [ | arg parameter args parameters
    Hallowed Hlayout IH]; intros words Hread Hbound selected Hin Hused.
  - contradiction.
  - destruct arg as [v |]; cbn [read_arguments] in Hread.
    + destruct (before (register_of_value v)) as [word |] eqn:Hvalue;
        [ | discriminate].
      destruct (read_arguments before args) as [rest |] eqn:Hrest;
        [ | discriminate]. injection Hread as <-.
      inversion Hbound; subst. destruct Hin as [<- | Hin].
      * exists word. assumption.
      * eapply IH; try eassumption; reflexivity.
    + destruct (read_arguments before args) as [rest |] eqn:Hrest;
        [ | discriminate]. injection Hread as <-.
      inversion Hbound; subst. destruct Hin as [<- | Hin].
      * contradiction.
      * eapply IH; try eassumption; reflexivity.
Qed.

(* A newly defined live register is bound by the actual step. Results
   come from executing an instruction; used parameters receive arguments. *)
Lemma step_new_live_bound : forall (blocks : list block) (entry : block)
    (before after : state) (reg : register),
  well_formed_ssa blocks entry -> control_layout blocks ->
  valid_position before -> In (current_block before) blocks ->
  defined_at (state_point after) reg -> register_used blocks reg ->
  step before after ->
  exists (word : Z), current_registers after reg = Some word.
Proof.
  intros blocks entry before after reg Hwf Hlayout Hposition Hblock
    [v [Hdefinition <-]] Hused Hstep.
  destruct v as [id op args index | b index].
  - destruct (step_new_result _ _ _ _ _ _ Hposition Hstep Hdefinition)
      as [-> Hexec].
    destruct (execute_instruction_result _ _ _ _ _ _ Hexec)
      as [_ [words [result [Hread [Heval Hregs]]]]].
    exists result. rewrite Hregs. apply write_register_same.
  - destruct Hdefinition as [Hentry Hparam].
    destruct Hstep; cbn [state_point enter] in Hentry.
    + unfold entry_point in Hentry. injection Hentry as Hsame Hlength.
      subst b0. destruct Hposition as [prefix Hbody]. cbn in Hbody.
      rewrite Hbody, length_app in Hlength. cbn in Hlength. lia.
    + unfold entry_point in Hentry. injection Hentry as Hsame Hlength.
      subst target.
      eapply used_parameter_bound with (parameters := params b)
        (args := args) (before := rs) (words := zs).
      * eapply goto_parameter_layout; eassumption.
      * exact H0.
      * eapply bind_parameters_values; [apply (parameters_distinct
          (graph_parameters _ _ Hwf)) | exact H1].
      * eapply nth_int_In. exact Hparam.
      * exact Hused.
    + unfold entry_point in Hentry. injection Hentry as Hsame Hlength.
      subst target. rewrite H3 in Hparam. discriminate.
Qed.

(* Live-register definedness is preserved by execution. Old values are
   needed on the preceding edge; new definitions are handled above. *)
Theorem step_live_registers_bound : control_edges ->
  forall (blocks : list block) (entry : block) (before after : state),
  well_formed_ssa blocks entry -> control_layout blocks ->
  valid_position before -> In (current_block before) blocks ->
  live_registers_bound (state_point before) (current_registers before) ->
  step before after ->
  live_registers_bound (state_point after) (current_registers after).
Proof.
  intros Hedges blocks entry before after Hwf Hlayout Hposition Hblock Hbound
    Hstep reg Hlive.
  assert (Hafter : In (current_block after) blocks).
  { eapply step_in_graph; eassumption. }
  destruct (classic (defined_at (state_point after) reg)) as [Hnew | Hold].
  - eapply step_new_live_bound; try eassumption.
    exact (live_register_used blocks entry (state_point after) reg
      Hwf Hafter Hlive).
  - assert (Hlive_before : live_at (state_point before) reg).
    { eapply Live_predecessor; [ | exact Hold | exact Hlive].
      eapply step_point_edge; eassumption. }
    destruct (Hbound _ Hlive_before) as [word Hword]. exists word.
    destruct (live_at_available blocks entry (state_point after) reg
      Hwf Hafter Hlive)
      as [v [Hreg [site [Hdefinition [Hsite Hdom]]]]].
    assert (Hneq : site <> state_point after).
    { intros Heq. subst site. apply Hold. exists v. auto. }
    rewrite <- Hreg.
    rewrite (step_definition_frame blocks entry before after v site Hwf
      Hposition Hblock Hdefinition Hsite Hneq Hstep).
    rewrite Hreg. exact Hword.
Qed.

(* Bound input registers give bound live operands at every reached point.
   No boundness invariant is required as an execution premise. *)
Theorem execution_live_registers_bound : control_edges ->
  forall (blocks : list block) (entry : block) (initial_regs : registers)
    (reached : state),
  well_formed_ssa blocks entry -> control_layout blocks ->
  live_registers_bound (entry_point entry) initial_regs ->
  steps (enter entry initial_regs) reached ->
  live_registers_bound (state_point reached) (current_registers reached).
Proof.
  intros Hedges blocks entry initial_regs reached Hwf Hlayout Hinitial Hsteps.
  assert (Hrun : forall (before after : state), steps before after ->
    valid_position before -> In (current_block before) blocks ->
    live_registers_bound (state_point before) (current_registers before) ->
    live_registers_bound (state_point after) (current_registers after)).
  { intros before after Hrun. induction Hrun; intros Hposition Hin Hbound;
      [exact Hbound |].
    apply IHHrun.
    - eapply step_valid_position; eassumption.
    - eapply step_in_graph; eassumption.
    - eapply step_live_registers_bound; eassumption. }
  eapply Hrun; [exact Hsteps | apply enter_valid_position |
    exact (entry_in_graph _ _ Hwf) | exact Hinitial].
Qed.

(* Reading Goto arguments succeeds when each non-omitted input is bound;
   omitted arguments still occupy a parameter position. *)
Lemma read_arguments_bound : forall (regs : registers)
    (args : list Terminator.arg),
  (forall (arg : value), In (Terminator.Arg arg) args ->
     exists (word : Z), regs (register_of_value arg) = Some word) ->
  exists (words : list (option Z)), read_arguments regs args = Some words
    /\ length words = length args.
Proof.
  intros regs args. induction args as [ | [arg |] args IH]; intros Hbound.
  - exists []. auto.
  - destruct (Hbound arg (or_introl eq_refl)) as [word Hword].
    destruct (IH ltac:(intros v Hin; apply Hbound; right; exact Hin))
      as [words [Hwords Hlength]].
    exists (Some word :: words). split; [ | cbn; congruence].
    cbn [read_arguments]. rewrite Hword, Hwords. reflexivity.
  - destruct (IH ltac:(intros v Hin; apply Hbound; right; exact Hin))
      as [words [Hwords Hlength]].
    exists (None :: words). split; [ | cbn; congruence].
    cbn [read_arguments]. rewrite Hwords. reflexivity.
Qed.

(* Equal-length parameter and argument lists can always be bound. *)
Lemma bind_parameters_total : forall (parameters : list value)
    (words : list (option Z)) (regs : registers),
  length parameters = length words ->
  exists (after : registers),
    bind_parameters parameters words regs = Some after.
Proof.
  intros parameters. induction parameters as [ | parameter parameters IH];
    intros [ | word words] regs Hlength; try discriminate.
  - exists regs. reflexivity.
  - cbn [bind_parameters]. apply IH. cbn in Hlength. lia.
Qed.

(* A supported state with bound live registers makes progress, provided
   its Switch (if any) has a defined index. No loop property is used. *)
Theorem supported_state_progress : forall (blocks : list block)
    (entry : block) (s : state),
  well_formed_ssa blocks entry -> control_layout blocks ->
  valid_position s -> In (current_block s) blocks ->
  live_registers_bound (state_point s) (current_registers s) ->
  supported_block (current_block s) = true ->
  (forall (index : value) (targets : list block) (word : Z),
    remaining s = [] ->
    terminator (current_block s) = Terminator.Switch index targets ->
    current_registers s (register_of_value index) = Some word ->
    0 <= word < Z.of_nat (length targets)) ->
  exists (next : state), step s next.
Proof.
  intros blocks entry [b insns regs] Hwf Hlayout Hposition Hblock Hbound
    Hsupported Hswitch.
  unfold supported_block in Hsupported. apply andb_true_iff in Hsupported.
  destruct Hsupported as [Hinsns Hterm]. cbn in *.
  destruct insns as [ | insn rest].
  - destruct (terminator b) as [continuation args | index targets | |]
      eqn:Hterminator; try discriminate.
    + destruct continuation as [target | | kind |]; try discriminate.
      destruct (read_arguments_bound regs args) as [words [Hread Hlength]].
      { intros arg Hin.
        destruct (continue_argument_operand (Goto target) args arg Hin)
          as [uses [Huses Huse]].
        apply Hbound. apply Live_read.
        eapply Terminator_operand with (b := b) (args := uses).
        - rewrite Hterminator. exact Huses.
        - exact Huse. }
      pose proof (goto_parameter_layout _ Hlayout b target args Hblock
        Hterminator) as Hparameters.
      assert (Harity : length (params target) = length words).
      { rewrite Hlength. symmetry. eapply Forall2_length. exact Hparameters. }
      destruct (bind_parameters_total _ _ regs Harity) as [after Hbind].
      exists (enter target after). econstructor; eassumption.
    + destruct (Hbound (register_of_value index)) as [word Hword].
      { apply Live_read.
        eapply Terminator_operand with (b := b) (args := [index]);
          [rewrite Hterminator; cbn; auto | cbn; auto]. }
      pose proof (Hswitch index targets word eq_refl eq_refl Hword) as Hrange.
      assert (Hindex : (Z.to_nat word < length targets)%nat) by lia.
      destruct (nth_error targets (Z.to_nat word)) as [target |] eqn:Htarget.
      * exists (enter target regs). eapply Step_switch; try eassumption.
        -- lia.
        -- eapply switch_parameterless; [exact Hlayout | exact Hblock |
             exact Hterminator | eapply nth_error_In; exact Htarget].
      * apply nth_error_None in Htarget. lia.
  - assert (Hin : In insn (block_body b)).
    { destruct Hposition as [prefix Hbody]. cbn in Hbody. rewrite Hbody.
      apply in_or_app. right. left. reflexivity. }
    apply forallb_forall with (x := insn) in Hinsns; [ | exact Hin].
    assert (Hreads : exists (words : list Z),
      read_values regs (args_of_instr insn) = Some words).
    { apply read_values_bound. intros arg Harg. apply Hbound.
      destruct insn as [id op args count | |]; try contradiction.
      apply Live_read. eapply Instruction_operand; [ | exact Harg].
      eapply executing_result_definition. exact Hposition. }
    destruct Hreads as [words Hread].
    destruct (supported_instruction_executes _ _ _ Hinsns Hread)
      as [id [op [args [result [Hinsn [Heval Hexec]]]]]].
    eexists. apply Step_instruction. exact Hexec.
Qed.

(* A proof-only executable successor function. None means that this
   partial semantics has no next step; it is not a successful exit. *)
Definition next_state (s : state) : option state :=
  match s.(remaining) with
  | insn :: rest =>
    match execute_instruction s.(current_registers) insn with
    | Some regs => Some {| current_block := s.(current_block);
                           remaining := rest; current_registers := regs |}
    | None => None
    end
  | [] =>
    match terminator s.(current_block) with
    | Terminator.Continue (Goto target) args =>
      match read_arguments s.(current_registers) args with
      | Some words =>
        match bind_parameters (params target) words s.(current_registers) with
        | Some regs => Some (enter target regs)
        | None => None
        end
      | None => None
      end
    | Terminator.Switch index targets =>
      match s.(current_registers) (register_of_value index) with
      | Some word =>
        if Z.leb 0 word then
          match nth_error targets (Z.to_nat word) with
          | Some target =>
            match params target with
            | [] => Some (enter target s.(current_registers))
            | _ :: _ => None
            end
          | None => None
          end
        else None
      | None => None
      end
    | _ => None
    end
  end.

(* Every actual semantic step is found by the successor function. This
   lets the finite-exit proof construct a trace without a choice axiom. *)
Lemma next_state_complete : forall (before after : state),
  step before after -> next_state before = Some after.
Proof.
  intros before after Hstep. destruct Hstep;
    cbn [next_state current_registers remaining current_block].
  - rewrite H. reflexivity.
  - rewrite H, H0, H1. reflexivity.
  - rewrite H, H0, (proj2 (Z.leb_le _ _) H1), H2, H3. reflexivity.
Qed.
