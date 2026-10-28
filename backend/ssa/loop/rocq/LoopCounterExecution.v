(* The arithmetic of a loop counter in actual SSA execution.

   Update equations are derived from [value_coherent], itself proved from
   execution in SsaExecution.v. Consecutive header entries are selected
   using LoopExecution.v, so a recurrence step is one actual traversal of
   the loop, including whichever back edge it takes. No field of
   [infinite_header_run] is assumed here.

   The public theorems at the end compose [find_deletions] with this
   semantics: literal-bound tests, and counters satisfying the static
   [unconditional_counter] predicate, cannot execute forever inside the
   reported loop. Register bounds needing affine entry-range facts are
   not covered yet. Neither theorem proves progress from stuck states,
   live-out agreement or correctness of the graph rewrite.

   Review the definitions in the first section, the public theorem
   statements at the end, and their imported contracts: [control_edges],
   [well_formed_ssa], [dominance_semantics], [op_def_correct] and
   [no_infinite_execution_in]. The intervening lemmas are proved from
   those contracts, not extra assumptions on the compiler. *)

From Stdlib Require Import ZArith Lia Bool List.
From OxCamlStdlib Require Import OxCamlInt OxCamlInt64 OxCamlList.
From OxCamlBackend Require Import Operation IntegerComparison.
From OxCamlSsa Require Import SsaModel SsaGraph SsaSemantics SsaExecution.
From OxCamlLoop Require Import NaturalLoop InductionVar LoopTermination
  LoopComparisons DeleteEmptyLoops LoopExecution LoopInvariantExecution.
Import ListNotations.
Local Open Scope Z_scope.

(* ======================================================================== *)
(* Static coverage and observations (nothing in this file is extracted)     *)
(* ======================================================================== *)

(* A syntactic condition on the actual header terminator: its index is
   computed by an immediate integer comparison. The deletion checks
   establish the operand arity and the continuing/exit targets. *)
Definition literal_header_test (header : block) : Prop :=
  exists (id : instr_id) (cmp : integer_comparison) (limit : int)
    (args : list value) (index : int) (targets : list block),
    terminator header =
      Terminator.Switch
        (Res id (Intop_imm (Icomp cmp) limit) args index) targets.

(* The part of the termination checker that needs no entry-range facts.
   This is a static property of the analyzed counter and header test,
   not an assumption about execution or the bound's value. For example,
   a step of one with the continuing comparison [Clt] qualifies. *)
Definition unconditional_counter (defs : op_def) (biv : biv) : Prop :=
  exists (exit_info : exit_branch) (step_size : int)
    (cmp : integer_comparison) (iv_is_left : bool) (bnd : bound),
    find_exit_branch biv.(InductionVar.loop) = Some exit_info
    /\ signed_step biv = Some step_size
    /\ extract_comparison
         (fun v => is_param biv.(InductionVar.loop).(header)
           biv.(param_index) v || existsb (value_eqb v) biv.(update))
         (is_loop_invariant defs biv.(InductionVar.loop).(header))
         exit_info.(condition) = Some (cmp, iv_is_left, bnd)
    /\ continue_terminates step_size
         (oriented_continue_comparison iv_is_left
           exit_info.(continue_when_true) cmp) = LoopComparisons.Terminates.

(* The comparison may test the parameter or its just-computed update.
   This choice depends on the reference, not on the execution state. *)
Definition tested_counter (loop : natural_loop) (biv : biv)
    (counter_ref : value) (step_size : int) (counter : Z) : Z :=
  if is_param loop.(header) biv.(param_index) counter_ref then counter
  else wrap64 (counter + to_Z step_size).

(* The concrete instruction shape of an extracted comparison. *)
Definition comparison_shape (condition : value) (cmp : integer_comparison)
    (iv_is_left : bool) (counter_ref : value) (bnd : bound) : Prop :=
  exists (id : instr_id) (index : int),
    match bnd with
    | Const_bound constant =>
      iv_is_left = true
      /\ condition =
           Res id (Intop_imm (Icomp cmp) constant) [counter_ref] index
    | Value_bound bound_ref =>
      condition = Res id (Intop (Icomp cmp))
        (if iv_is_left then [counter_ref; bound_ref]
         else [bound_ref; counter_ref]) index
    end.

Definition read_bound (regs : registers) (bnd : bound) : option Z :=
  match bnd with
  | Const_bound constant => Some (to_Z constant)
  | Value_bound bound_ref => regs (register_of_value bound_ref)
  end.

(* ======================================================================== *)
(* Operational lemmas                                                      *)
(* ======================================================================== *)

(* A reported counter index is in range: an update is passed at that
   position by a Goto whose argument list matches the header parameters. *)
Lemma biv_parameter_identity : parameter_layout ->
  forall (defs : op_def) (loop : natural_loop) (biv : biv),
  biv_spec defs loop biv ->
  param loop.(header) biv.(param_index)
    = Block_param loop.(header) biv.(param_index).
Proof.
  intros Hlayout defs loop biv [_ [Hnonempty [_ [_ Harrives]]]].
  destruct biv.(update) as [ | updated updates] eqn:Hupdates;
    [contradiction |].
  assert (Hin : In updated biv.(update)).
  { rewrite Hupdates. left. reflexivity. }
  destruct (Harrives updated Hin) as [source [args [_ [Hgoto Harg]]]].
  destruct (same_length_nth_int args (params loop.(header)) biv.(param_index)
    (Terminator.Arg updated) (goto_args_arity _ _ _ Hgoto)
    (arg_value_nth _ _ _ Harg)) as [parameter Hparameter].
  rewrite (parameter_lookup Hlayout _ _ _ Hparameter).
  apply (parameter_identity Hlayout _ _ _ Hparameter).
Qed.

(* An actual update result is the current parameter plus the signed step,
   with machine wraparound. Both the parameter and the result are bound. *)
Lemma biv_update_observed : forall (defs : op_def) (loop : natural_loop)
    (biv : biv) (step_size : int) (updated : value) (regs : registers),
  biv_spec defs loop biv -> signed_step biv = Some step_size ->
  In updated biv.(update) -> value_coherent regs updated ->
  exists (counter : Z),
    regs (register_of_value (param loop.(header) biv.(param_index)))
      = Some counter
    /\ regs (register_of_value updated)
         = Some (wrap64 (counter + to_Z step_size)).
Proof.
  intros defs loop biv step_size updated regs Hspec Hstep Hin Hcoherent.
  destruct Hspec as [_ [_ [Hupdates _]]].
  destruct (Hupdates updated Hin)
    as [step' [sign' [Hclass [Hsame Hsign]]]].
  unfold signed_step in Hstep.
  destruct biv.(step) as [constant | variable] eqn:Hbiv_step;
    [ | discriminate].
  destruct step' as [constant' | variable']; cbn [step_same] in Hsame;
    [ | discriminate].
  apply eqb_int in Hsame. subst constant'.
  destruct (classify_update_const defs loop _ _ _ _ Hclass)
    as [id [index [self [Hself Hshape]]]].
  unfold is_param in Hself. apply value_eqb_spec in Hself. subst self.
  destruct biv.(sign) eqn:Hbiv_sign.
  - injection Hstep as <-.
    destruct sign'; cbn [sign_same] in Hsign; [ | discriminate].
    destruct Hshape as [[_ Hshape] | [Hbad _]]; [ | discriminate].
    subst updated.
    destruct Hcoherent as [values [result [Hread [Heval Hvalue]]]].
    cbn [read_values] in Hread.
    destruct (regs (register_of_value (param loop.(header) biv.(param_index))))
      as [counter |] eqn:Hcounter; [ | discriminate].
    injection Hread as <-. cbn [eval_operation] in Heval.
    injection Heval as <-. exists counter. split; [reflexivity |].
    exact Hvalue.
  - destruct (constant =? min_int)%sint63 eqn:Hmin; [discriminate |].
    injection Hstep as <-.
    destruct sign'; cbn [sign_same] in Hsign; [discriminate |].
    destruct Hshape as [[Hbad _] | [_ Hshape]]; [discriminate |].
    subst updated.
    destruct Hcoherent as [values [result [Hread [Heval Hvalue]]]].
    cbn [read_values] in Hread.
    destruct (regs (register_of_value (param loop.(header) biv.(param_index))))
      as [counter |] eqn:Hcounter; [ | discriminate].
    injection Hread as <-. cbn [eval_operation] in Heval.
    injection Heval as <-. exists counter. split; [reflexivity |].
    rewrite Sint63.to_Z_opp by (apply eqb_int_false; exact Hmin).
    replace (counter + - to_Z constant) with (counter - to_Z constant) by ring.
    exact Hvalue.
Qed.

(* Observing an accepted counter operand determines the header parameter
   and whether the comparison sees it before or after the update. *)
Lemma biv_operand_observed : forall (defs : op_def) (loop : natural_loop)
    (biv : biv) (step_size : int) (counter_ref : value) (regs : registers)
    (observed : Z),
  biv_spec defs loop biv -> signed_step biv = Some step_size ->
  is_param loop.(header) biv.(param_index) counter_ref
    || existsb (value_eqb counter_ref) biv.(update) = true ->
  value_coherent regs counter_ref ->
  regs (register_of_value counter_ref) = Some observed ->
  exists (counter : Z),
    regs (register_of_value (param loop.(header) biv.(param_index)))
      = Some counter
    /\ observed = tested_counter loop biv counter_ref step_size counter.
Proof.
  intros defs loop biv step_size counter_ref regs observed Hspec Hstep
    Haccepted Hcoherent Hread.
  unfold tested_counter.
  destruct (is_param loop.(header) biv.(param_index) counter_ref) eqn:Hself.
  - unfold is_param in Hself. apply value_eqb_spec in Hself. subst counter_ref.
    exists observed. auto.
  - cbn in Haccepted. apply existsb_exists in Haccepted.
    destruct Haccepted as [updated [Hin Heq]].
    apply value_eqb_spec in Heq. subst counter_ref.
    destruct (biv_update_observed _ _ _ _ _ _ Hspec Hstep Hin Hcoherent)
      as [counter [Hcounter Hupdated]].
    rewrite Hread in Hupdated. injection Hupdated as ->.
    exists counter. auto.
Qed.

(* The comparison recognizer supplies an actual counter operand and the
   instruction shape, not a hypothesis about the values it computes. *)
Lemma extract_comparison_shape : forall (is_counter is_bound : value -> bool)
    (condition : value) (cmp : integer_comparison) (iv_is_left : bool)
    (bnd : bound),
  extract_comparison is_counter is_bound condition
    = Some (cmp, iv_is_left, bnd) ->
  exists (counter_ref : value), is_counter counter_ref = true
    /\ (match bnd with Const_bound _ => True
        | Value_bound bound_ref => is_bound bound_ref = true end)
    /\ comparison_shape condition cmp iv_is_left counter_ref bnd.
Proof.
  intros is_counter is_bound condition cmp iv_is_left bnd Hextract.
  destruct (extract_comparison_spec _ _ _ _ _ _ Hextract)
    as [id [index Hcases]].
  destruct Hcases as [[counter [constant [-> [Hcounter [-> ->]]]]] |
    [[counter [bound_ref [-> [Hcounter [Hbound [-> ->]]]]]] |
     [bound_ref [counter [-> [Hcounter [Hbound [-> ->]]]]]]]].
  - exists counter. split; [exact Hcounter |]. split; [exact I |].
    exists id, index. auto.
  - exists counter. split; [exact Hcounter |]. split; [exact Hbound |].
    exists id, index. reflexivity.
  - exists counter. split; [exact Hcounter |]. split; [exact Hbound |].
    exists id, index. reflexivity.
Qed.

(* Operands of the actual comparison are available at every point where
   its result is available. This includes an update tested by the header. *)
Lemma comparison_operands_available : forall (blocks : list block)
    (entry : block) (position : SsaDominance.point) (condition : value)
    (cmp : integer_comparison) (iv_is_left : bool) (counter_ref : value)
    (bnd : bound),
  well_formed_ssa blocks entry ->
  available_value blocks entry position condition ->
  comparison_shape condition cmp iv_is_left counter_ref bnd ->
  available_value blocks entry position counter_ref
    /\ match bnd with Const_bound _ => True
       | Value_bound bound_ref =>
         available_value blocks entry position bound_ref end.
Proof.
  intros blocks entry position condition cmp iv_is_left counter_ref bnd
    Hwf Havailable [id [index Hshape]].
  destruct bnd as [bound_ref | constant].
  - subst condition. destruct iv_is_left; split;
      eapply operand_available; try eassumption; cbn; auto.
  - destruct Hshape as [-> ->]. split; [ | exact I].
    eapply operand_available; try eassumption; cbn; auto.
Qed.

(* Evaluating the comparison reads these two operand values and produces
   exactly its 0/1 result, for either orientation and either kind of bound. *)
Lemma comparison_values_observed : forall (condition : value)
    (cmp : integer_comparison) (iv_is_left : bool) (counter_ref : value)
    (bnd : bound) (regs : registers),
  comparison_shape condition cmp iv_is_left counter_ref bnd ->
  value_coherent regs condition ->
  exists (counter_word bound_word : Z),
    regs (register_of_value counter_ref) = Some counter_word
    /\ read_bound regs bnd = Some bound_word
    /\ regs (register_of_value condition) = Some (bool_to_Z
         (if iv_is_left then IntegerComparison.eval cmp counter_word bound_word
          else IntegerComparison.eval cmp bound_word counter_word)).
Proof.
  intros condition cmp iv_is_left counter_ref bnd regs [id [index Hshape]]
    Hcoherent.
  destruct bnd as [bound_ref | constant].
  - subst condition. destruct iv_is_left;
      destruct Hcoherent as [values [result [Hread [Heval Hvalue]]]];
      cbn [read_values] in Hread.
    + destruct (regs (register_of_value counter_ref)) as [counter_word |]
        eqn:Hcounter; [ | discriminate].
      destruct (regs (register_of_value bound_ref)) as [bound_word |]
        eqn:Hbound; [ | discriminate].
      injection Hread as <-. cbn [eval_operation] in Heval.
      injection Heval as <-. exists counter_word, bound_word.
      split; [reflexivity |]. split.
      * unfold read_bound. exact Hbound.
      * exact Hvalue.
    + destruct (regs (register_of_value bound_ref)) as [bound_word |]
        eqn:Hbound; [ | discriminate].
      destruct (regs (register_of_value counter_ref)) as [counter_word |]
        eqn:Hcounter; [ | discriminate].
      injection Hread as <-. cbn [eval_operation] in Heval.
      injection Heval as <-. exists counter_word, bound_word.
      split; [reflexivity |]. split.
      * unfold read_bound. exact Hbound.
      * exact Hvalue.
  - destruct Hshape as [-> ->].
    destruct Hcoherent as [values [result [Hread [Heval Hvalue]]]].
    cbn [read_values] in Hread.
    destruct (regs (register_of_value counter_ref)) as [counter_word |]
      eqn:Hcounter; [ | discriminate].
    injection Hread as <-. cbn [eval_operation] in Heval.
    injection Heval as <-. exists counter_word, (to_Z constant).
    split; [reflexivity |]. split; [reflexivity | exact Hvalue].
Qed.

(* A bound that was actually read fits a machine register. *)
Lemma read_bound_bounded : forall (regs : registers) (bnd : bound) (word : Z),
  bounded_registers regs -> read_bound regs bnd = Some word -> in_int64 word.
Proof.
  intros regs [bound_ref | constant] word Hbounded Hread.
  - eapply Hbounded. exact Hread.
  - injection Hread as <-. pose proof (int_bounds constant).
    unfold in_int64, two63, two62 in *. lia.
Qed.

(* Testing the updated value shifts the same IV sequence by one step. *)
Lemma tested_counter_sequence : forall (loop : natural_loop) (biv : biv)
    (counter_ref : value) (step_size : int) (counter : Z) (iteration : nat),
  tested_counter loop biv counter_ref step_size
    (iv counter (to_Z step_size) iteration)
  = iv (tested_counter loop biv counter_ref step_size counter)
      (to_Z step_size) iteration.
Proof.
  intros loop biv counter_ref step_size counter iteration.
  unfold tested_counter. destruct (is_param _ _ _); [reflexivity |].
  rewrite <- iv_shift. reflexivity.
Qed.

Section CounterExecution.
  Variable blocks : list block.
  Variable entry : block.
  Variable defs : op_def.
  Variable loop : natural_loop.
  Variable bivs : list biv.
  Variable exit : block.
  Variable initial_regs : registers.
  Variable trace : nat -> state.

  Hypothesis edges : control_edges.
  Hypothesis well_formed : well_formed_ssa blocks entry.
  Hypothesis loop_graph : loop_graph_properties blocks entry loop.
  Hypothesis certificate : deletion_certificate defs blocks loop bivs exit.
  Hypothesis prefix : steps (enter entry initial_regs) (trace 0%nat).
  Hypothesis execution : infinite_execution trace.
  Hypothesis confined : stays_in_region loop.(body) trace.

  (* The initial instruction position follows from the executed prefix. *)
  Lemma counter_trace_position : valid_position (trace 0%nat).
  Proof.
    eapply steps_valid_position; [exact prefix | apply enter_valid_position].
  Qed.

  (* A counter accepted by the deletion certificate satisfies the BIV
     specification used by the concrete arithmetic lemmas above. *)
  Lemma counter_spec : forall (biv : biv),
    In biv bivs -> biv_spec defs loop biv.
  Proof.
    intros biv Hin. destruct certificate as [_ [_ [_ [[_ Hspecs] _]]]].
    exact (proj1 (Hspecs biv Hin)).
  Qed.

  (* Register bounds hold along the executed prefix and every later step. *)
  Lemma counter_trace_bounded : bounded_registers initial_regs ->
    forall (time : nat), bounded_registers (current_registers (trace time)).
  Proof.
    intros Hinitial time.
    destruct (execution_invariants entry initial_regs _ Hinitial prefix)
      as [Hposition Hbounded].
    exact (proj2 (infinite_execution_invariants trace execution
      Hposition Hbounded time)).
  Qed.

  (* Reaching the header test executes its body once and preserves every
     header parameter. This statement does not assume the test's result. *)
  Lemma header_terminal : forall (start : nat),
    at_entry loop.(header) (trace start) ->
    exists (test_time : nat),
      current_block (trace test_time) = loop.(header)
      /\ remaining (trace test_time) = []
      /\ forall (index : int),
           current_registers (trace test_time) (Param loop.(header) index)
           = current_registers (trace start) (Param loop.(header) index).
  Proof.
    intros start [Hblock Hbody].
    destruct (reaches_terminator trace execution start
      (length (remaining (trace start))) eq_refl) as [Hsame Hfinished].
    exists (start + length (remaining (trace start)))%nat.
    split; [rewrite Hsame; exact Hblock |]. split; [exact Hfinished |].
    intros index. apply parameters_through_body;
      [exact execution | reflexivity].
  Qed.

  (* The header test is an actual terminator operand and is therefore
     available after the header instructions have executed. *)
  Lemma header_comparison_available : forall (exit_info : exit_branch)
      (time : nat),
    find_exit_branch loop = Some exit_info ->
    current_block (trace time) = loop.(header) ->
    remaining (trace time) = [] ->
    available_value blocks entry (state_point (trace time))
      exit_info.(condition).
  Proof.
    intros exit_info time Hexit Hblock Hfinished.
    destruct (find_exit_branch_spec loop exit_info Hexit)
      as [ifnot [ifso [Hterm _]]].
    eapply terminator_operand_available with (args := [exit_info.(condition)]);
      [exact well_formed | | exact Hfinished | | left; reflexivity].
    - rewrite Hblock. exact (loop_header_in_graph _ _ _ loop_graph).
    - rewrite Hblock, Hterm. cbn [terminator_args]. left. reflexivity.
  Qed.

  (* The header's comparison observes the actual counter (or its update)
     and bound, and its result is the corresponding machine boolean. *)
  Lemma header_test_observed : forall (biv : biv) (step_size : int)
      (exit_info : exit_branch) (cmp : integer_comparison) (iv_is_left : bool)
      (counter_ref : value) (bnd : bound) (time : nat),
    In biv bivs -> signed_step biv = Some step_size ->
    find_exit_branch loop = Some exit_info ->
    comparison_shape exit_info.(condition) cmp iv_is_left counter_ref bnd ->
    is_param loop.(header) biv.(param_index) counter_ref
      || existsb (value_eqb counter_ref) biv.(update) = true ->
    current_block (trace time) = loop.(header) ->
    remaining (trace time) = [] ->
    exists (counter bound_word : Z),
      current_registers (trace time) (Param loop.(header) biv.(param_index))
        = Some counter
      /\ read_bound (current_registers (trace time)) bnd = Some bound_word
      /\ current_registers (trace time)
           (register_of_value exit_info.(condition))
           = Some (bool_to_Z
               (if iv_is_left
                then IntegerComparison.eval cmp
                  (tested_counter loop biv counter_ref step_size counter)
                  bound_word
                else IntegerComparison.eval cmp bound_word
                  (tested_counter loop biv counter_ref step_size counter))).
  Proof.
    intros biv step_size exit_info cmp iv_is_left counter_ref bnd time
      Hin Hstep Hexit Hshape Haccepted Hblock Hfinished.
    pose proof (counter_spec biv Hin) as Hspec.
    pose proof (header_comparison_available exit_info time
      Hexit Hblock Hfinished) as Havailable.
    pose proof (reachable_execution_values edges blocks entry initial_regs
      trace
      well_formed prefix execution time) as Hvalues.
    destruct (comparison_operands_available _ _ _ _ _ _ _ _ well_formed
      Havailable Hshape) as [Hcounter_available _].
    destruct (comparison_values_observed _ _ _ _ _ _ Hshape
      (Hvalues _ Havailable))
      as [observed [bound_word [Hcounter_read [Hbound Hcondition]]]].
    destruct (biv_operand_observed _ _ _ _ _ _ _ Hspec Hstep Haccepted
      (Hvalues _ Hcounter_available) Hcounter_read)
      as [counter [Hcounter Htested]].
    pose proof (biv_parameter_identity (graph_parameters _ _ well_formed)
      defs loop biv Hspec) as Hparam.
    rewrite Hparam in Hcounter. cbn [register_of_value] in Hcounter.
    exists counter, bound_word. split; [exact Hcounter |].
    split; [exact Hbound |]. rewrite Htested in Hcondition. exact Hcondition.
  Qed.

  (* Staying inside the loop forces the comparison's boolean to select
     its continuing edge. This follows from the executed Switch. *)
  Lemma header_test_continues : forall (exit_info : exit_branch)
      (time : nat) (test : bool),
    find_exit_branch loop = Some exit_info ->
    current_block (trace time) = loop.(header) ->
    remaining (trace time) = [] ->
    current_registers (trace time) (register_of_value exit_info.(condition))
      = Some (bool_to_Z test) -> test = exit_info.(continue_when_true).
  Proof.
    intros exit_info time test Hexit Hblock Hfinished Hvalue.
    destruct (find_exit_branch_spec loop exit_info Hexit)
      as [ifnot [ifso [Hterm [Hso Hnot]]]].
    assert (Htarget : current_block (trace (S time))
      = if test then ifso else ifnot).
    { eapply boolean_switch_step;
        [exact Hfinished | rewrite Hblock; exact Hterm | exact Hvalue |
          apply execution]. }
    pose proof (confined (S time)) as Hinside. rewrite Htarget in Hinside.
    destruct test.
    - rewrite Hinside in Hso. exact Hso.
    - rewrite Hinside in Hnot.
      destruct exit_info.(continue_when_true); cbn in Hnot; congruence.
  Qed.

  (* The first subsequent entry advances the counter exactly once. This
     includes branches and multiple back edges inside the loop body. *)
  Theorem counter_next_entry : forall (biv : biv) (step_size : int)
      (start : nat) (counter : Z),
    In biv bivs -> signed_step biv = Some step_size ->
    at_entry loop.(header) (trace start) ->
    current_registers (trace start) (Param loop.(header) biv.(param_index))
      = Some counter ->
    exists (next : nat), (start < next)%nat
      /\ at_entry loop.(header) (trace next)
      /\ current_registers (trace next)
           (Param loop.(header) biv.(param_index))
           = Some (wrap64 (counter + to_Z step_size)).
  Proof.
    intros biv step_size start counter Hin Hstep Hstart Hcounter.
    pose proof (counter_spec biv Hin) as Hspec.
    pose proof (graph_parameters _ _ well_formed) as Hlayout.
    pose proof (biv_parameter_identity Hlayout defs loop biv Hspec) as Hparam.
    pose proof certificate as [_ [_ [Hrevisits _]]].
    destruct (next_header_entry edges loop.(body) loop.(header) trace
      Hrevisits execution confined counter_trace_position start)
      as [back_time [Hlater [Hnext Hbetween]]].
    pose proof (execution_positions trace execution counter_trace_position)
      as Hpositions.
    assert (Hfinished : remaining (trace back_time) = []).
    { eapply step_to_entry;
        [apply Hpositions | apply execution | exact Hnext]. }
    destruct (loop_back_edge_step blocks entry defs loop bivs exit edges
      Hlayout
      loop_graph certificate _ _ Hfinished (confined back_time)
      (execution back_time) (proj1 Hnext))
      as [args [Hback [Hpred [Hgoto Hbinding]]]].
    pose proof Hspec as [_ [_ [_ [Hupdates _]]]].
    destruct (Hupdates _ Hback Hpred)
      as [arguments [updated [Harguments [Harg Hin_updated]]]].
    pose proof (goto_args_terminator _ _ _ Harguments) as Hterm.
    rewrite Hgoto in Hterm. injection Hterm as <-.
    pose proof (arg_value_nth _ _ _ Harg) as Harg_index.
    destruct (continue_argument_used (Goto loop.(header)) args
      biv.(param_index) updated Harg_index) as [uses [Huses Hused]].
    assert (Havailable : available_value blocks entry
      (state_point (trace back_time)) updated).
    { eapply terminator_operand_available;
        [exact well_formed | | exact Hfinished | | exact Hused].
      - apply (loop_body_in_graph _ _ _ loop_graph), confined.
      - rewrite Hgoto. exact Huses. }
    pose proof (reachable_execution_values edges blocks entry initial_regs
      trace
      well_formed prefix execution back_time updated Havailable) as Hcoherent.
    destruct (biv_update_observed defs loop biv step_size updated
      (current_registers (trace back_time)) Hspec Hstep Hin_updated Hcoherent)
      as [current [Hcurrent Hupdated]].
    assert (Hsame : current_registers (trace back_time)
      (Param loop.(header) biv.(param_index))
      = current_registers (trace start)
          (Param loop.(header) biv.(param_index))).
    { replace back_time with (start + (back_time - start))%nat by lia.
      eapply parameter_between_entries; [exact Hlayout | exact execution |].
      intros offset Hoffset. apply Hbetween. lia. }
    rewrite Hparam in Hcurrent. cbn [register_of_value] in Hcurrent.
    rewrite Hsame, Hcounter in Hcurrent. injection Hcurrent as <-.
    exists (S back_time). split; [lia |]. split; [exact Hnext |].
    specialize (Hbinding biv.(param_index) updated Harg_index).
    rewrite Hparam in Hbinding. cbn [register_of_value] in Hbinding.
    rewrite Hbinding. exact Hupdated.
  Qed.

  (* Every mathematical iteration number is realized by an actual header
     entry with that counter value. No global sampled valuation is needed. *)
  Theorem counter_entry_values : forall (biv : biv) (step_size : int)
      (counter : Z),
    In biv bivs -> signed_step biv = Some step_size ->
    at_entry loop.(header) (trace 0%nat) ->
    current_registers (trace 0%nat) (Param loop.(header) biv.(param_index))
      = Some counter ->
    forall (iteration : nat), exists (time : nat),
      at_entry loop.(header) (trace time)
      /\ current_registers (trace time)
           (Param loop.(header) biv.(param_index))
           = Some (iv counter (to_Z step_size) iteration).
  Proof.
    intros biv step_size counter Hin Hstep Hentry Hcounter iteration.
    induction iteration as [ | iteration IH].
    - exists 0%nat. auto.
    - destruct IH as [time [Hentry_at Hcounter_at]].
      destruct (counter_next_entry biv step_size time _ Hin Hstep
        Hentry_at Hcounter_at) as [next [_ [Hnext Hcounter_next]]].
      exists next. split; [exact Hnext | exact Hcounter_next].
  Qed.

  (* The operational counter cannot continue forever against a fixed
     bound satisfying the arithmetic termination criterion. Constancy of
     a literal bound needs no execution hypothesis; register-bound facts
     will be supplied by the entry analysis separately. *)
  Theorem counter_cannot_continue : forall (biv : biv) (step_size : int)
      (exit_info : exit_branch) (cmp : integer_comparison) (iv_is_left : bool)
      (counter_ref : value) (bnd : bound) (bound_word : Z),
    bounded_registers initial_regs -> In biv bivs ->
    signed_step biv = Some step_size ->
    find_exit_branch loop = Some exit_info ->
    comparison_shape exit_info.(condition) cmp iv_is_left counter_ref bnd ->
    is_param loop.(header) biv.(param_index) counter_ref
      || existsb (value_eqb counter_ref) biv.(update) = true ->
    at_entry loop.(header) (trace 0%nat) ->
    (forall (time : nat), current_block (trace time) = loop.(header) ->
       remaining (trace time) = [] ->
       read_bound (current_registers (trace time)) bnd = Some bound_word) ->
    (continue_terminates step_size
       (oriented_continue_comparison iv_is_left
          exit_info.(continue_when_true) cmp) = LoopComparisons.Terminates
     \/ (continue_terminates step_size
          (oriented_continue_comparison iv_is_left
             exit_info.(continue_when_true) cmp)
           = Terminates_if_bound_in_range
         /\ LoopComparisons.bound_in_range
              (to_Z step_size) bound_word = true)) ->
    False.
  Proof.
    intros biv step_size exit_info cmp iv_is_left counter_ref bnd bound_word
      Hbounded Hin Hstep Hexit Hshape Haccepted Hentry Hbound_fixed Hverdict.
    destruct (header_terminal 0%nat Hentry)
      as [first_test [Hfirst_block [Hfirst_finished Hfirst_params]]].
    destruct (header_test_observed biv step_size exit_info cmp iv_is_left
      counter_ref bnd first_test Hin Hstep Hexit Hshape Haccepted
      Hfirst_block Hfirst_finished)
      as [counter [first_bound [Hcounter [Hread_bound Hcondition]]]].
    pose proof (Hbound_fixed first_test Hfirst_block Hfirst_finished)
      as Hfixed.
    rewrite Hfixed in Hread_bound. injection Hread_bound as <-.
    rewrite Hfirst_params in Hcounter.
    assert (Hcounter_bounded : in_int64 counter).
    { eapply (counter_trace_bounded Hbounded 0%nat). exact Hcounter. }
    assert (Hbound_bounded : in_int64 bound_word).
    { eapply read_bound_bounded;
        [apply counter_trace_bounded; exact Hbounded | exact Hfixed]. }
    assert (Htested_bounded :
      in_int64 (tested_counter loop biv counter_ref step_size counter)).
    { unfold tested_counter. destruct (is_param _ _ _);
        [exact Hcounter_bounded | apply wrap64_in_range]. }
    destruct (loop_exits iv_is_left exit_info.(continue_when_true) cmp
      step_size
      (tested_counter loop biv counter_ref step_size counter) bound_word
      Htested_bounded Hbound_bounded Hverdict) as [iteration Hfails].
    destruct (counter_entry_values biv step_size counter Hin Hstep
      Hentry Hcounter iteration) as [visit [Hvisit Hcounter_at_visit]].
    destruct (header_terminal visit Hvisit)
      as [test_time [Htest_block [Htest_finished Htest_params]]].
    destruct (header_test_observed biv step_size exit_info cmp iv_is_left
      counter_ref bnd test_time Hin Hstep Hexit Hshape Haccepted
      Htest_block Htest_finished)
      as [tested [actual_bound [Htested [Hactual_bound Hactual_condition]]]].
    rewrite Htest_params, Hcounter_at_visit in Htested.
    injection Htested as <-.
    rewrite (Hbound_fixed test_time Htest_block Htest_finished)
      in Hactual_bound. injection Hactual_bound as <-.
    rewrite tested_counter_sequence in Hactual_condition.
    pose proof (header_test_continues exit_info test_time _ Hexit
      Htest_block Htest_finished Hactual_condition) as Hcontinues.
    unfold loop_continues in Hfails. cbv zeta in Hfails.
    rewrite Hcontinues in Hfails.
    destruct exit_info.(continue_when_true); discriminate.
  Qed.

  Section InvariantBound.
    Hypothesis dominance : SsaDominance.dominance_semantics entry.
    Hypothesis definitions : op_def_correct defs blocks.

    (* The bound classifier supplies one fixed value at every executed
       header test. This includes constants computed inside the header. *)
    Theorem header_bound_fixed : forall (exit_info : exit_branch)
        (cmp : integer_comparison) (iv_is_left : bool) (counter_ref : value)
        (bnd : bound),
      find_exit_branch loop = Some exit_info ->
      comparison_shape exit_info.(condition) cmp iv_is_left counter_ref bnd ->
      (match bnd with Const_bound _ => True
       | Value_bound bound_ref =>
         loop_invariant_value defs loop.(header) bound_ref
       end) ->
      at_entry loop.(header) (trace 0%nat) ->
      exists (bound_word : Z), forall (time : nat),
        current_block (trace time) = loop.(header) ->
        remaining (trace time) = [] ->
        read_bound (current_registers (trace time)) bnd = Some bound_word.
    Proof.
      intros exit_info cmp iv_is_left counter_ref [bound_ref | constant]
        Hexit Hshape Hinvariant Hentry.
      - destruct (header_terminal 0%nat Hentry)
          as [first [Hfirst_block [Hfirst_finished Hfirst_params]]].
        pose proof (header_comparison_available exit_info first
          Hexit Hfirst_block Hfirst_finished) as Hfirst.
        pose proof (reachable_execution_values edges blocks entry initial_regs
          trace well_formed prefix execution first _ Hfirst) as Hcoherent.
        destruct (comparison_values_observed _ _ _ _ _ _ Hshape Hcoherent)
          as [counter_word [bound_word [Hcounter [Hbound Hcondition]]]].
        destruct (comparison_operands_available _ _ _ _ _ _ _ _ well_formed
          Hfirst Hshape) as [_ Hbound_first].
        exists bound_word. intros time Hblock Hfinished.
        pose proof (header_comparison_available exit_info time
          Hexit Hblock Hfinished) as Havailable.
        destruct (comparison_operands_available _ _ _ _ _ _ _ _ well_formed
          Havailable Hshape) as [_ Hbound_now].
        assert (Hsame : current_registers (trace time)
          (register_of_value bound_ref)
          = current_registers (trace first) (register_of_value bound_ref)).
        { eapply loop_invariant_value_same; eassumption. }
        unfold read_bound in *. rewrite Hsame. exact Hbound.
      - exists (to_Z constant). intros time Hblock Hfinished. reflexivity.
    Qed.

    (* Rules requiring no bound-range facts are now operationally sound
       for register bounds as well as literals. All bound constancy and
       counter-run premises have been discharged from execution. *)
    Theorem unconditional_counter_cannot_continue : forall (biv : biv)
        (step_size : int) (exit_info : exit_branch) (cmp : integer_comparison)
        (iv_is_left : bool) (counter_ref : value) (bnd : bound),
      bounded_registers initial_regs -> In biv bivs ->
      signed_step biv = Some step_size ->
      find_exit_branch loop = Some exit_info ->
      comparison_shape exit_info.(condition) cmp iv_is_left counter_ref bnd ->
      is_param loop.(header) biv.(param_index) counter_ref
        || existsb (value_eqb counter_ref) biv.(update) = true ->
      (match bnd with Const_bound _ => True
       | Value_bound bound_ref =>
         loop_invariant_value defs loop.(header) bound_ref
       end) ->
      at_entry loop.(header) (trace 0%nat) ->
      continue_terminates step_size
        (oriented_continue_comparison iv_is_left
          exit_info.(continue_when_true) cmp) = LoopComparisons.Terminates ->
      False.
    Proof.
      intros biv step_size exit_info cmp iv_is_left counter_ref bnd Hbounded
        Hin Hstep Hexit Hshape Haccepted Hinvariant Hentry Hverdict.
      destruct (header_bound_fixed exit_info cmp iv_is_left counter_ref bnd
        Hexit Hshape Hinvariant Hentry) as [bound_word Hfixed].
      eapply counter_cannot_continue with (bound_word := bound_word);
        try eassumption.
      left. exact Hverdict.
    Qed.
    (* Package the static witness without exposing per-iteration
       invariance or the internal comparison-shape lemmas to callers. *)
    Theorem unconditional_biv_cannot_continue :
      bounded_registers initial_regs ->
      at_entry loop.(header) (trace 0%nat) ->
      forall (biv : biv), In biv bivs ->
      unconditional_counter defs biv -> False.
    Proof.
      intros Hbounded Hentry biv Hin
        [exit_info [step_size [cmp [iv_is_left [bnd
          [Hexit [Hstep [Hextract Hverdict]]]]]]]].
      pose proof (counter_spec biv Hin) as Hspec.
      rewrite (proj1 Hspec) in Hexit, Hextract.
      destruct (extract_comparison_shape _ _ _ _ _ _ Hextract)
        as [counter_ref [Hcounter [Hbound Hshape]]].
      eapply unconditional_counter_cannot_continue; try eassumption.
      destruct bnd; [apply is_loop_invariant_spec; exact Hbound | exact I].
    Qed.
  End InvariantBound.

  (* For literal header comparisons, every remaining premise of the
     arithmetic termination argument follows from the analysis verdict.
     There are no per-iteration value or branch hypotheses. *)
  Theorem literal_test_cannot_continue : bounded_registers initial_regs ->
    at_entry loop.(header) (trace 0%nat) ->
    literal_header_test loop.(header) -> False.
  Proof.
    intros Hbounded Hentry
      [literal_id [literal_cmp [limit [args [index [targets Hliteral]]]]]].
    destruct (certificate_counter _ _ _ _ _ certificate)
      as [biv [Hin [Hspec Haccepted]]].
    destruct (biv_implies_termination_spec defs loop biv
      (proj1 Hspec) Haccepted)
      as [exit_info [step_size [cmp [iv_is_left [bnd
        [Hexit [Hstep [Hextract Hverdict]]]]]]]].
    destruct (extract_comparison_shape _ _ _ _ _ _ Hextract)
      as [counter_ref [Hcounter [_ Hshape]]].
    destruct bnd as [bound_ref | constant].
    - destruct (find_exit_branch_spec loop exit_info Hexit)
        as [ifnot [ifso [Hterm _]]].
      rewrite Hterm in Hliteral. injection Hliteral as Hcondition Htargets.
      destruct Hshape as [id [result_index Hshape]].
      rewrite Hcondition in Hshape. discriminate.
    - eapply counter_cannot_continue with
        (biv := biv) (step_size := step_size) (exit_info := exit_info)
        (cmp := cmp) (iv_is_left := iv_is_left) (counter_ref := counter_ref)
        (bnd := Const_bound constant) (bound_word := to_Z constant);
        try eassumption.
      + intros time Hblock Hfinished. reflexivity.
      + destruct Hverdict as [Hverdict | [Hverdict Hrange]].
        * left. exact Hverdict.
        * right. split; [exact Hverdict |].
          eapply constant_bound_in_range. exact Hrange.
  Qed.
End CounterExecution.

(* ======================================================================== *)
(* Public operational theorems                                              *)
(* ======================================================================== *)

(* Operational termination for the literal-bound fragment, starting at a
   reachable header entry. Graph well-formedness and the deletion
   certificate are structural premises; no abstract run record is assumed. *)
Theorem literal_loop_no_infinite_execution : control_edges ->
  forall (blocks : list block) (entry : block) (defs : op_def)
    (loop : natural_loop) (bivs : list biv) (exit : block)
    (initial_regs header_regs : registers),
  well_formed_ssa blocks entry -> loop_graph_properties blocks entry loop ->
  deletion_certificate defs blocks loop bivs exit ->
  bounded_registers initial_regs ->
  steps (enter entry initial_regs) (enter loop.(header) header_regs) ->
  literal_header_test loop.(header) ->
  no_infinite_execution_in loop.(body) (enter loop.(header) header_regs).
Proof.
  intros Hedges blocks entry defs loop bivs exit initial_regs header_regs
    Hwf Hgraph Hcertificate Hbounded Hprefix Hliteral trace Hstart
    Htrace Hregion.
  eapply literal_test_cannot_continue with
    (blocks := blocks) (entry := entry) (defs := defs) (loop := loop)
    (bivs := bivs) (exit := exit) (initial_regs := initial_regs)
    (trace := trace);
    try eassumption.
  - rewrite Hstart. exact Hprefix.
  - rewrite Hstart. split; reflexivity.
Qed.

(* The corresponding operational theorem for register or literal bounds
   when the selected arithmetic rule needs no range premise. *)
Theorem unconditional_loop_no_infinite_execution : control_edges ->
  forall (blocks : list block) (entry : block) (defs : op_def)
    (loop : natural_loop) (bivs : list biv) (exit : block)
    (initial_regs header_regs : registers),
  well_formed_ssa blocks entry -> loop_graph_properties blocks entry loop ->
  SsaDominance.dominance_semantics entry -> op_def_correct defs blocks ->
  deletion_certificate defs blocks loop bivs exit ->
  bounded_registers initial_regs ->
  steps (enter entry initial_regs) (enter loop.(header) header_regs) ->
  (exists (biv : biv), In biv bivs /\ unconditional_counter defs biv) ->
  no_infinite_execution_in loop.(body) (enter loop.(header) header_regs).
Proof.
  intros Hedges blocks entry defs loop bivs exit initial_regs header_regs
    Hwf Hgraph Hdominance Hdefs Hcertificate Hbounded Hprefix
    [biv [Hin Hcounter]]
    trace Hstart Htrace Hregion.
  eapply unconditional_biv_cannot_continue with
    (blocks := blocks) (entry := entry) (defs := defs) (loop := loop)
    (bivs := bivs) (exit := exit) (initial_regs := initial_regs)
    (trace := trace);
    try eassumption.
  - rewrite Hstart. exact Hprefix.
  - rewrite Hstart. split; reflexivity.
Qed.

Section GraphTermination.
  Variable blocks : list block.
  Variable entry : block.
  Hypothesis predecessors_closed : forall (b pred : block),
    In b blocks -> In pred (predecessors b) -> In pred blocks.
  Hypothesis successors_closed : forall (b succ : block),
    In b blocks -> In succ (all_successors b) -> In succ blocks.
  Hypothesis dominance : SsaDominance.dominance_semantics entry.
  Hypothesis dominance_complete : forall (dominator target : block),
    In dominator blocks -> In target blocks ->
    (forall (path : list block), SsaDominance.path entry path target ->
       In dominator path) -> dominator --dom--> target.

  (* Compose the extracted decision, graph discovery and operational
     counter proof. The loop in the conclusion is the actual analyzed
     loop, not an arbitrary region chosen after seeing the execution. *)
  Theorem find_deletions_literal_no_infinite_execution : control_edges ->
    forall (defs : op_def) (header exit : block)
      (initial_regs header_regs : registers),
    well_formed_ssa blocks entry ->
    In (header, exit) (find_deletions defs blocks) ->
    bounded_registers initial_regs ->
    steps (enter entry initial_regs) (enter header header_regs) ->
    literal_header_test header ->
    exists (loop : natural_loop) (bivs : list biv),
      In (loop, bivs) (InductionVar.analyze defs blocks)
      /\ header = loop.(NaturalLoop.header)
      /\ no_infinite_execution_in loop.(body) (enter header header_regs).
  Proof.
    intros Hedges defs header exit initial_regs header_regs Hwf Hin Hbounded
      Hprefix Hliteral.
    destruct (find_deletions_graph_properties blocks entry predecessors_closed
      successors_closed dominance dominance_complete defs header exit Hin)
      as [loop [bivs [Hloop [Hheader [Hcertificate Hgraph]]]]].
    exists loop, bivs. split; [exact Hloop |]. split; [exact Hheader |].
    subst header. eapply literal_loop_no_infinite_execution; eassumption.
  Qed.
  (* The static coverage condition is checked on the actual analyzed BIV
     list. Register-bound constancy is a conclusion of execution, not a
     premise the caller must establish for every iteration. *)
  Theorem find_deletions_unconditional_no_infinite_execution : control_edges ->
    forall (defs : op_def) (header exit : block)
      (initial_regs header_regs : registers),
    well_formed_ssa blocks entry -> op_def_correct defs blocks ->
    In (header, exit) (find_deletions defs blocks) ->
    bounded_registers initial_regs ->
    steps (enter entry initial_regs) (enter header header_regs) ->
    exists (loop : natural_loop) (bivs : list biv),
      In (loop, bivs) (InductionVar.analyze defs blocks)
      /\ header = loop.(NaturalLoop.header)
      /\ ((exists (biv : biv),
             In biv bivs /\ unconditional_counter defs biv) ->
          no_infinite_execution_in loop.(body) (enter header header_regs)).
  Proof.
    intros Hedges defs header exit initial_regs header_regs Hwf Hdefs Hin
      Hbounded Hprefix.
    destruct (find_deletions_graph_properties blocks entry predecessors_closed
      successors_closed dominance dominance_complete defs header exit Hin)
      as [loop [bivs [Hloop [Hheader [Hcertificate Hgraph]]]]].
    exists loop, bivs. split; [exact Hloop |]. split; [exact Hheader |].
    intros Hcounter. subst header.
    eapply unconditional_loop_no_infinite_execution; eassumption.
  Qed.
End GraphTermination.
