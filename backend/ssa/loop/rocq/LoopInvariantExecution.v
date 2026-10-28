(* Operational meaning of loop-invariant values.

   Strict dominators are outside a reachable natural-loop body, so their
   registers are not rewritten while execution stays in that body. Constant
   results have their literal value whenever available. Together these
   facts justify [loop_invariant_value] for actual available SSA values,
   without assigning invariance to fabricated expressions. *)

From Stdlib Require Import ZArith Lia Bool List.
From OxCamlStdlib Require Import OxCamlInt OxCamlInt64.
From OxCamlBackend Require Import Operation.
From OxCamlSsa Require Import SsaModel SsaGraph SsaDominance SsaSemantics
  SsaExecution.
From OxCamlLoop Require Import NaturalLoop InductionVar LoopExecution.
Import ListNotations.

Section Invariants.
  Variable blocks : list block.
  Variable entry : block.
  Variable defs : op_def.
  Variable loop : natural_loop.
  Variable initial_regs : registers.
  Variable trace : nat -> state.

  Hypothesis edges : control_edges.
  Hypothesis well_formed : well_formed_ssa blocks entry.
  Hypothesis loop_graph : loop_graph_properties blocks entry loop.
  Hypothesis dominance : dominance_semantics entry.
  Hypothesis definitions : op_def_correct defs blocks.
  Hypothesis prefix : steps (enter entry initial_regs) (trace 0%nat).
  Hypothesis execution : infinite_execution trace.
  Hypothesis confined : stays_in_region loop.(body) trace.
  Hypothesis starts_at_header : at_entry loop.(header) (trace 0%nat).

  (* Header reachability follows from the actual prefix, so antisymmetry
     of dominance cannot be used vacuously on unreachable blocks. *)
  Lemma invariant_header_reachable :
    point_reachable entry (entry_point loop.(header)).
  Proof.
    assert (Hreachable : point_reachable entry (state_point (trace 0%nat))).
    { eapply steps_point_reachable;
        [exact edges | exact prefix | apply enter_valid_position |].
      exists [entry_point entry]. constructor. }
    destruct starts_at_header as [Hblock Hremaining].
    unfold state_point in Hreachable. rewrite Hblock, Hremaining in Hreachable.
    exact Hreachable.
  Qed.

  (* A strict dominator of the header cannot also lie in its body. *)
  Lemma strict_dominator_outside : forall (dominator : block),
    dominator --dom--> loop.(header) -> dominator <> loop.(header) ->
    set_mem dominator loop.(body) = false.
  Proof.
    intros dominator Hdom Hstrict.
    destruct (set_mem dominator loop.(body)) eqn:Hinside; [ | reflexivity].
    assert (Hto_header : point_dominates entry (entry_point dominator)
      (entry_point loop.(header))).
    { apply point_dominance_of_block; [exact edges |].
      intros path Hpath. exact (dominates_spec dominance _ _ Hdom _ Hpath). }
    assert (Hto_body : point_dominates entry (entry_point loop.(header))
      (entry_point dominator)).
    { apply point_dominance_of_block; [exact edges |].
      exact (loop_header_dominates_body _ _ _ loop_graph dominator Hinside). }
    pose proof (point_dominance_antisymmetric entry _ _
      invariant_header_reachable Hto_header Hto_body) as Heq.
    apply (f_equal fst) in Heq. cbn in Heq. contradiction.
  Qed.

  (* The defining-block table identifies every actual result register.
     If it says a strict dominator defines the register, the body cannot
     contain another instruction that rewrites that same register. *)
  Lemma invariant_result_outside : forall (id : instr_id) (index : int)
      (defining_block : block),
    op_def_find defs id = Some defining_block ->
    defining_block --dom--> loop.(header) ->
    defining_block <> loop.(header) ->
    ~ defined_in_region loop.(body) (Result id index).
  Proof.
    intros id index defining_block Hlookup Hdom Hstrict
      [body_block [op [args [results [Hinside Hdefinition]]]]].
    pose proof (definitions body_block id op args results
      (loop_body_in_graph _ _ _ loop_graph body_block Hinside) Hdefinition)
      as Hactual.
    rewrite Hlookup in Hactual. injection Hactual as <-.
    rewrite (strict_dominator_outside defining_block Hdom Hstrict) in Hinside.
    discriminate.
  Qed.

  (* An outside register has the same contents at any two times in this
     confined execution, whether or not it is read at either time. *)
  Lemma invariant_register_same : forall (reg : register) (first second : nat),
    ~ defined_in_region loop.(body) reg ->
    current_registers (trace second) reg = current_registers (trace first) reg.
  Proof.
    intros reg first second Houtside.
    assert (Hposition : valid_position (trace 0%nat)).
    { eapply steps_valid_position;
        [exact prefix | apply enter_valid_position]. }
    pose proof (region_register_constant (graph_parameters _ _ well_formed)
      loop.(body) trace reg execution confined Hposition Houtside) as Hfixed.
    rewrite (Hfixed first), (Hfixed second). reflexivity.
  Qed.

  (* The syntactic invariant classifier is sound for available actual
     values. Availability is essential: constants need not have executed
     at arbitrary states, and fabricated results are not definitions. *)
  Theorem loop_invariant_value_same : forall (v : value) (first second : nat),
    loop_invariant_value defs loop.(header) v ->
    available_value blocks entry (state_point (trace first)) v ->
    available_value blocks entry (state_point (trace second)) v ->
    current_registers (trace second) (register_of_value v)
      = current_registers (trace first) (register_of_value v).
  Proof.
    intros [id op args index | b index] first second Hinvariant Hfirst Hsecond.
    - destruct op; cbn [loop_invariant_value] in Hinvariant;
        try solve
          [lazymatch type of Hinvariant with ex _ => idtac end;
           destruct Hinvariant as [defining_block [Hlookup [Hdom Hstrict]]];
           apply invariant_register_same;
           eapply invariant_result_outside; eassumption].
      all: pose proof (reachable_execution_values edges blocks entry
        initial_regs trace well_formed prefix execution first _ Hfirst)
          as Hcoherent_first;
        destruct Hcoherent_first as [values_first [result_first
          [Hread_first [Heval_first Hvalue_first]]]];
        cbn [eval_operation] in Heval_first; try discriminate.
      destruct values_first; [ | discriminate]. injection Heval_first as <-.
      pose proof (reachable_execution_values edges blocks entry initial_regs
        trace well_formed prefix execution second _ Hsecond)
        as Hcoherent_second.
      destruct Hcoherent_second
        as [values_second [result_second
          [Hread_second [Heval_second Hvalue_second]]]].
      destruct values_second; cbn [eval_operation] in Heval_second;
        [ | discriminate].
      injection Heval_second as <-. cbn [register_of_value].
      rewrite Hvalue_first, Hvalue_second. reflexivity.
    - destruct Hinvariant as [Hdom Hstrict]. apply invariant_register_same.
      change (~ (set_mem b loop.(body) = true)).
      rewrite (strict_dominator_outside b Hdom Hstrict).
      discriminate.
  Qed.
End Invariants.
