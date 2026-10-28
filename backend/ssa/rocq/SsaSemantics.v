(* Execution of the integer/control-flow fragment used by empty loops.

   Review [supported_operation], [eval_operation], [execute_instruction]
   and [step]. The whitelist, including operand and result arities, is
   extracted; the execution semantics and its proofs are not. The exact
   evaluator also covers immediate shifts and or, for bounds computed
   outside loops; this does not widen the loop whitelist. Other operations
   have no rule here. SsaContext.v handles their observations in unchanged
   prefixes without interpreting memory effects as no-ops.

   Registers are identified by instruction/result or block/parameter, not
   by a freely constructed expression. An operand reads its register; only
   executing an instruction evaluates its operation. [step] executes one
   instruction or terminator, and [return_state] distinguishes a return
   from a stuck state. SsaExecution.v derives available-value equations
   from these steps and structural SSA well-formedness. SsaProgress.v
   derives operand definedness and progress. LoopEligibility.v proves
   semantic loop eligibility; the graph rewriter is not modelled. *)

From Stdlib Require Import ZArith Lia Bool List.
From OxCamlStdlib Require Import OxCamlOption OxCamlInt OxCamlInt64
  OxCamlList.
From OxCamlBackend Require Import IntegerComparison Operation.
From OxCamlSsa Require Import SsaModel SsaGraph.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: the supported fragment                                           *)
(* ======================================================================== *)

(* Constants, counter increments/decrements and integer comparisons only.
   Match the operand list as well as the opcode: a malformed instruction
   must not receive a totality guarantee. *)
Definition supported_operation {A : Type} (op : operation) (args : list A)
    : bool :=
  match op, args with
  | Const_int _, []
  | Intop (Iadd | Isub | Icomp _), [_; _]
  | Intop_imm (Iadd | Isub | Icomp _) _, [_] => true
  | _, _ => false
  end.

(* Every supported instruction defines exactly one machine-word result. *)
Definition supported_instruction (insn : instr) : bool :=
  match insn with
  | Op _ op args results =>
    (results =? one)%sint63 && supported_operation op args
  | Push_trap | Pop_trap => false
  end.

(* The supported control flow is Goto and Switch, as for the original
   effect check, but the instruction whitelist is deliberately narrower. *)
Definition supported_block (b : block) : bool :=
  forallb supported_instruction (block_body b)
  && terminator_pure_control (terminator b).

(* ======================================================================== *)
(* Part 2: execution                                                       *)
(* ======================================================================== *)

Local Open Scope Z_scope.

Inductive register : Type :=
  | Result (id : instr_id) (index : int)
  | Param (b : block) (index : int).

Definition register_of_value (v : value) : register :=
  match v with
  | Res id _ _ i => Result id i
  | Block_param b i => Param b i
  end.

Definition register_eqb (r s : register) : bool :=
  match r, s with
  | Result id i, Result id' i' =>
    instr_id_eqb id id' && (i =? i')%sint63
  | Param b i, Param b' i' => block_eqb b b' && (i =? i')%sint63
  | _, _ => false
  end.

(* Unbound registers have no value. There are no arbitrary defaults for
   instructions that have not executed. *)
Definition registers : Type := register -> option Z.

Definition write_register (rs : registers) (r : register) (z : option Z)
    : registers :=
  fun s => if register_eqb s r then z else rs s.

Fixpoint read_values (rs : registers) (args : list value)
    : option (list Z) :=
  match args with
  | [] => Some []
  | v :: args =>
    let* z := rs (register_of_value v) in
    let* zs := read_values rs args in Some (z :: zs)
  end.

Definition comparison_value (cmp : integer_comparison) (x y : Z) : Z :=
  if IntegerComparison.eval cmp x y then 1 else 0.

(* Operations for which the observation semantics has an exact integer
   equation. This is broader than the loop whitelist: shifts and bitwise
   or may compute bounds before entering an otherwise empty loop. *)
Definition modeled_operation {A : Type} (op : operation) (args : list A)
    : bool :=
  match op, args with
  | Const_int _, _
  | Intop (Iadd | Isub | Icomp _), [_; _]
  | Intop_imm (Iadd | Isub | Icomp _ | Ior) _, [_] => true
  | Intop_imm (Ilsl | Iasr | Ilsr) bits, [_] =>
    Z.leb 0 (to_Z bits) && Z.leb (to_Z bits) 63
  | _, _ => false
  end.

(* Operations compute on values read from the current environment. These
   clauses, rather than equations imposed on every SSA expression, define
   their semantics. Arithmetic wraps at 64 bits. *)
Definition eval_operation (op : operation) (args : list Z) : option Z :=
  match op, args with
  | Const_int n, _ => Some (Int64.to_Z (Int64.of_nativeint n))
  | Intop Iadd, [x; y] => Some (wrap64 (x + y))
  | Intop Isub, [x; y] => Some (wrap64 (x - y))
  | Intop (Icomp cmp), [x; y] => Some (comparison_value cmp x y)
  | Intop_imm Iadd k, [x] => Some (wrap64 (x + to_Z k))
  | Intop_imm Isub k, [x] => Some (wrap64 (x - to_Z k))
  | Intop_imm (Icomp cmp) k, [x] =>
    Some (comparison_value cmp x (to_Z k))
  | Intop_imm Ilsl bits, [x] =>
    if Z.leb 0 (to_Z bits) && Z.leb (to_Z bits) 63
    then Some (wrap64 (x * 2 ^ to_Z bits)) else None
  | Intop_imm Iasr bits, [x] =>
    if Z.leb 0 (to_Z bits) && Z.leb (to_Z bits) 63
    then Some (wrap64 (x / 2 ^ to_Z bits)) else None
  | Intop_imm Ilsr bits, [x] =>
    if Z.leb 0 (to_Z bits) && Z.leb (to_Z bits) 63
    then Some (wrap64 (unsigned64 x / 2 ^ to_Z bits)) else None
  | Intop_imm Ior mask, [x] => Some (wrap64 (Z.lor x (to_Z mask)))
  | _, _ => None
  end.

Definition execute_instruction (rs : registers) (insn : instr)
    : option registers :=
  match insn with
  | Op id op args results =>
    if (results =? one)%sint63 then
      let* zs := read_values rs args in
      let* z := eval_operation op zs in
      Some (write_register rs (Result id zero) (Some z))
    else None
  | Push_trap | Pop_trap => None
  end.

(* Read every Goto argument before binding any parameters. An omitted
   argument leaves its parameter unbound, rather than preserving a value
   from an earlier visit. *)
Fixpoint read_arguments (rs : registers) (args : list Terminator.arg)
    : option (list (option Z)) :=
  match args with
  | [] => Some []
  | Terminator.Arg v :: args =>
    let* z := rs (register_of_value v) in
    let* zs := read_arguments rs args in Some (Some z :: zs)
  | Terminator.Omitted_since_unused :: args =>
    let* zs := read_arguments rs args in Some (None :: zs)
  end.

Fixpoint bind_parameters (ps : list value) (zs : list (option Z))
    (rs : registers) : option registers :=
  match ps, zs with
  | [], [] => Some rs
  | p :: ps, z :: zs =>
    bind_parameters ps zs (write_register rs (register_of_value p) z)
  | _, _ => None
  end.

Record state : Type :=
  { current_block : block;
    remaining : list instr;
    current_registers : registers }.

Definition enter (b : block) (rs : registers) : state :=
  {| current_block := b;
     remaining := block_body b;
     current_registers := rs |}.

Definition at_entry (b : block) (s : state) : Prop :=
  current_block s = b /\ remaining s = block_body b.

(* The length test avoids needing equality on opaque operation payloads.
   At a valid instruction position, a full-length suffix is the full body. *)
Definition entry_test (b : block) (s : state) : bool :=
  block_eqb (current_block s) b
  && Nat.eqb (length (remaining s)) (length (block_body b)).

(* The remaining instruction list is a suffix of the current block's
   body in a reachable state. Successor selection checks nonnegativity
   before conversion to nat, so negative indices do not select target 0.
   Switch edges have no arguments and may only enter parameterless blocks. *)
Inductive step : state -> state -> Prop :=
  | Step_instruction : forall (b : block) (insn : instr)
      (rest : list instr) (rs rs' : registers),
      execute_instruction rs insn = Some rs' ->
      step {| current_block := b; remaining := insn :: rest;
              current_registers := rs |}
           {| current_block := b; remaining := rest;
              current_registers := rs' |}
  | Step_goto : forall (b target : block) (args : list Terminator.arg)
      (rs : registers) (zs : list (option Z)) (rs' : registers),
      terminator b = Terminator.Continue (Goto target) args ->
      read_arguments rs args = Some zs ->
      bind_parameters (params target) zs rs = Some rs' ->
      step {| current_block := b; remaining := [];
              current_registers := rs |} (enter target rs')
  | Step_switch : forall (b : block) (index : value)
      (targets : list block) (rs : registers) (n : Z) (target : block),
      terminator b = Terminator.Switch index targets ->
      rs (register_of_value index) = Some n ->
      0 <= n -> nth_error targets (Z.to_nat n) = Some target ->
      params target = [] ->
      step {| current_block := b; remaining := [];
              current_registers := rs |} (enter target rs).

(* Finite execution, including zero steps. Infinite executions will be
   related to the loop analysis separately; a finite stuck execution is
   not identified with a successful return. *)
Inductive steps : state -> state -> Prop :=
  | Steps_refl : forall (s : state), steps s s
  | Steps_cons : forall (s t u : state),
      step s t -> steps t u -> steps s u.

(* Execute an instruction list without taking the block's terminator.
   This is the retained header computation in the eligibility theorem. *)
Inductive executes_insns : registers -> list instr -> registers -> Prop :=
  | Insns_nil : forall (regs : registers), executes_insns regs [] regs
  | Insns_cons : forall (before middle after : registers) (insn : instr)
      (rest : list instr),
      execute_instruction before insn = Some middle ->
      executes_insns middle rest after ->
      executes_insns before (insn :: rest) after.

Definition valid_position (s : state) : Prop :=
  exists (prefix : list instr),
    block_body (current_block s) = prefix ++ remaining s.

Definition return_state (s : state) (results : list (option Z)) : Prop :=
  remaining s = []
  /\ exists (args : list Terminator.arg),
       terminator (current_block s) = Terminator.Continue Return args
       /\ read_arguments (current_registers s) args = Some results.

Definition bounded_registers (rs : registers) : Prop :=
  forall (r : register) (z : Z), rs r = Some z -> in_int64 z.

(* The parameter observers describe distinct parameters of their own
   block, and the indexed accessor agrees with the list. These are local
   compiler-data contracts, independent of execution and loop analysis. *)
Record parameter_layout : Prop :=
  { parameters_local : forall (b : block) (v : value), In v (params b) ->
      exists (index : int), v = Block_param b index;
    parameters_distinct : forall (b : block),
      NoDup (map register_of_value (params b));
    parameter_lookup : forall (b : block) (index : int) (v : value),
      nth_int (params b) index = Some v -> param b index = v;
    parameter_identity : forall (b : block) (index : int) (v : value),
      nth_int (params b) index = Some v -> v = Block_param b index }.

(* An actual result reference agrees with the instruction in the graph,
   including its operation and operands. This excludes fabricated [Res]
   expressions that merely borrow the id of another instruction. *)
Definition defined_value (blocks : list block) (v : value) : Prop :=
  match v with
  | Res id op args i =>
    exists (b : block) (results : int),
      In b blocks /\ In (Op id op args results) (block_body b)
      /\ 0 <= to_Z i < to_Z results
  | Block_param b i =>
    In b blocks /\ nth_int (params b) i = Some v
  end.

(* A structural condition, independent of executions or loop analysis.
   Instruction identities have one definition in the whole graph. *)
Definition unique_definitions (blocks : list block) : Prop :=
  forall (b b' : block) (id : instr_id) (op op' : operation)
    (args args' : list value) (results results' : int),
    In b blocks -> In b' blocks ->
    In (Op id op args results) (block_body b) ->
    In (Op id op' args' results') (block_body b') ->
    b = b' /\ op = op' /\ args = args' /\ results = results'.

(* Registers defined by instructions or parameters of a region. This is
   a structural property of the graph, not a claim about a run. *)
Definition defined_in_region (region : blockset) (reg : register) : Prop :=
  match reg with
  | Result id _ =>
    exists (b : block) (op : operation) (args : list value) (results : int),
      set_mem b region = true /\ In (Op id op args results) (block_body b)
  | Param b _ => set_mem b region = true
  end.

(* ======================================================================== *)
(* Part 3: lemmas                                                          *)
(* ======================================================================== *)

(* Finite executions compose without any intermediate-state assumption. *)
Lemma steps_trans : forall (before middle after : state),
  steps before middle -> steps middle after -> steps before after.
Proof.
  intros before middle after Hprefix.
  induction Hprefix as [s | s t u Hstep Hprefix IH]; intros Hsuffix.
  - exact Hsuffix.
  - eapply Steps_cons; [exact Hstep | apply IH; exact Hsuffix].
Qed.

(* Executing a body list is an actual finite execution ending immediately
   before its terminator. No instruction is evaluated merely by reading it. *)
Lemma executes_insns_steps : forall (b : block) (insns : list instr)
    (before after : registers),
  executes_insns before insns after ->
  steps {| current_block := b; remaining := insns;
           current_registers := before |}
        {| current_block := b; remaining := [];
           current_registers := after |}.
Proof.
  intros b insns before after Hbody. induction Hbody.
  - constructor.
  - eapply Steps_cons; [constructor; exact H | exact IHHbody].
Qed.

(* A retained instruction sequence has a unique resulting environment. *)
Lemma executes_insns_deterministic : forall (insns : list instr)
    (before after other : registers),
  executes_insns before insns after ->
  executes_insns before insns other -> after = other.
Proof.
  intros insns before after other Hbody. revert other.
  induction Hbody; intros other Hother; inversion Hother; subst.
  - reflexivity.
  - assert (middle = middle0) by congruence. subst middle0.
    apply IHHbody. assumption.
Qed.

(* The executable entry test agrees with the structural entry predicate. *)
Lemma entry_test_spec : forall (b : block) (s : state),
  valid_position s -> (entry_test b s = true <-> at_entry b s).
Proof.
  intros b s Hposition. unfold entry_test, at_entry.
  rewrite andb_true_iff, block_eqb_spec, Nat.eqb_eq.
  split; intros [Hblock Hrest]; split; [exact Hblock | | exact Hblock |].
  - destruct Hposition as [prefix Hbody]. rewrite Hblock in Hbody.
    assert (length prefix = 0)%nat.
    { rewrite Hbody, length_app in Hrest. lia. }
    apply length_zero_iff_nil in H. subst prefix. cbn in Hbody. symmetry.
    exact Hbody.
  - rewrite Hrest. reflexivity.
Qed.

(* Reaching a block entry must be a terminator transfer, not an instruction
   step: consuming one instruction cannot leave a full-length body. *)
Lemma step_to_entry : forall (b : block) (before after : state),
  valid_position before -> step before after -> at_entry b after ->
  remaining before = [].
Proof.
  intros b before after Hposition Hstep [Hblock Hremaining].
  destruct Hstep; cbn in *; try reflexivity.
  destruct Hposition as [prefix Hbody]. cbn in Hbody.
  subst b. rewrite Hremaining in Hbody.
  apply (f_equal (@length instr)) in Hbody.
  rewrite length_app in Hbody. cbn in Hbody. lia.
Qed.

(* Register equality depends only on identity, as the compiler's does. *)
Lemma register_eqb_spec : forall (lhs rhs : register),
  register_eqb lhs rhs = true <-> lhs = rhs.
Proof.
  intros [id i | b i] [id' i' | b' i']; cbn [register_eqb];
    try (split; discriminate).
  - rewrite andb_true_iff, instr_id_eqb_spec, eqb_int.
    split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
  - rewrite andb_true_iff, block_eqb_spec, eqb_int.
    split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

(* Writing a result does not modify any other register. *)
Lemma write_register_other :
  forall (regs : registers) (written other : register) (result : option Z),
  other <> written -> write_register regs written result other = regs other.
Proof.
  intros rs r s z Hneq. unfold write_register.
  destruct (register_eqb s r) eqn:E; [ | reflexivity ].
  apply register_eqb_spec in E. contradiction.
Qed.

(* The written register receives exactly the supplied value. *)
Lemma write_register_same :
  forall (regs : registers) (reg : register) (result : option Z),
  write_register regs reg result reg = result.
Proof.
  intros rs r z. unfold write_register.
  assert (register_eqb r r = true) by (apply register_eqb_spec; reflexivity).
  rewrite H. reflexivity.
Qed.

(* Reading operands preserves their number. *)
Lemma read_values_length :
  forall (regs : registers) (args : list value) (arg_values : list Z),
  read_values regs args = Some arg_values ->
  length arg_values = length args.
Proof.
  intros rs args. induction args as [ | v args IH ]; intros zs H.
  - injection H as <-. reflexivity.
  - cbn [read_values] in H.
    destruct (rs (register_of_value v)); [ | discriminate ].
    destruct (read_values rs args) eqn:E; [ | discriminate ].
    injection H as <-. cbn. f_equal. apply IH. reflexivity.
Qed.

(* Equal operand-register values give equal argument lists, without
   making any claim about other registers or unexecuted instructions. *)
Lemma read_values_ext : forall (args : list value)
    (regs_before regs_after : registers),
  (forall (arg : value), In arg args ->
    regs_after (register_of_value arg)
      = regs_before (register_of_value arg)) ->
  read_values regs_after args = read_values regs_before args.
Proof.
  intros args. induction args as [ | arg args IH ];
    intros regs_before regs_after Hagree; cbn [read_values]; [reflexivity |].
  rewrite (Hagree arg (or_introl eq_refl)).
  rewrite (IH regs_before regs_after
    (fun v Hin => Hagree v (or_intror Hin))).
  reflexivity.
Qed.

(* Every whitelisted operation is defined for every list of operands of
   its accepted arity. There are no divisions, shifts or memory accesses
   requiring further dynamic preconditions. *)
Lemma supported_operation_total : forall (A : Type) (op : operation)
    (args : list A) (arg_values : list Z),
  supported_operation op args = true -> length arg_values = length args ->
  exists (result : Z), eval_operation op arg_values = Some result.
Proof.
  intros A op args zs Hsup Hlen.
  destruct op; try discriminate;
    try (destruct op; try discriminate);
    destruct args as [ | a [ | b [ | c args ] ]]; try discriminate;
    destruct zs as [ | x [ | y [ | z zs ] ]]; try discriminate;
    cbn [eval_operation]; eexists; reflexivity.
Qed.

(* The loop whitelist is a subset of the exact observation equations. *)
Lemma supported_operation_modeled : forall (A : Type) (op : operation)
    (args : list A),
  supported_operation op args = true -> modeled_operation op args = true.
Proof.
  intros A op args Hsupported.
  destruct op; try discriminate; try (destruct op; try discriminate);
    destruct args as [ | lhs [ | rhs [ | extra rest]]];
    try discriminate; reflexivity.
Qed.

(* All supported results fit a machine register, including wraparound. *)
Lemma eval_operation_bounded :
  forall (op : operation) (arg_values : list Z) (result : Z),
  eval_operation op arg_values = Some result -> in_int64 result.
Proof.
  intros op zs z H. destruct op; try discriminate;
    try (destruct op; try discriminate);
    destruct zs as [ | x [ | y [ | a zs ] ]]; try discriminate;
    cbn [eval_operation] in H;
    try (destruct (Z.leb 0 (to_Z k) && Z.leb (to_Z k) 63);
      [ | discriminate]);
    injection H as <-;
    try apply Int64.to_Z_bounded; try apply wrap64_in_range;
    unfold comparison_value; destruct (IntegerComparison.eval _ _ _);
    unfold in_int64, two63; lia.
Qed.

(* Binding a bounded value, or unbinding an omitted parameter, preserves
   the register-width invariant. *)
Lemma write_register_bounded :
  forall (regs : registers) (reg : register) (result : option Z),
  bounded_registers regs ->
  (forall (word : Z), result = Some word -> in_int64 word) ->
  bounded_registers (write_register regs reg result).
Proof.
  intros rs r z Hrs Hz s n H. unfold write_register in H.
  destruct (register_eqb s r).
  - apply Hz. exact H.
  - eapply Hrs. exact H.
Qed.

(* Reading Goto arguments preserves the width of each supplied value. *)
Lemma read_arguments_bounded : forall (regs : registers)
    (args : list Terminator.arg) (arg_values : list (option Z)),
  bounded_registers regs -> read_arguments regs args = Some arg_values ->
  Forall (fun (result : option Z) =>
    forall (word : Z), result = Some word -> in_int64 word) arg_values.
Proof.
  intros rs args. induction args as [ | [v |] args IH ];
    intros zs Hrs Hread; cbn [read_arguments] in Hread.
  - injection Hread as <-. constructor.
  - destruct (rs (register_of_value v)) eqn:Ev; [ | discriminate ].
    destruct (read_arguments rs args) eqn:E; [ | discriminate ].
    injection Hread as <-. constructor.
    + intros n Hn. injection Hn as <-. eapply Hrs. exact Ev.
    + apply IH; [exact Hrs | reflexivity].
  - destruct (read_arguments rs args) eqn:E; [ | discriminate ].
    injection Hread as <-. constructor.
    + intros n Hn. discriminate.
    + apply IH; [exact Hrs | reflexivity].
Qed.

(* Binding parameters does not change a register outside the parameter
   list. This also applies when some parameters are omitted. *)
Lemma bind_parameters_frame : forall (parameters : list value)
    (arg_values : list (option Z)) (regs_before regs_after : registers)
    (reg : register),
  bind_parameters parameters arg_values regs_before = Some regs_after ->
  ~ In reg (map register_of_value parameters) ->
  regs_after reg = regs_before reg.
Proof.
  intros ps. induction ps as [ | p ps IH ];
    intros zs rs rs' r H Hnot; destruct zs; try discriminate.
  - injection H as <-. reflexivity.
  - cbn [bind_parameters] in H. rewrite (IH _ _ _ _ H).
    + apply write_register_other. cbn in Hnot. intuition congruence.
    + cbn in Hnot. tauto.
Qed.

(* Distinct parameters receive the precomputed argument values. The old
   environment cannot affect the assignments, even when arguments and
   parameters overlap (for example, swapping two parameters). *)
Lemma bind_parameters_values : forall (parameters : list value)
    (arg_values : list (option Z)) (regs_before regs_after : registers),
  NoDup (map register_of_value parameters) ->
  bind_parameters parameters arg_values regs_before = Some regs_after ->
  Forall2 (fun (parameter : value) (result : option Z) =>
    regs_after (register_of_value parameter) = result) parameters arg_values.
Proof.
  intros ps. induction ps as [ | p ps IH ];
    intros zs rs rs' Hdup H; destruct zs; try discriminate.
  - constructor.
  - cbn in Hdup. inversion Hdup as [ | ? ? Hnot Htail ]; subst.
    cbn [bind_parameters] in H. constructor.
    + rewrite (bind_parameters_frame _ _ _ _ _ H Hnot).
      apply write_register_same.
    + eapply IH; eassumption.
Qed.

(* Reading and then binding argument lists associates each target
   parameter with the original argument register, not an already-updated
   parameter environment. *)
Lemma read_bound_arguments : forall (args : list Terminator.arg)
    (regs_before : registers) (arg_values : list (option Z))
    (parameters : list value) (regs_after : registers),
  read_arguments regs_before args = Some arg_values ->
  Forall2 (fun (parameter : value) (result : option Z) =>
    regs_after (register_of_value parameter) = result) parameters arg_values ->
  Forall2
    (fun (arg : Terminator.arg) (parameter : value) =>
      match arg with
      | Terminator.Arg v =>
        regs_after (register_of_value parameter)
        = regs_before (register_of_value v)
      | Terminator.Omitted_since_unused =>
        regs_after (register_of_value parameter) = None
      end)
    args parameters.
Proof.
  intros args. induction args as [ | [v |] args IH ];
    intros rs zs ps rs' Hread Hbind; cbn [read_arguments] in Hread.
  - injection Hread as <-. inversion Hbind. constructor.
  - destruct (rs (register_of_value v)) eqn:Ev; [ | discriminate].
    destruct (read_arguments rs args) eqn:E; [ | discriminate].
    injection Hread as <-. inversion Hbind; subst.
    constructor; [rewrite Ev; assumption | eapply IH; eassumption].
  - destruct (read_arguments rs args) eqn:E; [ | discriminate].
    injection Hread as <-. inversion Hbind; subst.
    constructor; [assumption | eapply IH; eassumption].
Qed.

(* Parameter binding preserves register widths. *)
Lemma bind_parameters_bounded : forall (parameters : list value)
    (arg_values : list (option Z)) (regs_before regs_after : registers),
  bounded_registers regs_before ->
  Forall (fun (result : option Z) =>
    forall (word : Z), result = Some word -> in_int64 word) arg_values ->
  bind_parameters parameters arg_values regs_before = Some regs_after ->
  bounded_registers regs_after.
Proof.
  intros ps. induction ps as [ | p ps IH ];
    intros zs rs rs' Hrs Hzs H; destruct zs; try discriminate.
  - injection H as <-. exact Hrs.
  - inversion Hzs; subst. eapply IH; [ | eassumption | exact H].
    apply write_register_bounded; assumption.
Qed.

(* ======================================================================== *)
(* Part 4: theorems                                                        *)
(* ======================================================================== *)

(* Supported instructions always execute when their operands are bound.
   Their only modification is their sole result register. *)
Theorem supported_instruction_executes :
  forall (insn : instr) (regs : registers) (arg_values : list Z),
  supported_instruction insn = true ->
  read_values regs (args_of_instr insn) = Some arg_values ->
  exists (id : instr_id) (op : operation) (args : list value) (result : Z),
    insn = Op id op args one
    /\ eval_operation op arg_values = Some result
    /\ execute_instruction regs insn
       = Some (write_register regs (Result id zero) (Some result)).
Proof.
  intros [id op args results | |] rs zs Hsup Hread; try discriminate.
  apply andb_true_iff in Hsup. destruct Hsup as [Hresults Hsup].
  apply eqb_int in Hresults. subst results.
  destruct (supported_operation_total _ _ _ _ Hsup
              (read_values_length _ _ _ Hread)) as [z Hz].
  exists id, op, args, z. split; [reflexivity |]. split; [exact Hz |].
  unfold execute_instruction. rewrite eqb_refl. cbn [args_of_instr] in Hread.
  rewrite Hread, Hz. reflexivity.
Qed.

(* Every instruction step preserves the machine-width invariant; this is
   derived from execution, not assumed of an arbitrary valuation. *)
Theorem execute_instruction_bounded :
  forall (insn : instr) (regs_before regs_after : registers),
  bounded_registers regs_before ->
  execute_instruction regs_before insn = Some regs_after ->
  bounded_registers regs_after.
Proof.
  intros [id op args results | |] rs rs' Hrs H; try discriminate.
  unfold execute_instruction in H.
  destruct (results =? one)%sint63; [ | discriminate ].
  destruct (read_values rs args); [ | discriminate ].
  destruct (eval_operation op l) eqn:E; [ | discriminate ].
  injection H as <-. apply write_register_bounded; [exact Hrs |].
  intros n Hn. injection Hn as <-. eapply eval_operation_bounded. exact E.
Qed.

(* Successful execution reads the operands, evaluates the operation and
   writes its unique result; each part follows by inverting execution. *)
Theorem execute_instruction_result : forall (id : instr_id) (op : operation)
    (args : list value) (result_count : int)
    (regs_before regs_after : registers),
  execute_instruction regs_before (Op id op args result_count)
    = Some regs_after ->
  result_count = one /\
  exists (arg_values : list Z) (result : Z),
    read_values regs_before args = Some arg_values
    /\ eval_operation op arg_values = Some result
    /\ regs_after = write_register regs_before (Result id zero) (Some result).
Proof.
  intros id op args result_count regs_before regs_after Hexec.
  unfold execute_instruction in Hexec.
  destruct (result_count =? one)%sint63 eqn:E; [ | discriminate].
  apply eqb_int in E. split; [exact E |].
  destruct (read_values regs_before args) as [arg_values |] eqn:Hread;
    [ | discriminate].
  destruct (eval_operation op arg_values) as [result |] eqn:Heval;
    [ | discriminate].
  injection Hexec as <-. exists arg_values, result. auto.
Qed.

(* A successful instruction writes no other register, regardless of the
   operation or environment. *)
Theorem execute_instruction_frame :
  forall (id : instr_id) (op : operation) (args : list value)
    (result_count : int) (regs_before regs_after : registers) (reg : register),
  execute_instruction regs_before (Op id op args result_count)
    = Some regs_after ->
  reg <> Result id zero -> regs_after reg = regs_before reg.
Proof.
  intros id op args results rs rs' r H Hneq.
  unfold execute_instruction in H.
  destruct (results =? one)%sint63; [ | discriminate ].
  destruct (read_values rs args); [ | discriminate ].
  destruct (eval_operation op l); [ | discriminate ].
  injection H as <-. apply write_register_other. exact Hneq.
Qed.

(* A concrete Goto step passes the source values to the corresponding
   parameters. No recurrence or run-model hypothesis is needed. *)
Theorem goto_step_parameter : parameter_layout ->
  forall (before after : state) (target : block) (args : list Terminator.arg),
  remaining before = [] ->
  terminator (current_block before)
    = Terminator.Continue (Goto target) args ->
  step before after ->
  current_block after = target /\ remaining after = block_body target /\
  forall (index : int) (arg : value),
    nth_int args index = Some (Terminator.Arg arg) ->
    current_registers after (register_of_value (param target index))
    = current_registers before (register_of_value arg).
Proof.
  intros Hlayout s s' target args Hremaining Hterm Hstep.
  destruct Hstep as [b insn rest rs rs' Hop |
    b dest arguments rs zs rs' Hgoto Hread Hbind |
    b index targets rs n dest Hswitch Hindex Hnonneg Hnth Hparams];
    cbn in *; try discriminate.
  - rewrite Hgoto in Hterm. injection Hterm as -> ->.
    split; [reflexivity |]. split; [reflexivity |]. intros i v Harg.
    pose proof (bind_parameters_values _ _ _ _
      (parameters_distinct Hlayout target) Hbind) as Hvalues.
    pose proof (read_bound_arguments _ _ _ _ _ Hread Hvalues) as Hargs.
    destruct (Forall2_nth_int _ _ _ Hargs _ _ Harg) as [p [Hp Hvalue]].
    rewrite (parameter_lookup Hlayout target i p Hp). exact Hvalue.
  - rewrite Hswitch in Hterm. discriminate.
Qed.

(* Every operational step, including simultaneous parameter binding,
   preserves machine-word bounds. *)
Theorem step_bounded : forall (before after : state),
  bounded_registers (current_registers before) -> step before after ->
  bounded_registers (current_registers after).
Proof.
  intros s s' Hrs Hstep. destruct Hstep; cbn in *.
  - eapply execute_instruction_bounded; eassumption.
  - eapply bind_parameters_bounded; [exact Hrs | | eassumption].
    eapply read_arguments_bounded; eassumption.
  - exact Hrs.
Qed.

(* An entry state starts with the actual instructions of its block. *)
Lemma enter_valid_position : forall (b : block) (regs : registers),
  valid_position (enter b regs).
Proof. intros b rs. exists []. reflexivity. Qed.

(* Stepping never introduces instructions not in the current block. *)
Theorem step_valid_position : forall (before after : state),
  valid_position before -> step before after -> valid_position after.
Proof.
  intros s s' Hpos Hstep. destruct Hstep.
  - destruct Hpos as [prefix Hprefix].
    exists (prefix ++ [insn]). cbn in *.
    rewrite Hprefix, <- app_assoc. reflexivity.
  - apply enter_valid_position.
  - apply enter_valid_position.
Qed.

(* Finite execution preserves a valid instruction position. *)
Lemma steps_valid_position : forall (before after : state),
  steps before after -> valid_position before -> valid_position after.
Proof.
  intros before after Hsteps. induction Hsteps; intros Hposition.
  - exact Hposition.
  - apply IHHsteps. eapply step_valid_position; eassumption.
Qed.

(* Every state reached from a block entry has an actual instruction
   position and bounded registers, if the initial registers were bounded. *)
Theorem execution_invariants :
  forall (entry : block) (initial_regs : registers) (reached : state),
  bounded_registers initial_regs -> steps (enter entry initial_regs) reached ->
  valid_position reached /\ bounded_registers (current_registers reached).
Proof.
  assert (forall s t, steps s t ->
    valid_position s -> bounded_registers (current_registers s) ->
    valid_position t /\ bounded_registers (current_registers t)) as Hsteps.
  { intros s t H. induction H; intros Hpos Hbound.
    - auto.
    - apply IHsteps.
      + eapply step_valid_position; eassumption.
      + eapply step_bounded; eassumption. }
  intros b rs s Hbound Hrun. eapply Hsteps; [exact Hrun | | exact Hbound].
  apply enter_valid_position.
Qed.

(* Executing an instruction never changes any block parameter. *)
Lemma instruction_parameter_frame : forall (b : block) (index : int)
    (before after : state),
  step before after -> remaining before <> [] ->
  current_registers after (Param b index)
    = current_registers before (Param b index).
Proof.
  intros b index before after Hstep Hnonempty.
  destruct Hstep; cbn in *; try contradiction.
  destruct insn as [id op args results | |]; try discriminate.
  eapply execute_instruction_frame; [eassumption | discriminate].
Qed.

(* The true/false targets of a two-way Switch are selected by 1 and 0,
   respectively, as computed by an integer comparison. *)
Lemma boolean_switch_step : forall (before after : state) (index : value)
    (ifnot ifso : block) (test : bool),
  remaining before = [] ->
  terminator (current_block before) = Terminator.Switch index [ifnot; ifso] ->
  current_registers before (register_of_value index)
    = Some (if test then 1 else 0) ->
  step before after -> current_block after = if test then ifso else ifnot.
Proof.
  intros before after index ifnot ifso test Hremaining Hterm Hvalue Hstep.
  destruct Hstep as [source insn rest regs regs' Hexec |
    source target args regs values regs' Hgoto Hread Hbind |
    source condition targets regs word target Hswitch Hindex Hpos Hnth
      Hparams];
    cbn in *; try discriminate.
  - rewrite Hgoto in Hterm. discriminate.
  - rewrite Hswitch in Hterm. injection Hterm as -> ->.
    rewrite Hvalue in Hindex. injection Hindex as <-.
    destruct test; cbn in Hnth; injection Hnth as <-; reflexivity.
Qed.

(* Parameters do not change unless a step arrives at their block entry.
   Instructions in the header itself therefore preserve its parameters. *)
Theorem step_parameter_frame_unless_entry : parameter_layout ->
  forall (b : block) (index : int) (before after : state),
  step before after -> ~ at_entry b after ->
  current_registers after (Param b index)
    = current_registers before (Param b index).
Proof.
  intros Hlayout b index before after Hstep Hnot.
  destruct Hstep as [source insn rest regs regs' Hexec |
    source target args regs values regs' Hterm Hread Hbind |
    source condition targets regs word target Hterm Hvalue Hpos Hnth Hparams];
    cbn in *.
  - destruct insn as [id op args results | |]; try discriminate.
    eapply execute_instruction_frame; [exact Hexec | discriminate].
  - eapply bind_parameters_frame; [exact Hbind |].
    intros Hin. apply in_map_iff in Hin.
    destruct Hin as [parameter [Hreg Hin]].
    destruct (parameters_local Hlayout target parameter Hin)
      as [param_index ->]. cbn in Hreg. inversion Hreg; subst.
    apply Hnot. split; reflexivity.
  - reflexivity.
Qed.

(* Parameters of a block are unchanged by a step that does not enter
   that block. Instruction results and block parameters are distinct
   register identities, including when their numeric indices coincide. *)
Theorem step_parameter_frame : parameter_layout ->
  forall (b : block) (index : int) (before after : state),
  step before after -> current_block after <> b ->
  current_registers after (Param b index)
    = current_registers before (Param b index).
Proof.
  intros Hlayout b index before after Hstep Hnot.
  destruct Hstep as [source insn rest regs regs' Hexec |
    source target args regs values regs' Hterm Hread Hbind |
    source condition targets regs value target Hterm Hvalue Hpos Hnth Hparams];
    cbn in *.
  - destruct insn as [id op args results | |]; try discriminate.
    eapply execute_instruction_frame; [exact Hexec | discriminate].
  - eapply bind_parameters_frame; [exact Hbind |].
    intros Hin. apply in_map_iff in Hin.
    destruct Hin as [parameter [Hreg Hin]].
    destruct (parameters_local Hlayout target parameter Hin)
      as [param_index ->]. cbn in Hreg. inversion Hreg. contradiction.
  - reflexivity.
Qed.

(* A control transfer into a parameterless block changes no register.
   This applies to the final exiting edge, not just to internal steps. *)
Theorem step_to_parameterless_frame : forall (before after : state),
  remaining before = [] -> params (current_block after) = [] ->
  step before after -> current_registers after = current_registers before.
Proof.
  intros before after Hfinished Hparams Hstep. destruct Hstep;
    cbn in *; try discriminate; [ | reflexivity].
  rewrite Hparams in H1. destruct zs; cbn in H1; [ | discriminate].
  injection H1 as <-. reflexivity.
Qed.

(* A step within a region cannot change a register defined outside it.
   Validity of the instruction position is proved for executions from
   block entries, rather than assumed for arbitrary instruction lists. *)
Theorem step_region_frame : parameter_layout ->
  forall (region : blockset) (reg : register) (before after : state),
  valid_position before ->
  set_mem (current_block before) region = true ->
  set_mem (current_block after) region = true ->
  ~ defined_in_region region reg -> step before after ->
  current_registers after reg = current_registers before reg.
Proof.
  intros Hlayout region reg before after Hposition Hbefore Hafter Houtside
    Hstep.
  destruct reg as [id index | b index].
  - destruct Hstep as [source insn rest regs regs' Hexec |
      source target args regs values regs' Hterm Hread Hbind |
      source condition targets regs value target Hterm Hvalue Hpos Hnth
        Hparams];
      cbn in *.
    + destruct insn as [defined_id op args results | |]; try discriminate.
      eapply execute_instruction_frame; [exact Hexec |].
      intros Heq. inversion Heq; subst.
      apply Houtside. exists source, op, args, results.
      split; [exact Hbefore |].
      destruct Hposition as [prefix Hprefix]. cbn in Hprefix.
      rewrite Hprefix.
      apply in_or_app. right. left. reflexivity.
    + eapply bind_parameters_frame; [exact Hbind |].
      intros Hin. apply in_map_iff in Hin.
      destruct Hin as [parameter [Hreg Hin]].
      destruct (parameters_local Hlayout target parameter Hin)
        as [param_index ->]. discriminate.
    + reflexivity.
  - eapply step_parameter_frame; [exact Hlayout | exact Hstep |].
    intros Heq. subst b. contradiction.
Qed.

(* Each executable state has at most one successor. *)
Theorem step_deterministic : forall (before after other_after : state),
  step before after -> step before other_after -> after = other_after.
Proof.
  intros s s' s'' H H'. inversion H; inversion H'; subst; congruence.
Qed.

(* A return is not a stuck instruction or an invalid branch. *)
Theorem return_has_no_step :
  forall (returned : state) (results : list (option Z)),
  return_state returned results ->
  forall (after : state), ~ step returned after.
Proof.
  intros s results [Hremaining [args [Hterm Hargs]]] s' Hstep.
  destruct Hstep; cbn in *; congruence.
Qed.

(* On actual values of a graph with unique instruction definitions,
   register identity agrees with the complete value term. It does not
   agree on arbitrary fabricated expressions, nor need it do so. *)
Theorem defined_value_identity :
  forall (blocks : list block) (v w : value),
  unique_definitions blocks -> defined_value blocks v ->
  defined_value blocks w -> register_of_value v = register_of_value w ->
  v = w.
Proof.
  intros blocks [id op args i | b i] [id' op' args' i' | b' i']
    Hunique Hv Hw Hreg; cbn [register_of_value] in Hreg;
    try discriminate; inversion Hreg; subst.
  - destruct Hv as [b [results [Hb [Hi _]]]].
    destruct Hw as [b' [results' [Hb' [Hi' _]]]].
    destruct (Hunique _ _ _ _ _ _ _ _ _ Hb Hb' Hi Hi')
      as [_ [-> [-> _]]]. reflexivity.
  - reflexivity.
Qed.

(* The extracted block check establishes the instruction whitelist and
   permits only internal control transfers. *)
Theorem supported_block_spec : forall (b : block),
  supported_block b = true ->
  (forall (insn : instr), In insn (block_body b) ->
     supported_instruction insn = true)
  /\ terminator_pure_control (terminator b) = true.
Proof.
  intros b H. apply andb_true_iff in H. destruct H as [Hi Ht].
  rewrite forallb_forall in Hi. auto.
Qed.
