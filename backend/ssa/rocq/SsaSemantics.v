(* Execution of the integer/control-flow fragment used by empty loops.

   Review [supported_operation], [eval_operation], [execute_instruction]
   and [step]. The whitelist, including operand and result arities, is
   extracted; the execution semantics and its proofs are not. Unsupported
   operations have no execution rule here: in particular, memory operations
   are not interpreted as no-ops.

   Registers are identified by instruction/result or block/parameter, not
   by a freely constructed expression. An operand reads its register; only
   executing an instruction evaluates its operation. [step] executes one
   instruction or terminator, and [return_state] distinguishes a return
   from a stuck state. This is a partial SSA semantics, not yet a proof of
   the loop analysis or the graph rewriter. *)

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
Definition supported_instruction (instruction : instr) : bool :=
  match instruction with
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

(* Operations compute on values read from the current environment. These
   clauses, rather than equations imposed on every SSA expression, define
   their semantics. Arithmetic wraps at 64 bits. *)
Definition eval_operation (op : operation) (args : list Z) : option Z :=
  match op, args with
  | Const_int n, [] => Some (Int64.to_Z (Int64.of_nativeint n))
  | Intop Iadd, [x; y] => Some (wrap64 (x + y))
  | Intop Isub, [x; y] => Some (wrap64 (x - y))
  | Intop (Icomp cmp), [x; y] => Some (comparison_value cmp x y)
  | Intop_imm Iadd k, [x] => Some (wrap64 (x + to_Z k))
  | Intop_imm Isub k, [x] => Some (wrap64 (x - to_Z k))
  | Intop_imm (Icomp cmp) k, [x] =>
    Some (comparison_value cmp x (to_Z k))
  | _, _ => None
  end.

Definition execute_instruction (rs : registers) (instruction : instr)
    : option registers :=
  match instruction with
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

(* The remaining instruction list is a suffix of the current block's
   body in a reachable state. Successor selection checks nonnegativity
   before conversion to nat, so negative indices do not select target 0.
   Switch edges have no arguments and may only enter parameterless blocks. *)
Inductive step : state -> state -> Prop :=
  | Step_instruction : forall b instruction rest rs rs',
      execute_instruction rs instruction = Some rs' ->
      step {| current_block := b; remaining := instruction :: rest;
              current_registers := rs |}
           {| current_block := b; remaining := rest;
              current_registers := rs' |}
  | Step_goto : forall b target args rs zs rs',
      terminator b = Terminator.Continue (Goto target) args ->
      read_arguments rs args = Some zs ->
      bind_parameters (params target) zs rs = Some rs' ->
      step {| current_block := b; remaining := [];
              current_registers := rs |} (enter target rs')
  | Step_switch : forall b index targets rs n target,
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
  | Steps_refl : forall s, steps s s
  | Steps_cons : forall s t u, step s t -> steps t u -> steps s u.

Definition valid_position (s : state) : Prop :=
  exists prefix,
    block_body (current_block s) = prefix ++ remaining s.

Definition return_state (s : state) (results : list (option Z)) : Prop :=
  remaining s = []
  /\ exists args,
       terminator (current_block s) = Terminator.Continue Return args
       /\ read_arguments (current_registers s) args = Some results.

Definition bounded_registers (rs : registers) : Prop :=
  forall (r : register) (z : Z), rs r = Some z -> in_int64 z.

(* An actual result reference agrees with the instruction in the graph,
   including its operation and operands. This excludes fabricated [Res]
   expressions that merely borrow the id of another instruction. *)
Definition defined_value (blocks : list block) (v : value) : Prop :=
  match v with
  | Res id op args i =>
    exists b results,
      In b blocks /\ In (Op id op args results) (block_body b)
      /\ 0 <= to_Z i < to_Z results
  | Block_param b i =>
    In b blocks /\ nth_int (params b) i = Some v
  end.

(* A structural condition, independent of executions or loop analysis.
   Instruction identities have one definition in the whole graph. *)
Definition unique_definitions (blocks : list block) : Prop :=
  forall b b' id op op' args args' results results',
    In b blocks -> In b' blocks ->
    In (Op id op args results) (block_body b) ->
    In (Op id op' args' results') (block_body b') ->
    b = b' /\ op = op' /\ args = args' /\ results = results'.

(* ======================================================================== *)
(* Part 3: lemmas                                                          *)
(* ======================================================================== *)

(* Register equality depends only on identity, as the compiler's does. *)
Lemma register_eqb_spec : forall (r s : register),
  register_eqb r s = true <-> r = s.
Proof.
  intros [id i | b i] [id' i' | b' i']; cbn [register_eqb];
    try (split; discriminate).
  - rewrite andb_true_iff, instr_id_eqb_spec, eqb_int.
    split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
  - rewrite andb_true_iff, block_eqb_spec, eqb_int.
    split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

(* Writing a result does not modify any other register. *)
Lemma write_register_other : forall (rs : registers) (r s : register) z,
  s <> r -> write_register rs r z s = rs s.
Proof.
  intros rs r s z Hneq. unfold write_register.
  destruct (register_eqb s r) eqn:E; [ | reflexivity ].
  apply register_eqb_spec in E. contradiction.
Qed.

(* The written register receives exactly the supplied value. *)
Lemma write_register_same : forall (rs : registers) (r : register) z,
  write_register rs r z r = z.
Proof.
  intros rs r z. unfold write_register.
  assert (register_eqb r r = true) by (apply register_eqb_spec; reflexivity).
  rewrite H. reflexivity.
Qed.

(* Reading operands preserves their number. *)
Lemma read_values_length : forall rs args zs,
  read_values rs args = Some zs -> length zs = length args.
Proof.
  intros rs args. induction args as [ | v args IH ]; intros zs H.
  - injection H as <-. reflexivity.
  - cbn [read_values] in H.
    destruct (rs (register_of_value v)); [ | discriminate ].
    destruct (read_values rs args) eqn:E; [ | discriminate ].
    injection H as <-. cbn. f_equal. apply IH. reflexivity.
Qed.

(* Every whitelisted operation is defined for every list of operands of
   its accepted arity. There are no divisions, shifts or memory accesses
   requiring further dynamic preconditions. *)
Lemma supported_operation_total : forall (A : Type) (op : operation)
    (args : list A) (zs : list Z),
  supported_operation op args = true -> length zs = length args ->
  exists z, eval_operation op zs = Some z.
Proof.
  intros A op args zs Hsup Hlen.
  destruct op; try discriminate;
    try (destruct op; try discriminate);
    destruct args as [ | a [ | b [ | c args ] ]]; try discriminate;
    destruct zs as [ | x [ | y [ | z zs ] ]]; try discriminate;
    cbn [eval_operation]; eexists; reflexivity.
Qed.

(* All supported results fit a machine register, including wraparound. *)
Lemma eval_operation_bounded : forall op zs z,
  eval_operation op zs = Some z -> in_int64 z.
Proof.
  intros op zs z H. destruct op; try discriminate;
    try (destruct op; try discriminate);
    destruct zs as [ | x [ | y [ | a zs ] ]]; try discriminate;
    injection H as <-;
    try apply Int64.to_Z_bounded; try apply wrap64_in_range;
    unfold comparison_value; destruct (IntegerComparison.eval _ _ _);
    unfold in_int64, two63; lia.
Qed.

(* Binding a bounded value, or unbinding an omitted parameter, preserves
   the register-width invariant. *)
Lemma write_register_bounded : forall rs r z,
  bounded_registers rs ->
  (forall n, z = Some n -> in_int64 n) ->
  bounded_registers (write_register rs r z).
Proof.
  intros rs r z Hrs Hz s n H. unfold write_register in H.
  destruct (register_eqb s r).
  - apply Hz. exact H.
  - eapply Hrs. exact H.
Qed.

(* Reading Goto arguments preserves the width of each supplied value. *)
Lemma read_arguments_bounded : forall rs args zs,
  bounded_registers rs -> read_arguments rs args = Some zs ->
  Forall (fun z => forall n, z = Some n -> in_int64 n) zs.
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
Lemma bind_parameters_frame : forall ps zs rs rs' r,
  bind_parameters ps zs rs = Some rs' ->
  ~ In r (map register_of_value ps) -> rs' r = rs r.
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
Lemma bind_parameters_values : forall ps zs rs rs',
  NoDup (map register_of_value ps) ->
  bind_parameters ps zs rs = Some rs' ->
  Forall2 (fun p z => rs' (register_of_value p) = z) ps zs.
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

(* Parameter binding preserves register widths. *)
Lemma bind_parameters_bounded : forall ps zs rs rs',
  bounded_registers rs ->
  Forall (fun z => forall n, z = Some n -> in_int64 n) zs ->
  bind_parameters ps zs rs = Some rs' -> bounded_registers rs'.
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
Theorem supported_instruction_executes : forall instruction rs zs,
  supported_instruction instruction = true ->
  read_values rs (args_of_instr instruction) = Some zs ->
  exists id op args z,
    instruction = Op id op args one
    /\ eval_operation op zs = Some z
    /\ execute_instruction rs instruction
       = Some (write_register rs (Result id zero) (Some z)).
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
Theorem execute_instruction_bounded : forall instruction rs rs',
  bounded_registers rs -> execute_instruction rs instruction = Some rs' ->
  bounded_registers rs'.
Proof.
  intros [id op args results | |] rs rs' Hrs H; try discriminate.
  unfold execute_instruction in H.
  destruct (results =? one)%sint63; [ | discriminate ].
  destruct (read_values rs args); [ | discriminate ].
  destruct (eval_operation op l) eqn:E; [ | discriminate ].
  injection H as <-. apply write_register_bounded; [exact Hrs |].
  intros n Hn. injection Hn as <-. eapply eval_operation_bounded. exact E.
Qed.

(* A successful instruction writes no other register, regardless of the
   operation or environment. *)
Theorem execute_instruction_frame : forall id op args results rs rs' r,
  execute_instruction rs (Op id op args results) = Some rs' ->
  r <> Result id zero -> rs' r = rs r.
Proof.
  intros id op args results rs rs' r H Hneq.
  unfold execute_instruction in H.
  destruct (results =? one)%sint63; [ | discriminate ].
  destruct (read_values rs args); [ | discriminate ].
  destruct (eval_operation op l); [ | discriminate ].
  injection H as <-. apply write_register_other. exact Hneq.
Qed.

(* Every operational step, including simultaneous parameter binding,
   preserves machine-word bounds. *)
Theorem step_bounded : forall s s',
  bounded_registers (current_registers s) -> step s s' ->
  bounded_registers (current_registers s').
Proof.
  intros s s' Hrs Hstep. destruct Hstep; cbn in *.
  - eapply execute_instruction_bounded; eassumption.
  - eapply bind_parameters_bounded; [exact Hrs | | eassumption].
    eapply read_arguments_bounded; eassumption.
  - exact Hrs.
Qed.

(* An entry state starts with the actual instructions of its block. *)
Lemma enter_valid_position : forall b rs, valid_position (enter b rs).
Proof. intros b rs. exists []. reflexivity. Qed.

(* Stepping never introduces instructions not in the current block. *)
Theorem step_valid_position : forall s s',
  valid_position s -> step s s' -> valid_position s'.
Proof.
  intros s s' Hpos Hstep. destruct Hstep.
  - destruct Hpos as [prefix Hprefix].
    exists (prefix ++ [instruction]). cbn in *.
    rewrite Hprefix, <- app_assoc. reflexivity.
  - apply enter_valid_position.
  - apply enter_valid_position.
Qed.

(* Every state reached from a block entry has an actual instruction
   position and bounded registers, if the initial registers were bounded. *)
Theorem execution_invariants : forall b rs s,
  bounded_registers rs -> steps (enter b rs) s ->
  valid_position s /\ bounded_registers (current_registers s).
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

(* Each executable state has at most one successor. *)
Theorem step_deterministic : forall s s' s'',
  step s s' -> step s s'' -> s' = s''.
Proof.
  intros s s' s'' H H'. inversion H; inversion H'; subst; congruence.
Qed.

(* A return is not a stuck instruction or an invalid branch. *)
Theorem return_has_no_step : forall s results,
  return_state s results -> forall s', ~ step s s'.
Proof.
  intros s results [Hremaining [args [Hterm Hargs]]] s' Hstep.
  destruct Hstep; cbn in *; congruence.
Qed.

(* On actual values of a graph with unique instruction definitions,
   register identity agrees with the complete value term. It does not
   agree on arbitrary fabricated expressions, nor need it do so. *)
Theorem defined_value_identity : forall blocks v w,
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
Theorem supported_block_spec : forall b,
  supported_block b = true ->
  (forall instruction, In instruction (block_body b) ->
     supported_instruction instruction = true)
  /\ terminator_pure_control (terminator b) = true.
Proof.
  intros b H. apply andb_true_iff in H. destruct H as [Hi Ht].
  rewrite forallb_forall in Hi. auto.
Qed.
