# Reviewing the empty-loop deletion judgement

The Rocq goal is **correctness of the positive deletion judgement**: when
`find_deletions` reports a loop, that loop can be bypassed while retaining
its first header execution. Proving the implementation of the graph rewrite
is outside the Rocq scope; it is a separate OCaml code-review obligation.

The main result is `LoopEligibility.find_deletions_eligible`, in
`backend/ssa/loop/rocq/LoopEligibility.v`. Under its explicit graph,
representation, resource and input premises, it proves `eligible_entry`:

- The original loop reaches the designated parameterless exit after a finite
  sequence of silent integer/control-flow steps.
- The header instructions execute once before the bypass point.
- Every register needed at the exit has the same value as after that first
  header execution. "Needed" means read before its next definition, including
  paths that later re-enter the loop; dead counter registers need not agree.

`eligible_entry_execution` and `eligible_entry_progress` make explicit that
this excludes divergence inside the loop and getting stuck before its exit.
The result covers all counter/comparison shapes accepted by the checker,
subject to the premises below. It is a soundness result, not completeness:
a loop the checker does not report may still be deletable.

## 1. Read the complete contract, not just the theorem declaration

Start with `eligible_entry`, `find_deletions_eligible`, and the definitions
of their premises. Include the hypotheses in the enclosing
`GraphEligibility` section: Rocq generalizes those used by the theorem into
arguments of its exported type. After loading the modules:

```coq
From OxCamlLoop Require Import LoopEligibility.
Check @find_deletions_eligible.
Print Assumptions find_deletions_eligible.
Print SsaExecution.well_formed_ssa.
Print SsaProgress.control_layout.
Print SsaGraph.op_def_correct.
```

The two audit commands answer different questions:

- `Check` shows the theorem's premises, including section hypotheses.
- `Print Assumptions` shows its transitive global axioms and parameters.
  It does not expand theorem premises or the definitions of named predicates.

For a report covering every built module, run:

```sh
make -s -C rocq assumptions > assumptions.txt
```

The report lists global assumptions, then declaration types including nested
modules, generalized section premises and record projections. Auxiliary
lemmas can have stronger premises than the main theorem; those are not
additional reviewer obligations when the main proof discharges them.

Proof scripts can be skipped. Review the statements and definitions that
specify the claim, the compiler-side premises, and the trusted mappings.
A checked proof cannot establish that a mistaken semantic definition matches
the compiler; that correspondence must still be reviewed.

## 2. Check that the semantics express the intended judgement

Read `backend/ssa/rocq/SsaSemantics.v` and `SsaLiveness.v`, together with
`backend/rocq/IntegerComparison.v` and `rocq/OxCamlInt64.v`.

- **Machine arithmetic.** The model is for the 64-bit backend. Register
  arithmetic wraps at 64 bits; analysis `int`s are signed 63-bit values.
  Check `wrap64`, `unsigned64`, signed/unsigned comparisons and untagged
  comparison results of 0 or 1 against backend semantics.
- **Loop whitelist.** `supported_operation` and `supported_instruction`
  accept only integer constants, additions, subtractions and comparisons,
  with the expected operand arity and one result. The check includes the
  header. The exact evaluator also supports immediate shifts and or for
  pre-loop computations; that does not widen the loop whitelist. Result
  count is observed, but full machine types are not: applicability relies
  on the compiler's typing conventions.
- **Register reads.** A use reads an instruction/result or block/parameter
  register. It does not reevaluate its defining expression. Unbound reads
  do not receive default values.
- **Control flow.** Goto reads all arguments before binding parameters.
  Omitted arguments become unbound. Switch preserves target order, selects
  by an in-range nonnegative index, and enters a parameterless target.
- **Observations.** Candidate-loop steps have no memory effects, calls or
  trap manipulation. `live_at` and `agree_on_live` must express all values
  the continuation can observe before their next definition, rather than
  equality of the whole register file.

These definitions and their correspondence to actual SSA instructions are
review obligations. Counter recurrence, termination and live-out agreement
are conclusions of the proof, not extra machine assumptions.

## 3. Establish the ordinary SSA and metadata premises

Compare the following formal contracts with `backend/ssa/ssa.ml` and the
observers in `backend/ssa/rocq/SsaModelExtract.v`.

### Finished graph and dominance

`SsaExecution.well_formed_ssa` and the `GraphEligibility` section require:

- The entry belongs to the supplied graph, and every supplied block is
  structurally reachable. This is not a claim about dynamic feasibility.
- The block list is closed under predecessors and successors.
- `SsaGraph.control_edges` holds: ordinary Goto/Switch edges occur among
  `all_successors`, and predecessor and successor membership agree.
  Exceptional successors must be represented as the compiler reports them.
- `SsaDominance.dominance_semantics` gives the path meaning of a true
  dominance answer. The main theorem also requires complete dominance
  answers for graph blocks, not merely sound true answers.
- `strict_dominators header` contains distinct graph blocks. Review the
  finished dominator-chain walk and its termination at the entry.
- `SsaGraph.switch_edge_multiplicity` holds: repeated Switch targets produce
  repeated predecessor occurrences. A branch to `[next; next] must not
  establish either boolean outcome through a singleton-predecessor test.

The relevant builder code includes `compute_reachability_and_trap_stacks`,
`compute_dominators` and `finish_graph`. Its implementation and checks are
evidence for these premises; the Rocq proof does not verify the OCaml builder.

### Definitions, parameters and uses

Read `result_definition`, `value_definition`, `available_value` and
`well_formed_ssa` in `SsaExecution.v`, `parameter_layout` in
`SsaSemantics.v`, and `control_layout` in `SsaProgress.v`. Check that:

- Each instruction ID has one definition site. A result reference carries
  that actual instruction's opcode and operands, with an in-range index.
- Instruction operands have strictly earlier dominating definitions;
  terminator operands have dominating definitions. Within-block ordering
  matters, not just block dominance.
- Parameter positions are distinct and canonical: position `i` of a block's
  parameter array is `Block_param (block, i)`, and `param` agrees with it.
- Goto argument lists match target parameters in length and order. Every
  omitted argument feeds a parameter with no operand use anywhere in the
  supplied graph. Switch targets have no parameters.
- `delete_empty_loops.ml:compute_op_def` visits every Op and maps its ID to
  its containing block, as required by `SsaGraph.op_def_correct`.

`check_terminator` and `check_value_invariants` are relevant compiler checks.
They do not themselves establish all runtime input conditions below.

### Graph-local identity and representation

`Ssa.Value.equal` compares op-data identity and result index, whereas
`SsaModel.value_eqb_spec` equates complete model values. Check the
correspondence on canonical values of one graph: unique instruction IDs,
shared actual op-data, correct payloads and a finite operand DAG. Do not
identify arbitrary fabricated expressions merely because they reuse an ID.
Similarly, block equality and ID-ordered block sets must agree on the graph.

The extracted analyses inspect existing SSA values rather than constructing
new ones. The custom match functions expose one node's operands at a time.
There is no separate formal OCaml-to-Rocq representation-refinement proof;
this correspondence is part of reviewing the veneer.

## 4. Check input, context and resource applicability

These are explicit premises of `find_deletions_eligible`, distinct from
builder metadata.

- `bounded_registers initial_regs`: every present initial word fits the
  modeled register width.
- `live_registers_bound (entry_point entry) initial_regs`: function-entry
  registers needed before their next definition are bound. Definedness of
  later live operands follows from execution and `control_layout`.
- `switches_in_range (enter header header_regs)`: subsequent executions
  represented by `SsaSemantics.steps` use defined Switch indices. The SSA
  interface declares out-of-range indices undefined behavior. This premise
  is not a claim that the builder validates every runtime index, nor an
  assumed termination or progress property.
- `context_steps (enter entry initial_regs) (enter header header_regs)`:
  the real prefix must be represented by the observation semantics in
  `backend/ssa/rocq/SsaContext.v`.

For the last premise, review `context_step` and `opaque_outputs`. Opaque Op
instructions may produce arbitrary bounded observations in their declared
result registers; other registers are unchanged. Opaque terminators may
take CFG successors and supply arbitrary target-parameter observations.
Calls return through target parameters. This is a word-observation
abstraction, not a full memory, call or vector semantics. Memory effects
are unconstrained, not interpreted as no-ops.

**Trap-stack markers and exceptional transfers from mid-block operations
are not represented by this prefix relation.** Opaque call transfers can
include exceptional successors. If an actual prefix cannot be represented,
the theorem does not cover that execution; the pass does not enforce this
restriction on surrounding code. Covering such prefixes requires extending
the semantics, not asking a reviewer to assume the missing transitions.

Finally, `LoopRangeExecution.graph_size_supported` requires at most
`2^32` supplied blocks. Together with distinct graph-local strict dominators,
this discharges affine atom-counter capacity. **It is an unchecked
host-resource premise, not a limit enforced by the pass.** Establish it for
the supported compilation inputs before applying the theorem.

## 5. Review extraction and the trusted primitives

Read the `*Extract.v` files and check that their mappings implement the
stated model. Check reproducibility with `make -C rocq all`, and that the
root `dune` builds these generated files.

- `SsaModelExtract.v`: value, instruction and terminator matches preserve
  identities, retained payloads, operand/target order and result count
  (`Array.length typ`). The actual Call/Invalid use arrays must be retained
  for liveness and dead-use analysis even though other payloads are abstract.
- `Operation.v`/`OperationExtract.v` and
  `IntegerComparison.v`/`IntegerComparisonExtract.v`: constructors,
  payloads, comparison orientation and negation agree with the compiler
  types and operations.
- `rocq/OxCamlExtract.v`: signed integer and Int64 operations, conversions,
  list/option functions, fold argument order, and short-circuit booleans
  implement their specifications. Check the corresponding arithmetic,
  equality and set axioms, including logical shift by zero and
  `sort_uniq` membership/distinctness.
- `rocq/IntArithExtract.v`: the four unproved overflow tests implement
  `add_fits`, `mul_fits`, `add_fits64` and `mul_fits64`, including zero and
  minimum-integer times minus-one cases.
- Extracted constants agree with their definitions: arithmetic widths,
  the linearization budget, shift limit and Fourier-Motzkin limits.

The trusted foundation also includes the Rocq kernel, extraction and the
primitive libraries named by the assumption audit. Classical logic is used
for definedness and the finite-exit witness; it does not assume facts about
SSA executions.

## 6. Read the checked conclusions; do not resupply them as assumptions

The main theorem discharges the loop-specific obligations through:

- `DeleteEmptyLoops.find_deletions_spec`: the actual reported loop/BIVs have
  the required whitelist, dead-use restrictions, header revisits and exit
  constraints.
- `SsaExecution.v` and `SsaContext.v`: exact operation equations for
  available canonical modeled values, without equations for opaque results.
- `LoopExecution.v`, `LoopInvariantExecution.v` and
  `LoopCounterExecution.v`: actual header visits, counter updates, bound
  constancy and absence of infinite confined execution for accepted rules.
- `LoopValueSnapshot.v`, `LoopGuardExecution.v` and `LoopRangeExecution.v`:
  a constructed affine valuation, actual accepted guard outcomes and
  sound range checks on the observed bound.
- `SsaProgress.v`, `LoopExecution.v` and `LoopLiveOut.v`: progress, finite
  first exit and agreement on live-out values.

Review the meanings of the arithmetic and affine specifications they use,
including `LoopComparisons.loop_exits`, `AffineSsa.linearize_sound`,
`AffineSsa.guards_at_sound` and `FourierMotzkin.entails_sound`. Their proof
scripts, and the proofs connecting them to execution, are checked by Rocq.
In particular, finite exit, affine guard truth and live-out invariance are
not obligations left for the reviewer to prove by inspection.

## 7. Review the mechanical rewrite separately

In `backend/ssa/loop/delete_empty_loops.ml`, `backend/ssa/ssa_reducer.ml`
and `backend/ssa/ssa.ml`, check that the OCaml implementation uses the
proved judgement as intended:

- Apply it to the same finished graph and definition table that were
  analyzed, and bypass only the reported headers toward their selected exits.
- Retain the header's first instruction execution; replace its terminator
  with Goto to the parameterless exit, with no arguments.
- Map blocks and values consistently while rebuilding, and preserve live
  uses through dead-code removal and unreachable-block pruning. Applying
  multiple reported deletions must respect those mappings and continuations.

These are implementation-review obligations, not missing Rocq proofs of the
eligibility judgement. The judgement theorem is deliberately stated on the
original graph; it does not model a post-rewrite graph or the reducer.
