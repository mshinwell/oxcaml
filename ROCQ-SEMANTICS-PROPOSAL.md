# A clearer soundness boundary for empty-loop deletion

This proposal responds to `ROCQ-REVIEWER-OBLIGATIONS.md` at revision
`ddb773dee1bda63f0f9cbc5dff339f2ace8e7d2a`.

**Obligation 1 should be a theorem, not a reviewer obligation. A small
operational semantics is the right next step, and it need not include a
concrete memory model.** Obligation 3 should largely become a theorem too.

The distinction is:

- “This accessor returns the block’s instructions” is a reasonable veneer
  contract.
- “Every real infinite execution induces this particular mathematical
  object” is a substantial correctness argument. Leaving it to inspection
  defeats much of the purpose of the proof.

## There is a concrete problem with Obligation 1

This is more than a concern about presentation. I checked a short lemma in
Rocq against the revision above showing that the run hypotheses are too
strong.

`SsaModel.value` permits constructing arbitrary terms:

```rocq
Res id op args result_index
```

Meanwhile:

- `iter_op` specifies arithmetic for **every** such term.
- `iter_invariant` specifies invariance for **every** term classified as
  loop-invariant.
- `loop_invariant_value` classifies a nonconstant result using its
  instruction ID’s defining block, without checking that its operation and
  arguments belong to that instruction.

Suppose `id` belongs to an instruction in a strict dominator of the header.
For any value `v`, construct:

```rocq
Res id (Intop_imm Iadd zero) [v] zero
```

Call this fabricated value `w`.

1. Its borrowed ID makes `w` loop-invariant.
2. Its operation makes its value equal to `v`, since adding zero preserves
   a bounded machine integer.
3. Consequently, **`v` must be loop-invariant too**.

The checked lemma establishes that, given such an ID, `infinite_header_run`
forces:

```rocq
forall n v, iter n v = iter 0 v
```

That includes the induction variable. Thus the model cannot represent
ordinary varying-counter executions under these circumstances.

This is an **adequacy defect**, not by itself evidence of an executable
miscompilation. But it demonstrates why “the reviewer checks that these
fields hold” is unacceptable here. I was too accepting of that boundary in
the earlier review.

## 1. Give executions an independent meaning

I would introduce a small SSA operational semantics whose state contains:

```text
current block
position within the block
register environment
abstract external state
```

Its rules should say:

- An instruction reads its operands from the environment, performs its
  operation, and binds its results.
- A `Goto` evaluates its arguments in the old environment, then binds the
  target parameters **simultaneously**.
- A `Switch` selects the successor at the computed index.
- Returns, exceptions and other observable actions are represented
  explicitly.
- Invalid execution is distinguished from successful termination.

Crucially, **using an SSA value reads a previously computed result; it does
not recursively execute its defining expression again**. This matters
particularly for loads.

The current instruction view omits its opcode and result types, and the
call view omits execution-relevant details. Those observations need modest
enrichment, or a canonical instruction-definition lookup. We should not
try to extract an execution semantics from an analysis view that
deliberately discarded those details.

### Restrict semantic facts to actual program values

Alongside this, define structural SSA well-formedness:

- Each instruction ID has one canonical definition.
- A `Res` reference agrees with that definition’s operation, operands and
  result index.
- Parameters, arities and operand types are valid.
- Definitions dominate uses, including instruction ordering within a block.
- Edges and parameter passing agree.
- The graph’s block list is complete.

These must be structural properties—not a record containing “there exists
an `iter` satisfying everything the analysis needs.”

It is not necessary to abandon direct matching on the existing datatype.
We can retain it and introduce program-membership and
definition-consistency predicates. But semantic and equality contracts
must respect that domain. In particular, arbitrary fabricated `Res` terms
must not acquire facts merely by borrowing an ID.

## 2. Prove the connection to the existing analysis

The existing arithmetic and graph proofs remain useful. What is missing
is the theorem connecting them to execution.

The intended chain is:

1. Execution steps follow the graph’s edges.
2. An infinite execution staying in an accepted body visits the header
   infinitely often, using the existing `revisits` result.
3. Those visits yield the induction-variable recurrence and branch
   conditions needed by the termination proof.
4. The termination proof contradicts that infinite execution.

Most of Obligation 1 then becomes ordinary lemmas:

- **Arithmetic and comparison values:** instruction execution rules.
- **Values defined outside the loop remain fixed:** SSA well-formedness,
  natural-loop properties, and environment updates.
- **Entry guards held:** executed branch rules and the relevant
  dominance/path facts.
- **Header parameters receive back-edge arguments:** the `Goto` rule.
- **Execution returns to the header:** the existing acyclicity/revisit
  proof.
- **Atom counter fits:** a static size condition or checked bound—not an
  execution hypothesis.

The natural-loop closure, dominance and back-edge facts should be composed
into this theorem in Rocq. A reviewer should not have to apply
`find_loops_complete` manually.

I would also narrow the sampled valuation to the values and program points
the arithmetic proof actually needs. Requiring one total valuation to
satisfy operation equations for every value—including unexecuted
instructions—is an unnecessarily difficult interface.

**Keeping `infinite_header_run` as an internal abstraction is fine, after
repairing it, provided constructing it from execution is proved.** Making
that construction another axiom would merely rename Obligation 1.

## 3. Memory can remain abstract—but operation properties cannot

We do not need to implement heaps, allocation or stores to reason about
this pass.

For example, use an abstract type `world`. An operation’s semantics
consumes its explicit operand values and a world, and produces results, a
world and observable events. Stores and calls outside the deleted region
can remain abstract: the two executions perform the same operation with
the same inputs.

For ordinary sequential loads, even this can suffice:

```text
read : world × address × chunk → result
```

A loop that preserves the world and the load’s inputs repeats the same
read. No concrete memory layout or store implementation is needed.

However, **“has no side effects” is not the same as “can be skipped or
repeated harmlessly.”** We need to distinguish:

- Producing no observable event.
- Preserving external state.
- Terminating normally on the relevant inputs.
- Producing the same result when repeated with unchanged inputs and state.

The last property matters for header results used after the loop. The
first three matter when instructions are skipped.

Currently `Ssa.Instruction.has_side_effect` accepts all `Load` operations.
“The loop contains no stores” does not alone establish stability under
concurrent writes. Faults and other environmental operations also need a
deliberate treatment.

There are two honest approaches:

- **Smallest initial scope:** prove deletion for a whitelist of suitably
  pure operations, conservatively retaining loops containing unsupported
  operations. Loads before the loop remain fine: their already-computed
  SSA results are fixed.
- **Preserve the current eligibility:** provide explicit contracts for the
  currently accepted operations, including the intended memory/concurrency
  semantics for loads.

The first is simpler but changes optimization coverage; it should be an
explicit decision, not an incidental consequence of restructuring the
proofs. A sequential load model is useful, but must not be presented as a
concurrency proof.

## 4. Prove the rewrite, not just termination

Even a completed termination bridge would leave a substantial part of
Obligation 3 outstanding.

The useful local theorem is approximately:

> Entering an accepted loop reaches its unique exit after finitely many
> silent steps, with the same external state and the same values needed by
> subsequent execution as the bypassed version.

The equality should concern **live-out values**, not the entire register
environment: dead induction variables intentionally differ.

“No exit parameters” is not enough. A header instruction may define a
register read directly after the loop. The existing dead-use checks
should establish that any such result is independent of the changing
loop-control values; the operation contracts then establish its
stability. That argument belongs in Rocq.

I would first model the rewrite as changing header terminators while
retaining block identities and unreachable blocks. Then:

- Prove that rewrite preserves behavior.
- Handle all selected deletions together, or prove their composition.
- Treat pruning and renaming separately.

This gives the `Ssa_reducer` veneer a precise correspondence requirement:
it implements that graph rewrite, modulo renaming and unreachable-code
removal. It does not automatically verify the reducer, but it makes the
remaining contract concrete.

## 5. Make the source itself identify what needs reviewing

The top-level theorem should eventually have a shape like
this—schematically:

```rocq
wf_ssa graph ->
metadata_correct graph ->
machine_contract machine ->
behaviors_equivalent
  (execute machine graph)
  (execute machine (rewrite_selected_loops graph)).
```

Its conclusion must preserve divergence as well as terminating results and
observable actions. Merely proving “if the original terminates, the
answers agree” would miss the central empty-loop-deletion failure mode.

The review surface would then be:

1. The independent execution semantics.
2. Structural graph invariants and local machine contracts.
3. The behavior-preservation theorem statement.
4. Extraction and rewrite correspondence.

The current `find_deletions_spec` remains useful as an
**analysis-certificate theorem**, but should not be mistaken for optimizer
correctness.

`Print Assumptions` helps audit axioms, but is insufficient: the present
problem is hidden in predicates appearing inside theorem statements, not
an `Admitted`.

## Recommended sequence

1. Repair the domain of value hypotheses and introduce explicit structural
   SSA invariants.
2. Add the small operational semantics and prove the execution-to-analysis
   connection.
3. Prove silent exit and live-out agreement, then the abstract rewrite
   theorem.
4. Deliberately settle the operation coverage, especially loads, and
   tighten the reducer correspondence.

That would turn most of Obligations 1 and 3 into checked proofs while
leaving the reasonable parts of Obligation 2 as small, local contracts.

## Validation of the review

The Rocq sources at the revision above rebuilt in scratch, and the
diagnostic lemma above compiled successfully. No compiler or proof
implementation changes are part of this proposal.
