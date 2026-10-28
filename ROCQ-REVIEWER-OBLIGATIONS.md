# Updated review: `c40f2f81` to `8b6cef049a`

This re-review covers the whole change from the original base, including
analysis definitions, theorem statements, extraction directives, the OCaml
veneers, graph construction/reduction and tests. Proof scripts can be
skipped; their statements and the definitions they mention cannot.

**The development now proves useful operational results, but not correctness
of empty-loop deletion as a whole.** I found no new concrete executable
miscompilation in this review. I did find another inadequacy in the legacy
abstract-run record, described in section 5. That record is not used by the
new operational theorems.

The distinction below is important:

- **Review contracts:** independent machine semantics, local graph
  invariants and the correspondence with OCaml representations.
- **Read checked conclusions:** facts already derived by Rocq; reviewers need
  not reconstruct their proofs.
- **Outstanding proofs:** missing execution or transformation arguments.
  These must not quietly become assumptions that reviewers are asked to
  accept.

## 1. Start with the actual top-level claims

Paths in this section are under `backend/ssa/loop/rocq/` unless qualified.
Read enclosing `Section` hypotheses as well as individual theorem statements;
Rocq adds the hypotheses a theorem uses to its exported type.

### Analysis certificate: every reported deletion

`DeleteEmptyLoops.find_deletions_spec` identifies the actual analyzed loop
and BIV list for each returned `(header, exit)`. Its conclusion is
`deletion_certificate`, comprising:

1. The recognized header exit branch targets `exit`, which has no parameters.
2. `LoopTermination.analyze` returned `Terminates` for that BIV list.
3. Infinite control flow confined to the body revisits the header.
4. Every header parameter is a recognized dead BIV, with the specified
   restrictions on parameter, update and exit-comparison uses.
5. All body instructions, including the header's, pass the integer whitelist;
   terminators are Goto or Switch.
6. All edges leaving the body go to `exit`.

The second item is an **analysis verdict**, not by itself an execution
property. The sixth permits early exits to the same target; it does not
say there is only one exiting edge. `certificate_counter` supplies a
particular accepted BIV, so non-emptiness is no longer a separate assumption.

### Operational conclusions: only the stated cases

The public theorems at the end of `LoopCounterExecution.v` establish
`LoopExecution.no_infinite_execution_in`: there is no infinite sequence of
actual `SsaSemantics.step` transitions, from the specified header state,
that stays in the reported body.

- `find_deletions_literal_no_infinite_execution` covers accepted headers
  whose test is an **immediate** integer comparison (`literal_header_test`).
  A constant held in a register does not meet that syntactic condition.
- `find_deletions_unconditional_no_infinite_execution` identifies the
  analyzed loop/BIVs and gives a **conditional** conclusion: an actual BIV
  must satisfy `unconditional_counter`. This selects rules needing no
  entry-range premise: continuing equality with a nonzero step, `<` with
  step `+1`, or `>` with step `-1`, after comparison orientation. Register
  bounds are allowed. Membership in `find_deletions` alone does not
  establish this extra condition.

Both require correct graph metadata, structural SSA well-formedness,
bounded initial registers and a finite execution from function entry to the
header. The register-bound theorem also requires `op_def_correct`.

These are **raw SSA machine steps**, not source-language increments.
An OCaml tagged-integer increment by one can become an addition of two to
its register representation (`backend/cmm_helpers.ml:add_int_caml`). Thus a
source loop using `incr` and a register bound is not automatically covered
by the unconditional `+1` rule. The exact SSA shape matters.

Neither theorem proves that execution cannot get stuck, that it reaches
`exit`, or that the rewritten program has the same results and effects.

### Intermediate facts reviewers no longer have to supply

- `LoopExecution.find_deletions_graph_properties` composes natural-loop
  discovery, header uniqueness, body domination and complete back-edge
  discovery for the particular reported loop.
- `backend/ssa/rocq/SsaExecution.v:execution_values_coherent` derives
  operation equations for available canonical values from execution.
- `LoopExecution.next_header_entry` and
  `LoopCounterExecution.counter_next_entry` connect consecutive actual
  header entries to one counter update, including multiple back edges.
- `LoopInvariantExecution.loop_invariant_value_same` proves equality of
  available bound values at different visits. It does not assume that
  every expression carrying an outside instruction ID is invariant.
- The header's continuing branch condition follows from its actual Switch;
  `LoopComparisons.loop_exits` then contradicts an infinite confined run in
  the covered cases.

The helper `counter_cannot_continue` does take fixed-bound and arithmetic
premises. Inspect the public theorems, which discharge them for their stated
cases, rather than treating that helper as the final contract.

## 2. Review the independent semantics and its scope

Read `backend/ssa/rocq/SsaSemantics.v`, especially `supported_operation`,
`supported_instruction`, `eval_operation`, `execute_instruction`,
`read_arguments`, `bind_parameters`, `step` and `return_state`. Check:

- The target is the 64-bit backend: analysis `int`s are signed 63-bit values;
  register arithmetic wraps at 64 bits. `IntegerComparison.eval` uses signed
  or unsigned comparison as appropriate, and results are untagged 0 or 1.
  Check `wrap64`, `unsigned64` and `in_int64` themselves, not just theorems
  that reuse those definitions.
- Supported instructions are integer constants and binary/immediate
  addition, subtraction and comparison, with exact operand arity and one
  result. The model observes result count, **not** the full machine types;
  correspondence still relies on the compiler's typing conventions.
- A value use reads a register. It does not execute its defining expression
  again. Result registers use instruction ID/result index; parameters use
  block identity/parameter index.
- Goto reads every argument before assigning any target parameter. Omitted
  arguments become unbound rather than retaining an earlier iteration's
  value. Unbound operands and arity mismatches prevent a step.
- Switch preserves target order, checks a nonnegative in-range index and
  enters a parameterless block. For two targets, 0 is false and 1 is true.
  The compiler constructs comparison-based branches in
  `backend/ssa/ssa_of_cmm.ml:emit_branch`; the SSA interface declares an
  out-of-range Switch index undefined. The lowering's truth-test shortcut
  in `cfg_of_ssa.ml` must be understood on that valid-input domain.
- Return is distinguished from a stuck state. There is no heap, event trace,
  call, exception or unsupported-operation execution rule here.

The last point limits even the new termination results. Their reachable
prefix is in this same partial semantics. **A load before an otherwise
supported loop has no step**, so these theorems do not currently cover that
execution, although the implementation deliberately allows the deletion.
Supplying an arbitrary incoming register value does not discharge the
function-entry prefix premise. An abstract context/effect semantics is
still needed; a concrete heap implementation is not necessary.

## 3. Review the graph and representation contracts against OCaml

These are reasonable local contracts, unlike the old per-iteration run
assumptions. They are explicit premises, not proved facts about the OCaml
builder.

### Graph observations and metadata

Compare `SsaModelExtract.v` and `SsaGraph.control_edges` with
`backend/ssa/ssa.ml`:

- `Ssa.blocks` supplies the whole relevant finished graph, with predecessor
  and successor closure. `all_successors` includes exceptional successors,
  and predecessors describe the same edges.
- Dominance is reflexive and has the path meaning in
  `SsaDominance.dominance_semantics`. The public operational composition also
  requires **complete**, not merely sound, dominance answers for graph
  blocks. `strict_dominators` must walk the finished dominator chain and
  terminate at entry.
- `parameter_layout` matches the actual parameter array: its element at
  index `i` is `Block_param (block, i)`, indices are distinct, and `param`
  agrees with the array. Actual arrays and generated indices fit OCaml ints.
- `compute_op_def` in `delete_empty_loops.ml` visits every Op in `Ssa.blocks`
  and maps its ID to the containing block. The source satisfies the stated
  one-way `op_def_correct` contract provided graph IDs are unique.

`compute_reachability_and_trap_stacks`, `compute_dominators`,
`check_terminator`, `check_value_invariants` and `finish_graph` are the
relevant builder code. In particular, the builder checks Goto arity,
parameterless Switch targets and omitted arguments feeding unused
parameters. Those checks are useful evidence, not a proof of every premise
of `well_formed_ssa`, nor a guarantee that every runtime Switch index is valid.

### Canonical values, not arbitrary terms with borrowed IDs

Read `backend/ssa/rocq/SsaExecution.v:well_formed_ssa` and its definitions of
`result_definition`, `value_definition` and `available_value`. Check that:

- each instruction ID has one definition site;
- a result reference carries that actual instruction's operation and
  operands, with an in-range result index;
- instruction operands have strictly earlier dominating definitions, and
  terminator operands have dominating definitions;
- parameter definitions belong to the graph and have the stated indices.

There is also a representation obligation beyond reading record fields.
`Ssa.Value.equal` compares op-data identity and result index, whereas
`SsaModel.value_eqb_spec` equates entire Rocq `value` terms, including their
payloads. They correspond on **canonical values of one graph**, with unique
IDs and finite operand DAGs; they do not correspond on arbitrary fabricated
Rocq terms. Likewise, block sets compare IDs while `Block.equal` uses physical
identity. Keep the graph-local identity invariant explicit. The SSA interface
already prohibits mixing IDs from different graphs.

The extracted analyses inspect existing values and do not construct new Res
or block values. The custom match functions unfold only the immediate
argument array, not the whole DAG. The finite canonical representation and
this read-only use justify the correspondence to check; there is not a
formal OCaml-to-Rocq representation-refinement theorem.

## 4. Review the trusted extraction and arithmetic code

Read all `*Extract.v` files, not the generated `.ml` as a second independent
implementation. Check the generated files are reproducible and are what
`dune` builds.

- `SsaModelExtract.v` has three custom matches: values, instructions and
  terminators. Check every retained field, array order, and the result count
  obtained by `Array.length typ`. Call/Invalid payloads are intentionally
  incomplete for execution, but their actual value-use arrays are retained
  for dead-use analysis. Trap instructions have no SSA value operands and
  are rejected inside candidate loops.
- `Operation.v`/`OperationExtract.v` correspond to `backend/operation.mli`;
  `IntegerComparison.v`/`IntegerComparisonExtract.v` correspond to
  `Scalar.Integer_comparison`, including constructor order, swap and negate.
  The named-record refactor of operation payloads preserves their fields;
  the two AMD64 edits qualify the now-shared record labels.
- `rocq/OxCamlExtract.v` maps the correct signed integer, Int64, list and
  option operations, including fold argument order and short-circuit boolean
  operators. Inspect the Int64 axioms for wraparound, signed division,
  conversion bounds and shifts, including logical shift by zero. Check the
  `sort_uniq` membership/no-duplicates axioms and the block-set axioms against
  their mapped library operations as well.
- `rocq/IntArithExtract.v` contains four unproved overflow predicates. Check
  the addition sign-bit tests and multiplication divide-back tests, including
  zero and minimum-integer times minus-one cases. Rocq assumes their specs.
- Check extracted numeric literals against their definitions: the 256-node
  linearization budget, shift limit, 64-bit width and Fourier-Motzkin limits.
  Overflow/size-limit fallbacks must remain conservative. The atom counter's
  no-wrap condition is separate from the per-linearization node budget.
- `rocq/Makefile`, `Extract.v` and root `dune` select the generated analyses.
  The execution proofs are checked by Rocq but are not runtime code. The old
  handwritten analysis modules are removed, not a fallback implementation.

For the mathematical layers, review the meanings and public conclusions:
`FourierMotzkin.entails_sound`, `AffineExpr.to_affine_sound`,
`AffineSsa.linearize_sound`/`guards_at_sound`, and
`LoopComparisons.loop_exits`.
Their arithmetic proofs need not be redone. In particular, the AffineSsa
results still have valuation and taken-guard premises; they are not yet
operational range theorems.

## 5. Do not reinstate the legacy run record as a contract

The earlier fabricated-value invariance problem is avoided by the new
available-value proofs. A separate problem remains in
`LoopTermination.loop_entry.iter_branches`:

```text
preheader: switch comparison [next; next]
next:      ... goto header ...
```

If every path to the header takes `preheader -> next`, the legacy field
applies for both `negate = false` and `negate = true`. It demands that the
same comparison be both true and false. Both outcomes actually take the
same edge. A scratch Rocq lemma checked this contradiction during this
review; it requires no counter or arithmetic-run assumptions.

This is an **adequacy defect in the legacy premise**, not a demonstrated
miscompilation by the current checker. The real builder records one
predecessor occurrence per edge (`ssa.ml:add_pred_to`), so this example gives
`[preheader; preheader]`. `sole_predecessor` rejects it, and `guard_test` does
not infer either outcome. But `control_edges` expresses edge membership,
not multiplicity: those current graph premises alone do not explain that
rejection.

The future entry-guard proof should reason about the guards actually
accepted, their executed branch outcomes and the values still available at
loop entry. It must handle duplicate targets and repeated visits explicitly,
not assume the broader `iter_branches` field. The current public operational
theorems use neither that field nor `infinite_header_run`.

## 6. Missing correctness arguments are still missing proofs

To justify the complete optimizer, the following remain:

1. **Remaining termination cases.** Derive affine entry-range facts from
   execution for register bounds requiring them, including a justified
   atom-counter bound. The implementation accepts these cases today; it is
   not restricted to the coverage of the two new operational theorems.
2. **Progress and finite exit.** Under suitable valid-input and graph
   conditions, prove no unbound read, invalid Switch or other stuck state
   occurs in a candidate loop. Combine this with the no-infinite result and
   `exits_only_to` to prove a finite silent arrival at the exit.
3. **Live-out agreement.** Prove every value needed after the loop has the
   same value after bypass. Header instructions run once after rewriting but
   may have run many times originally. Zero exit parameters alone does not
   settle this: later blocks can directly read header results. The dead-use
   checks must establish that changing counters, updates and the comparison
   cannot affect live outputs. Whole-register-environment equality would be
   wrong, because dead counters intentionally differ.
4. **Rewrite and composition.** Define the abstract header-terminator rewrite
   and prove behavior preservation, including divergence, for all selected
   loops together or by a justified composition argument.
5. **Context and reducer correspondence.** Cover unsupported surrounding code
   as discussed above, and relate the abstract rewrite to block/value
   renaming, dead-code removal and unreachable-block pruning.

The current OCaml rewrite is small and looks faithful to the intended
operation: it builds a header-to-exit table, overrides only selected
terminators with `Goto exit` and an empty argument array, and uses
`Context.map_terminator` for output identities. `Ssa_reducer.Make_run` copies
instructions and maps values before finishing the new graph. Review those
facts in `delete_empty_loops.ml`, `ssa_reducer.ml` and `ssa.ml`; no theorem yet
says that this rewrite preserves behavior. The SSA builder's metadata and
usage-count calculations, and the reducer, remain unverified.

## 7. Evidence and remaining review discipline

For this re-review:

- Forced a rebuild of all Rocq sources and extraction with
  `make -C rocq -B all`; it passed and produced no tracked changes.
- Checked exported types and `Print Assumptions` for the certificate and both
  public operational theorems. They contain no legacy run assumption or
  newly introduced execution axiom. This does not itself establish adequacy
  of their premises; that is why the source review above is still needed.
- Checked the duplicate-target diagnostic in scratch, without adding axioms
  or changing repository code.
- Reviewed the SSA decision tests and native regressions. Unit tests assert
  deletion counts for simple/diamond loops and retention of internal cycles
  and unsupported operations. Native tests check observable results; their
  comments about which loops are deleted are not all automated assertions.

The compiler build, SSA tests and formatting passed on the committed source
in the preceding validation. That full suite reported 2742 passes, 214 skips
and one dynlink thread-output failure; the failing test passed in isolation.
The full compiler suite was not repeated for this documentation-only update.

The older `ROCQ-VACUITY-AUDIT.md` and `ROCQ-DIRECT-MATCHING.md` describe
historical revisions, not the current proof boundary. In particular, do not
reuse their assurances about run hypotheses or representation without the
qualifications above. The previous contents of this file are preserved
unchanged below.

---

# Reviewing the empty-loop model

The review boundary is stated in the source, not supplied by this note.
Read definitions, contracts and theorem statements; Rocq checks the proofs.
The operational proof is still incomplete. In particular, the old request
to justify `infinite_header_run` by inspection is withdrawn: that record is
not a trusted compiler contract.

## Source reading order

1. `backend/ssa/rocq/SsaSemantics.v`: the extracted whitelist and independent
   instruction semantics. Operands read registers; executing an instruction
   computes its result. Goto arguments are read before parameters are bound.
   Omitted arguments become unbound, and invalid Switch indices get stuck.
2. `backend/ssa/rocq/SsaExecution.v`: `well_formed_ssa`, canonical definitions,
   availability and `execution_values_coherent`. Only actual available
   definitions acquire operation equations; arbitrary fabricated `Res`
   expressions do not.
3. `backend/ssa/loop/rocq/DeleteEmptyLoops.v`: the extracted decision and
   `find_deletions_spec`. Its conclusion is a `deletion_certificate`, not
   behavior preservation.
4. `LoopExecution.v`, `LoopInvariantExecution.v` and
   `LoopCounterExecution.v` in the same loop directory: graph composition,
   actual header visits, counter recurrence, bound constancy and the
   operational no-infinite-execution theorems.

## What the certificate establishes

Every returned `(header, exit)` belongs to an actual analyzed loop and BIV
list satisfying these six conjuncts:

- `exit_branch_to`: the header has the recognized two-way Switch and its
  exit target takes no arguments.
- `LoopTermination.analyze ... = Terminates`: the arithmetic analysis
  accepted at least one of those BIVs (`certificate_counter` supplies it).
- `revisits`: infinite control flow confined to the body revisits the header.
- `params_are_dead_bivs`: every header parameter is a recognized dead BIV.
- `body_in_supported_fragment`: every body instruction, including those in
  the header, is an integer constant, addition, subtraction or comparison
  with the expected arities; terminators are Goto or Switch.
- `exits_only_to`: every edge leaving the body goes to the same exit target.
  This does not require every exiting edge to originate at the header.

There is no `no_infinite_header_run` conjunct. A contradiction in the
legacy abstract run model is no longer presented as operational termination.

## What is now proved from execution

`LoopCounterExecution.v` composes the actual deletion decision with two
operational results:

- `find_deletions_literal_no_infinite_execution`: accepted loops whose
  header tests an immediate comparison cannot execute forever inside the
  body, starting at a reachable header entry.
- `find_deletions_unconditional_no_infinite_execution`: the same conclusion
  for an actual analyzed BIV satisfying `unconditional_counter`. This is a
  static condition selecting comparison rules that need no bound-range
  premise, for example increment by one with continuing comparison `<`.
  Register bounds are allowed; their constancy is proved, not assumed.

Both use the independent `step` semantics, structural SSA well-formedness,
accurate graph metadata, and bounded initial registers. Consecutive header
entries advance the counter once, including branches and multiple back
edges. The comparison reads that counter or its update. Every mathematical
iteration is realized by an actual entry, so the arithmetic eventual-failure
theorem contradicts an infinite confined execution.

`no_infinite_execution_in` means exactly that. It does **not** imply that a
finite execution cannot get stuck, or that the rewritten program agrees.

## Remaining local compiler contracts

These are explicit source premises or extraction contracts:

- `Ssa.blocks ssa` includes the whole graph and is closed under predecessor
  and successor edges. The two edge views agree (`control_edges`).
- Dominance answers have the stated path meaning and are complete for graph
  blocks where required by `find_deletions_graph_properties`.
- `terminator`, `block_body`, `params` and `param` read actual block data.
  Parameter positions have the identities specified by `parameter_layout`.
  Instruction matches return the actual opcode, operands and result count.
- The graph builder satisfies `well_formed_ssa`: unique instruction sites,
  canonical references, valid result indices and definition/use dominance,
  including instruction order. This has not been proved for the OCaml
  builder.
- `compute_op_def` maps every actual instruction ID to its containing block
  (`op_def_correct`).
- Equality, set and integer primitives satisfy their stated contracts. The
  extraction directives and handwritten value/instruction/terminator match
  functions correspond to the OCaml representations. Operation constructors
  remain in the compiler's order.
- The Rocq kernel and extraction are trusted as usual.

## Missing proofs, not reviewer assumptions

- **Entry-range facts:** connect the affine bound and guard analysis to
  reachable execution for register-bound rules needing a range premise.
  Prove the relevant executed guards and account for the static atom-counter
  bound; do not assume the legacy run record.
- **Progress and finite exit:** exclude stuck executions under suitable
  structural typing, argument and Switch conditions. The current
  `well_formed_ssa` does not itself rule out reading an omitted parameter or
  selecting an invalid Switch index.
- **Live-out agreement and rewrite preservation:** the rewritten header
  executes once, whereas the original may execute it many times. Prove
  agreement for values needed after the loop; equality of the entire
  register environment is neither necessary nor true for dead counters.
- **Surrounding code:** the partial semantics has no rules for unsupported
  operations, even outside the loop. The implementation permits such
  operations outside candidate loops; covering those executions needs an
  abstract context/effect semantics, not an interpretation as no-ops.
- **Reducer correspondence:** relate the abstract header-terminator rewrite
  to `Ssa_reducer`, pruning, renaming and composition of multiple deletions.

The accepted direction remains `ROCQ-SEMANTICS-PROPOSAL.md`. None of these
missing proofs is discharged by asking a reviewer to accept a prose
execution argument.
