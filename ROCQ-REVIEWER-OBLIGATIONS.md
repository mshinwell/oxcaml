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
