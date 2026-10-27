# What a reviewer of the loop models must check

Date: 2026-10-28, at commit 216b1c3442. The Rocq models under
`backend/ssa/rocq/` and `backend/ssa/loop/rocq/` have no small-step
semantics of SSA. This note states precisely what Rocq proves about the
empty-loop deletion pass, and what therefore remains for a reviewer to
check by inspection before concluding that the pass is correct.

## What Rocq proves

One theorem, `DeleteEmptyLoops.find_deletions_spec`: for any table
`op_def` and block list `blocks`, every pair `(header, exit)` returned by
`find_deletions op_def blocks` is the header of a loop that
`InductionVar.analyze op_def blocks` reports, with that loop's basic
induction variables, and the loop satisfies `deletable` with exit
`exit`. The conjuncts of `deletable` are:

- `exit_branch_to`: the header's terminator is a two-way `Switch`, one
  edge into the body and the other to `exit`, which takes no arguments;
- `no_infinite_header_run`: for every block `entry` and every function
  `iter` from visit numbers and SSA values to integers, the record
  `infinite_header_run entry op_def loop iter` is contradictory;
- `revisits`: a sequence of body blocks, each a successor of the one
  before, contains the header after any point;
- `params_are_dead_bivs`: every header parameter is a basic induction
  variable (`biv_spec`) that is dead (`dead_spec`);
- `body_does_nothing`: every body block has only instructions with
  `has_side_effect = false` and a `Goto` or `Switch` terminator;
- `exits_only_to`: every successor of a body block is in the body or is
  `exit`.

Every conjunct but the second is a proposition over the observations
SsaModel.v takes from the compiler: `predecessors`, `all_successors`,
`dominates`, `params`, `param`, `block_body`, `terminator`,
`has_side_effect` and `op_def_find`. The second quantifies over a
mathematical function `iter`. Nothing in Rocq connects `iter` to an
execution of the compiled function; that connection is obligation 1.

## Obligation 1: the run hypotheses hold of real executions

The claim to check is this. Take any execution of the compiled function
and any segment of it that begins with control entering the loop's
header and in which control never leaves the loop body. Suppose the
segment is infinite. Then it visits the header infinitely often: the
blocks it visits form a sequence of body blocks following the graph's
edges, so `revisits` (a theorem) places the header after any point.
Define `iter n v` as the value the execution gives the SSA value `v`
during the n-th header visit of the segment, with the defaults the
comment on `infinite_header_run` in LoopTermination.v gives for values
the segment does not compute. The claim is that
`infinite_header_run entry op_def loop iter` holds, `entry` being the
function's entry block.

The reviewer checks the claim field by field, against their
understanding of how SSA code executes. The nine fields are:

- `iter_bounded`: every value is a 64-bit register.
- `iter_op`: the operations listed in `AffineSsa.op_semantics` compute
  what it says: addition, subtraction and left shift wrap at 64 bits,
  the arithmetic right shift divides rounding towards minus infinity,
  the logical right shift divides the unsigned reading of its argument,
  or is the bitwise or, and `Const_int n` is `Int64.of_nativeint n`.
- `iter_comparison`: a comparison instruction yields 1 or 0 according to
  `IntegerComparison.eval`, which must be the machine's signed and
  unsigned comparison of 64-bit values.
- `run_dominance`: `Block.dominates d b = true` implies that every path
  from the entry to `b` passes through `d`, and the entry dominates
  every block. The latter needs every block of a finished graph to be
  reachable from the entry, or `dominates` to answer `true` for the
  entry and an unreachable block.
- `iter_branches`: when a block ends in a two-way `Switch` and every
  path from the entry to the header takes one given edge of it, the
  comparison it tests came out the way that edge requires, at the first
  visit.
- `iter_invariant`: a value that is a constant, or is defined in a block
  that strictly dominates the header, has the same value at every
  visit. This relies on such a block not being in the body, which
  follows from the header dominating every body block (a consequence of
  `find_loops_body` in NaturalLoop.v), and on `op_def` naming the right
  defining block (obligation 2).
- `run_continues`: at every visit the header's `Switch` goes into the
  body. This is the definition of the segment.
- `run_back_edge`: the next visit arrives from a block in
  `back_edge_sources` that is a predecessor of the header, whose
  terminator is a `Goto` to the header, and the value of each header
  parameter at the next visit is the value of the corresponding
  argument at this one. This is SSA parameter passing, plus the fact
  that every edge from the body into the header is a back edge of this
  loop, which is `find_loops_complete` in NaturalLoop.v applied under the
  closure hypotheses of obligation 2.
- `run_atoms_fit`: the header has fewer than about 2^53 dominating
  branches, so the atom counter of AffineSsa.v cannot wrap.

Once the claim is accepted, `analyze_Terminates_of_graph` makes the
infinite segment contradictory. So every entry into the loop leaves the
body after finitely many steps, and by `exits_only_to` it can only leave
along an edge to `exit`.

## Obligation 2: the observations are the graph

- The list passed to `find_deletions`, `Ssa.blocks ssa`, is the whole
  graph: closed under predecessors and under successors. The theorems
  of NaturalLoop.v take this as the hypotheses `blocks_closed` and
  `succs_closed`. It is not a conjunct of `deletable`, so the reviewer
  applies those theorems by hand where obligation 1 needs them. (Adding
  the natural-loop facts to `deletable` under these hypotheses is an
  open item of ROCQ-VACUITY-AUDIT.md.)
- `predecessors` and `all_successors` describe the same edges from both
  ends.
- `terminator`, `params`, `param` and `block_body` return the block's
  own data, and `has_side_effect = false` means that the instruction
  has no effect beyond defining its results.
- `compute_op_def` in delete_empty_loops.ml maps each `Op` id to the
  block containing it, so that `op_def_find op_def id = Some b` exactly
  when `b` holds the instruction `id`.
- `Ssa.Value.equal` identifies two values only when they denote the
  same register value; `Ssa.Block.equal` and `Ssa.Instruction.Id.equal`
  are identity.
- The extraction directives in the `*Extract.v` files name the right
  OxCaml values, including the three hand-written match functions for
  values, instructions and terminators in SsaModelExtract.v, and
  `backend/rocq/Operation.v` lists the constructors of `Operation.t` in
  the compiler's order. The axioms of OxCamlInt64.v, OxCamlList.v,
  IntArith.v (with the OxCaml in IntArithExtract.v) and SsaModel.v hold
  of the OxCaml functions they describe.
- The Rocq kernel and extraction are trusted as usual.

## Obligation 3: the rewrite is justified by `deletable`

The rewrite, `Delete_empty_loops.run`, replaces the header's terminator
by an unconditional jump to `exit`, which takes no arguments; the body
becomes unreachable and is pruned. It is not modelled. The reviewer
checks the argument in the header comment of DeleteEmptyLoops.v:

- Termination and control: by obligation 1 the original loop always
  reaches `exit`, and by `exits_only_to` and `body_does_nothing` it can
  be left no other way (no call, raise or return in the body). The
  rewritten code reaches `exit` at once.
- Effects: the body performs none, so skipping it is unobservable.
- Values: the header's instructions still run once after the rewrite.
  Every header-defined value used after the loop must have, in that
  single iteration, the value it had in the last original iteration.
  The argument is that, by SSA scoping, such a value is a header
  parameter, which `dead_spec` forbids any use of outside the loop's
  control, or an instruction whose inputs are loop-invariant values,
  loads from memory the body does not write, or header parameters, the
  last excluded by `dead_spec` for any instruction other than the exit
  comparison and the parameter's own updates.

The value argument makes one assumption that is neither a graph property
nor a conjunct of `deletable`: a load in the header reads the same
memory at every iteration. Within the function this follows from
`body_does_nothing` (no store in the body); across threads or domains it
is a memory-model statement. It is the one item in this note that
deserves a second opinion.

## What is not covered at all

- The dominator computation behind `Block.dominates`.
- The invariants of a finished SSA graph that the observations rely on
  (one `op_data` per instruction, parameters bound by `Goto` arguments,
  pruning of unreachable blocks).
- `Ssa_reducer`, which performs the rewrite.
