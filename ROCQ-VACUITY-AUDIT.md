# Vacuity audit of the Rocq models

Date: 2026-10-27. Scope: every `.v` file under `rocq/`, `backend/rocq/`,
`backend/ssa/rocq/` and `backend/ssa/loop/rocq/`, together with the
extraction directives and the compiler functions they name, at commit
1caba8b525.

## The hazard

A hypothesis stated through a part-1 analysis function trusts that
function silently. If the function is wrong, the hypothesis may be false
of every real execution, so that the theorem says nothing about the
program, or true of executions it was not meant to describe. The
question for each file is therefore which statements at the top of the
development, and which axioms, mention part-1 code or depend on a
computed result, and whether each such dependence is justified.

The top-level theorem is `DeleteEmptyLoops.find_deletions_spec`. It has
no hypothesis. The assumptions about the world are the fields of
`LoopTermination.infinite_header_run`, which is the meaning of a run of
the loop that never ends, the axioms about the primitives of
`SsaModel.v`, `OxCamlInt64.v`, `OxCamlList.v` and `IntArith.v`, and the
extraction directives in the `*Extract.v` files.

## Findings

### 1. `atom_counter_fits` is stated through analysis code

`LoopTermination.atom_counter_fits`, a field of `infinite_header_run`,
is stated with `AffineSsa.guards_size`, which unfolds through
`guard_size`, `guard_test` and `SsaDominance.edge_dominates`, all part-1
definitions. It is the last field of the run record that a reviewer
cannot read without reading the analysis.

The risk is low. The field only bounds the atom counter of
`AffineSsa.v`, an OxCaml `int`, and no mistake in `guard_test` could make
it unsatisfiable short of a sum beyond 2^62. The field can nevertheless
be restated through primitives alone: every tree of `tree_of_value` has
at most 256 nodes, which is the budget `Ssa_view.tree_of_value`
documents, and the header has fewer than about 2^53 strict dominators. A
lemma bounding `guards_size target` by 258 times the length of
`strict_dominators target` carries the existing proof. The 256-node
bound could instead be an axiom of `SsaModel.v` beside
`tree_of_value_root`, which would need `size` moved there.

### 2. The meaning of the loop record does not reach the top theorem

`run_continues` and `run_back_edge` in the run record, and
`no_infinite_path_except l.(body) l.(header)`, `body_does_nothing` and
`exits_only_to` in `deletable`, all speak about the computed fields
`l.(body)` and `l.(back_edges)` of the loop record `NaturalLoop.v`
builds. For the run record to describe every real execution that stays
in the loop, the back-edge list must be complete, containing every edge
into the header from a block the header dominates, and the body must be
the whole natural loop of those edges. `NaturalLoop.v` proves both
directions, in `find_loops_body`, `find_loops_complete` and
`find_loops_back_edges`, but nothing outside that file uses these
theorems. The conclusion of `find_deletions_spec` carries only the
code-stated fact that the pair is in the output of
`InductionVar.analyze`.

Two further points follow:

- Those theorems sit under the section hypotheses `blocks_closed` and
  `succs_closed`. Both hold of `Ssa.blocks`, which lists the reachable
  finished blocks and records predecessors only from reachable blocks,
  but neither is stated at the top of the development.
- `find_loops_complete` yields some loop with the given header. That the
  table has one entry per header is not a stated theorem.

The smaller fix adds a conjunct to `deletable`, say `loop_is_natural
blocks l`, stating the body and back-edge equivalences, and adds the two
closure hypotheses to `find_deletions_spec`, with a header-uniqueness
lemma. The alternative restates `run_back_edge` by meaning, as an edge
from a block the header dominates, and moves the completeness argument
into the proof. The first keeps the run record as it is and makes the
top-level statement self-contained.

### 3. Definitions shared between the code and the meaning

`IntegerComparison.eval` is used by the extracted code, in
`LoopComparisons.loop_continues` and in the termination verdict, and by
the meaning, in `machine_values.iter_op` and `AffineSsa.test_result`. A
mis-transcribed case would pass every proof and make the hypothesis
false of the machine. It is ten lines in a file whose header already
says it is a transcription of `typing/scalar.ml`, and it was checked in
this audit: the signed cases compare the values and the unsigned cases
compare their unsigned readings. The same shape applies to `wrap64`,
`unsigned64` and `in_int64` in `OxCamlInt64.v`, shared by the axioms and
the meaning. These definitions belong in the list of the trusted base in
`rocq/HACKING.md`.

## Not hazards

### Intermediate hypotheses discharged in the chain

A hypothesis stated through code is harmless when the development
itself discharges it, because nothing at the top then depends on its
truth of the program:

- `bivs_of_loop` and `biv_spec`, hypotheses of
  `LoopTermination.analyze_Terminates`, are discharged by
  `InductionVar.analyze_spec` in `analyze_Terminates_of_graph`.
- `guards_taken`, stated through `guard_test`, is the hypothesis of
  `guards_at_sound` and is discharged by `guards_taken_of_run`.
- The `ctx_wf` and counter-room preconditions of `expr_of_value`,
  `linearize` and `guards_at`, and the `wf` preconditions of
  `FourierMotzkin.v`, are discharged at their call sites.

### Conclusion-side meanings stated through code

A conclusion stated through code cannot make a theorem vacuous; it only
makes the reader open the code to learn what is claimed. The cases are
`exit_branch_to` (through `find_exit_branch`), `dead_spec` (through
`find_exit_branch`, `instr_defines_value` and `passes_at`), `biv_spec`
inside `params_are_dead_bivs` (through `classify_update`, `goto_args`,
`arg_value`, `step_same`, `sign_same` and `is_param`),
`block_does_nothing` (through `terminator_pure_control`, six lines) and
`uses_only` (through the views `args_of_instr` and `terminator_args`).
The informal justification in the header of `DeleteEmptyLoops.v` leans
on `uses_only`, which is stated through the views only. Inlining
`find_exit_branch_spec` into `exit_branch_to` is the one cheap
improvement.

### `iter_invariant`

The field is stated through `InductionVar.loop_invariant_value`, which
uses only `op_def_find` and `dominates`. Its truth of real executions
rests on the argument in its comment, that a block strictly dominating
the header is outside the body and so does not run again between two
visits, and on `Ssa_view.compute_op_def` mapping each instruction id to
its defining block, which it does for every `Op` of every block of
`Ssa.blocks`.

## The trusted base, checked for falsity

- `OxCamlInt64.v`: `of_int` is exact; `to_int` is exact on
  [-2^62, 2^62 - 1]; addition, subtraction and multiplication wrap;
  `div` needs a non-zero divisor and wraps, which covers `min_int`
  divided by minus one as OxCaml's `Int64.div` computes it; `rem` is
  `Z.rem`; `abs` and `neg` wrap; the two right shifts are specified for
  amounts 0 to 63 only, the arithmetic one as floor division and the
  logical one through `unsigned64` with `wrap64`, needed for a shift by
  zero.
- `IntArithExtract.v`: `a lxor s land (b lxor s)` parses as
  `(a lxor s) land (b lxor s)`, since `lxor` and `land` share a
  precedence level and associate to the left, and the sign-bit test is
  right; the divide-back test for multiplication excludes zero and the
  `min_int` times minus one cases before dividing.
- `IntegerComparisonExtract.v`: the constructor order is that of
  `typing/scalar.ml` (`Ceq Cne Clt Cgt Cle Cge Cult Cugt Cule Cuge`).
- `SsaModelExtract.v` and `Ssa_view`: `Block.all_successors` includes
  the exception successor, so `exits_only_to` and `single_exit` see
  handler edges; `Block.dominates` is reflexive, as the model says;
  `Ssa_view.strict_dominators` walks the immediate dominators to the
  entry; every branch of `Ssa_view.tree_of_value` puts the value at the
  root, so `tree_of_value_root` holds; the logical shift keeps no
  argument, as the model's `Ilsr` says; `compute_op_def` covers every
  `Op` of every block of `Ssa.blocks`.
- `Ssa.blocks` lists the reachable finished blocks, and predecessors are
  recorded only from reachable blocks, so `blocks_closed`,
  `succs_closed` and `entry_dominates` hold of it, and the depth
  assertion in `Block.dominates` cannot fire on any block the models
  pass it.
- `OxCamlList.compare_length_with` has no axiom and appears only in the
  two size cut-offs of `FourierMotzkin.v`, never in a `Prop`.
- `Ssa_view.value` maps `Const_mask` to `Op_other` rather than
  `Op_const`, so such constants are not seen as loop-invariant. This is
  conservative, not unsound.
- `Instruction.has_side_effect` treats loads as effect-free and polls,
  allocations and stores as effects; it is the compiler's own
  classification and is trusted as such.

## Recommended changes

1. Restate `atom_counter_fits` through `size`, `tree_of_value` and
   `strict_dominators` only, with a `guards_size` bound lemma (finding 1).
2. Add `loop_is_natural` to `deletable` and the closure hypotheses to
   `find_deletions_spec`, with a header-uniqueness lemma for the
   back-edge table (finding 2).
3. List `IntegerComparison.eval`, `wrap64`, `unsigned64` and `in_int64`
   as shared definitions in the trusted base of `rocq/HACKING.md`
   (finding 3).
4. Optionally inline `find_exit_branch_spec` into `exit_branch_to`.
