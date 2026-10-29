# Review of the Rocq-verified empty-loop deletion

Branch `rocq-loop-proofs` at `419a3d21d8` ("Enforce loop-proof applicability
and cover guarded bounds"). Reviewer: AIDE, following
`ROCQ-REVIEWER-OBLIGATIONS.md`. Proof scripts (`Proof. ... Qed.`) were
skipped as instructed; everything else (statements, definitions, extraction
directives, the OCaml veneer, the tests) was read.

Scope, as agreed: the SSA IR and the mechanical rewrite are trusted; the
question is whether the Rocq development states and proves the right thing
about *when* a loop may be bypassed, and whether that statement actually
applies to what the compiler does.

## Status

The findings below were addressed in the follow-up commit "Address review
of the empty-loop deletion proofs", except where noted:

- R1: the simulation argument and the disjointness argument are written
  out in `ROCQ-REVIEWER-OBLIGATIONS.md` §7 and pointed to from
  `LoopEligibility.v` and `delete_empty_loops.ml`.
- F1: `SsaContext.context_step` gained `Context_trap_marker`; the gate no
  longer rejects graphs with `Push_trap`/`Pop_trap`, only the result-count
  shape. Theorem statement and axiom set unchanged. A `for` loop inside a
  live `try` is now deleted (end-to-end check in
  `testsuite/tests/backend/ssa/loop/delete_empty_loops.ml`).
- F2, F3, F7: documented in `SsaContext.v`, `SsaModel.v` (and the
  obligations document), `LoopTermination.v`, `DeleteEmptyLoops.v`.
- F4: `loop_analysis.ml` gained hand-built graphs for the shapes in
  section 6.2; `delete_empty_loops.ml` (testsuite) now observes deletion
  of the canonical shapes by processor time (2^36 iterations: ~19 s when
  kept, none when deleted) and has `try`, header-value and `Ceq` cases.
- F5: diagnosis refined; comment fixed. Not just an off-by-one: the lower
  bound of `x >>s 1` is `-2^62 = min_int`, and a fact `b + 2^62 >= 0`
  cannot be written with `int` affine constants, so
  `AffineExpr.shr_range_facts` omits it for a one-bit shift. Widening
  `bound_in_range` alone would not delete `downto` loops; left as is.
- F6: left as a known limitation (Flambda2 removes such parameters in
  practice).

Verification of the follow-up: `make -C rocq all` passes; extraction
regenerated (only `SsaSemantics.ml` changes); `Print Assumptions` for
`find_deletions_eligible` lists the same axioms as before; the unit tests
and the three testsuite programs pass natively against a compiler relinked
with the recompiled modules.

## Verdict

The theorem `LoopEligibility.find_deletions_eligible` states the right
property, its premises are discharged by the SSA builder as far as I can
tell, the extraction is faithful, and the OCaml veneer applies the judgement
as the theorem requires. I found no soundness bug in the statement, the
semantic definitions, the extraction mapping, or the pass. All findings
below are about conservativeness, documentation, or test coverage; none
blocks merging as an experimental, off-by-default pass.

The one thing a reader must accept that is *not* in Rocq is the standard
liveness-based simulation argument that turns the per-loop, per-entry
property `eligible_entry` into "the rewritten function behaves like the
original" (section 2.3 below). It is short and I checked it, but it should
be written down next to the theorem.

## 0. What I did

- Read every `.v` file's definitions and theorem statements (not proofs), the
  three `*Extract.v` files, `rocq/OxCamlExtract.v`, `rocq/IntArithExtract.v`,
  `backend/ssa/ssa.mli`, the relevant parts of `backend/ssa/ssa.ml`
  (`finish_graph`, `compute_reachability_and_trap_stacks`,
  `compute_dominators`, `check_terminator`, `check_value_invariants`,
  `Block.params/param/strict_dominators/dominates/all_successors`),
  `backend/ssa/loop/delete_empty_loops.ml(i)`, `ssa_reducer.ml(i)`, and the
  pipeline hook in `asmcomp/asmgen.ml`.
- Rebuilt all proofs from clean sources with Rocq 9.3.0
  (`make -s -C rocq all`, ~33 s) and regenerated the extracted OCaml: it is
  byte-identical to the committed `.ml`/`.mli` after `ocamlformat`.
- Ran `Check @find_deletions_eligible`, `Check @find_deletions_supported`
  and `Print Assumptions find_deletions_eligible`. No `Admitted`. The only
  global axioms are: the `SsaModel` parameters and their `*_eqb_spec`
  / block-set axioms, the `OxCamlInt64.Int64.*_spec` axioms, the four
  `IntArith.*_fits_spec` axioms, `OxCamlList.sort_uniq_{In,NoDup}`,
  Rocq's own `PrimInt63`/`Uint63Axioms`/`Sint63Axioms` axioms, and
  `Classical_Prop.classic`.
- Verified constructor order of `Operation.t`, `integer_operation` and
  `integer_comparison` against `backend/operation.mli` and
  `typing/scalar.ml`; `negate`/`swap` match `Scalar.Integer_comparison`.
- Built and ran the unit tests `oxcaml/tests/backend/ssa/loop_analysis.ml`
  and `loop_comparisons_facts.ml` natively against the current
  `compiler-libs` (both print `OK`), plus a dozen additional hand-built SSA
  graphs through `Delete_empty_loops.run` (section 6).
- Built the three testsuite programs in `testsuite/tests/backend/ssa/loop/`
  natively with `-O3 -use-ssa -ssa-delete-empty-loops -dssa`, ran them, and
  compared against the `.reference` files (all match), and checked that the
  set of functions in which a loop is deleted matches what the test
  comments claim. Also ran a differential test of 17 further OCaml
  functions with the pass on and off: identical output, deletions in the
  expected functions; a 2^59-iteration empty loop is deleted and returns
  the correct value instantly.

## 1. The statement: `eligible_entry` and `find_deletions_eligible`

`LoopEligibility.v:39`:

```coq
Definition eligible_entry (loop : natural_loop) (exit : block)
    (header_regs : registers) : Prop :=
  set_mem loop.(header) loop.(body) = true
  /\ set_mem exit loop.(body) = false
  /\ params exit = []
  /\ exists (first_header_regs exit_regs : registers),
       executes_insns header_regs (block_body loop.(header)) first_header_regs
       /\ region_steps loop.(body)
            {| current_block := loop.(header); remaining := [];
               current_registers := first_header_regs |}
            (enter exit exit_regs)
       /\ agree_on_live (entry_point exit) first_header_regs exit_regs.
```

Read against what the rewrite does (header terminator := `Goto exit` with no
arguments; header body retained; everything else untouched), this is
exactly the right per-entry obligation:

- The header body executes from `header_regs` to `first_header_regs`
  (so the rewritten header can execute it too).
- From the header's terminator with those registers, the *original* loop
  executes, staying inside `loop.(body)` except for the last step, and
  arrives at `enter exit exit_regs`. Since `exit ∉ body` and `region_steps`
  requires every *source* state to be in the body, this is the first exit,
  and it goes to `exit` (not to some other outside block). Because `step`
  is deterministic, this also excludes divergence and stuck states
  (`eligible_entry_execution`, `eligible_entry_progress`).
- `first_header_regs` and `exit_regs` agree on every register live at the
  exit's entry point. The rewritten program enters `exit` with
  `first_header_regs` (parameterless Goto writes nothing).

`find_deletions_eligible` (`LoopEligibility.v:219`) derives this for every
`(header, exit)` the extracted `find_deletions` returns, for every
`header_regs` reached from function entry through the context semantics,
under premises that are all builder metadata, no-UB (`switches_in_range`),
or trivially true of a machine (`bounded_registers`,
`live_registers_bound`). No premise mentions termination, the counter, the
bound, or guard outcomes; those are conclusions. The 2^32 block limit and
the prefix-instruction coverage, which were premises in the previous
revision, are now checked by the extracted gate `graph_supported` and read
back by `find_deletions_supported`. Good.

### 1.1 Things I specifically looked for and did not find

- A premise that smuggles in the conclusion (e.g. assuming the counter
  recurrence, bound constancy or `revisits`). None: the `Check` output lists
  only `control_edges`, `well_formed_ssa`, `control_layout`,
  `op_def_correct`, `switch_edge_multiplicity`, `dominance_semantics`,
  `dominance_complete`, predecessor/successor closure, `NoDup
  (strict_dominators header)` + membership, and the four input premises.
- A vacuous conclusion. `eligible_entry` is an existential over a
  deterministic relation, and `eligible_entry_execution` /
  `eligible_entry_progress` pin its meaning down.
- Confusion between "the exit edge from the header" and "any way out".
  `single_exit` (`DeleteEmptyLoops.v:83`) requires every successor of every
  body block to be in the body or equal to the header's exit target, and
  `region_exit_target` is what gets the final state to `enter exit _`.
- Dead-counter equality being required. Only `agree_on_live` is concluded;
  the counter is dead by `DeadInductionVar`.

## 2. Semantics versus the compiler

### 2.1 `SsaSemantics.v`

- `supported_operation` (`:34`): `Const_int []`, `Intop
  (Iadd|Isub|Icomp) [_;_]`, `Intop_imm (Iadd|Isub|Icomp) [_]`, one
  result. `eval_operation` (`:130`) wraps at 64 bits (`wrap64`), compares
  with `IntegerComparison.eval` yielding 0/1, immediates sign-extended via
  `to_Z`. Matches the CFG semantics of these ops (comparison orientation
  `arg0 cmp arg1`, `Intop_imm (Icomp c) n` = `arg0 c n`). The extra
  `modeled_operation` cases (`Ilsl/Iasr/Ilsr` by 0..63, `Ior` immediate)
  are correct: `Z.div` is floor division (arithmetic shift), `unsigned64`
  for `Ilsr`, `Z.lor` on signed `Z` is two's-complement or.
- `step` (`:205`): `Step_goto` reads all args before binding, omitted args
  bind `None`; `Step_switch` requires `0 <= n`, `nth_error targets n`, and a
  parameterless target. Boolean convention (`targets.(0)` false,
  `targets.(1)` true) is consistent with `comparison_value` and with
  `find_exit_branch`'s `[ifnot; ifso]`.
- Registers persist across blocks and are overwritten by re-execution; this
  is what makes `live_at` the right notion (2.2).
- `Const_int n` is `Int64.to_Z (Int64.of_nativeint n)`; the model never
  assumes anything about `of_nativeint`, and the affine layer only uses it
  through `int64_is_int`/`Int64.to_int` with the `to_int_exact` axiom.

### 2.2 `SsaLiveness.v`

`live_at` (`:37`) is "read at this point, or read later along some
structural point path before being redefined", with definitions at the
point after an instruction (all result indices) and at a block's entry
point (all its actual params). Point edges (`SsaDominance.v:94`) use
`all_successors`, so exceptional edges are included (conservative). I
checked the kill set against the semantics' write set: `execute_instruction`
writes `Result id 0` (and opaque instructions write exactly their declared
`Result id i`, `i < count`); `bind_parameters` writes exactly the target's
params (including `None` for omitted args, which is also a kill in
`defined_at`). Switch targets have no params. Nothing is written that is
not a definition site, and nothing is treated as a definition that is not
written. So `agree_on_live` at a point is sufficient for the continuation
to behave identically — given the simulation argument in 2.3.

### 2.3 The argument the Rocq development leaves to the reader

The theorem is per loop and per header entry, on the original graph. To
conclude that the rewritten function `P'` is observationally equivalent to
`P`, one needs the standard simulation: relate states of `P` and `P'` at the
same program point whose register files agree on `live_at^P` of that point
(same memory, trap stack, etc.). I checked the two non-obvious steps:

1. At `(header, 0)`, `P` runs the loop to `enter exit exit_regs` while `P'`
   takes `Goto exit` with `first_header_regs'` agreeing with
   `first_header_regs` on `live_at^P (header, 0)`. We need agreement on
   `live_at^P (entry_point exit)`. This follows from
   `Live_predecessor` with the edge `(header,0) -> entry_point exit`
   (`exit ∈ all_successors header`) and `~ defined_at (entry_point exit) r`
   (no params, and `result_definition_not_entry`), so
   `live_at^P (entry_point exit) ⊆ live_at^P (header, 0)`.
2. Everywhere else `P'` has a subset of `P`'s edges, so `live_at^{P'} ⊆
   live_at^P` and the invariant is preserved by identical steps.

Also needed and true but not stated by `eligible_entry`: the loop touches
neither memory nor the trap stack (follows from the whitelist and from
`step` having no such effects), so those components are equal at the exit.

**Recommendation (R1).** Write this argument (10–15 lines) in
`LoopEligibility.v`'s header or in `ROCQ-REVIEWER-OBLIGATIONS.md` §7, since
it is the bridge between the proved statement and the optimisation's
correctness. Multiple simultaneous deletions compose because reported
loops are pairwise block-disjoint (if two natural loops with distinct
headers shared a block, one header would lie in the other's body and the
inner cycle would fail `acyclic_except`); that one-paragraph argument also
belongs in `delete_empty_loops.ml`.

### 2.4 `SsaContext.v` (the unchanged prefix)

`context_step` (`:40`) is exact for `step`, lets an opaque `Op` write
arbitrary `in_int64` words to exactly its declared results, and lets a
non-pure-control terminator go to any `all_successors` target writing
arbitrary words to that target's params. With the new `graph_supported`
gate (`DeleteEmptyLoops.v:69`, `SsaSemantics.v:118`) rejecting any graph
containing `Push_trap`/`Pop_trap` or an exactly-modelled op family with a
result count other than one, every real prefix in an accepted graph is now
representable:

- no trap markers ⇒ trap stack always empty ⇒ `exn_successor = None`
  everywhere ⇒ no exceptional edges at all; a raise leaves the function;
- every instruction either steps exactly (modelled, one result, operands
  bound by SSA) or opaquely;
- every terminator either steps exactly (Goto/Switch) or opaquely
  (Call/Return/Raise/Invalid/Unreachable);
- a Switch out of range in the prefix is UB in the IR anyway.

I confirmed with the built compiler that a `for` loop inside a `try` whose
handler is live (real `push_trap` + `call … may_raise`) is now *not*
deleted, whereas in the previous revision it was while the theorem was
silent about it.

**Finding (F1, medium, conservativeness).** The gate is much stronger than
the proof needs: a function containing *any* `try … with` anywhere (even
after the loop, even unrelated) loses the optimisation entirely. Since
exceptional edges are already present in `all_successors` /
`Point_transfer`, and `Push_trap`/`Pop_trap` write no register, a
`Context_trap_marker` rule (`{b; Push_trap :: rest; rs} → {b; rest; rs}`,
same for `Pop_trap`) would cover these prefixes with a handful of extra
proof cases, and the gate could keep only the result-count check. I
suggest doing this before the pass is enabled by default; `try` is common
in exactly the kind of code with small loops.

**Note (F2, low).** `opaque_outputs` requires every observed word to be
`in_int64`. A vector-typed (`Vec128/256/512`) result or block param in the
prefix has no faithful word observation; the theorem still applies if one
reads the abstraction as "assign such registers an arbitrary in-range
word", which is harmless because typing prevents any modelled op from
reading them and the loop cannot write them. Worth one sentence in
`SsaContext.v`.

### 2.5 `SsaProgress.v`

`control_layout` (`:22`) and `switches_in_range` (`:42`) read correctly:
`Omitted_since_unused` ⇒ the parameter has no operand use anywhere in the
graph (`check_value_invariants` enforces `usage_count = removal_sentinel`,
which means never used as an instruction or terminator operand);
`switches_in_range` is the IR's "out-of-range index is UB", assumed only
along the exact-semantics execution from the reached header onward.

## 3. Builder premises (`ssa.ml`)

Checked, trusting the SSA code but confirming each premise has a concrete
enforcer:

| Premise | Where it comes from |
|---|---|
| `entry_in_graph`, `graph_blocks_reachable`, `graph_successors_closed`, predecessor/successor closure | `compute_reachability_and_trap_stacks` (forward search over exactly `all_successors`; `blocks` = visited) |
| `control_edges` incl. `switch_edge_multiplicity` | same function: one `add_pred_to` per target occurrence |
| `parameter_layout` | `Block.params`/`Block.param` construct `Block_param (b, i)` positionally |
| `result_sites_unique` | fresh `Instruction.Id` per `emit_op`, bodies appended once |
| `operand_definitions` (strict point dominance), `terminator_definitions` | `check_value_invariants`: block dominance via `Block.dominates`, within-block order via the dominators-first walk and the definition table |
| `control_layout.goto_parameter_layout` | `check_terminator` (arity) + `check_value_invariants` (omitted ⇒ sentinel) |
| `control_layout.switch_parameterless` | `check_target_has_no_params` at `finish_block` |
| `dominance_semantics`, `dominance_complete` | `compute_dominators` (standard iterative idom); `Block.dominates` walks the idom chain |
| `NoDup (strict_dominators h)`, membership | `Block.strict_dominators` walks the idom chain to the entry with strictly decreasing depth |
| `op_def_correct` | `compute_op_def` over `Ssa.blocks ssa`, the same list passed to `find_deletions` |

**Note (F3, info).** `control_edges` and `dominance_semantics` quantify over
*all* `block`s with no `In blocks` guard. They are literally true only if
the Rocq type `block` is read as "the reachable blocks of this finished
graph": pruned unreachable block objects would violate the `<-` direction
of `predecessor_successor`, and `Block.dominates` on them asserts. Since no
reachable block references an unreachable one, this reading is consistent,
but `SsaModel.v` should say so.

## 4. Extraction and trusted primitives

- `SsaModelExtract.v`: the custom match functions preserve `id`, `op`,
  `args` (as list), result index, `Array.length typ`, target order,
  `Omitted_since_unused`; `Call`/`Invalid` keep their `args` arrays.
  Equalities map to `Ssa.Block.equal` (physical), `Ssa.Value.equal`
  (physical `op_data` + index), `Instruction.Id.equal`; block sets to
  `Block.Set` (by id). The axioms `value_eqb_spec` etc. hold for one
  graph's canonical values because `id ↔ op_data` is a bijection there.
- `Operation.v`/`IntegerComparison.v`: constructor orders verified.
- `OxCamlExtract.v`: `OxCamlList.fold_left` is defined with OCaml's argument
  order; `sort_uniq` ⇒ `List.sort_uniq Int.compare`; `Sint63.ltb/leb` ⇒
  `(<)`/`(<=)` on `int`. Fine.
- `IntArithExtract.v`: `add_fits` (sign trick, correct precedence:
  `(a lxor s) land (b lxor s)`), `mul_fits` (zero and `min_int * -1`
  handled, divide-back check). Correct.
- `OxCamlInt64.v` axioms match the documented behaviour of `Int64`
  (`shift_right` = floor division for 0..63, `shift_right_logical` on the
  unsigned reading, `to_int` exact on 63-bit range, `div`/`rem`
  truncating).
- Constants: `max_nodes = 256`, `max_shift_bits = 16`, `word_bits = 64`,
  `max_atoms = 64`, `max_ineqs = 500`, `graph_block_limit = 2^32` all
  appear as the same literals in the extracted code.
- Extraction is reproducible (byte-identical).

## 5. The OCaml side of the pass

`delete_empty_loops.ml` analyses the finished graph and the `op_def` table
built from the same `Ssa.blocks`, then rewrites only the reported headers'
terminators to `Continue { Goto exit; args = [||] }` through
`Context.map_terminator`; the body becomes unreachable and the output
graph's `finish_graph` prunes it and the header's now-dead pure
instructions (`keep_unused_ops = false`). Header params that become unused
are fed `Omitted_since_unused`, which is consistent with the model. Per-loop
application composes (see 2.3). I have no concerns here.

## 6. Tests

### 6.1 What exists

- `testsuite/tests/backend/ssa/loop/delete_empty_loops{,_exits,_shapes}.ml`:
  good coverage of positive shapes (`for`, both-variable bounds, two back
  edges, self tail call, countdown) and negative ones (side effects,
  comparison live-out, extra exits, raise, bounds check, nested, variable
  step, `<>`, float). All three pass natively here and the per-function
  deletion claims in the comments are accurate.
- `oxcaml/tests/backend/ssa/loop_analysis.ml`: hand-built graphs for
  diamond/inner-cycle/irreducible bodies, whitelist checks at header and
  latch, loads before the loop, opaque-call prefix, trap-handler prefix
  (gate), zero-/two-result `Const_int` (gate), `length_at_most`, register
  bounds with guards and duplicate-target guards, linearizer budget.

### 6.2 Gaps

**Finding (F4, medium, test strength).** The testsuite tests only compare
program output. The claims "deleted"/"kept" in their comments are not
checked by the test harness; a regression that silently stopped deleting
(or started deleting the wrong loop with no observable effect for the given
inputs) would pass. Suggest asserting deletion counts: either a
`-dssa`-based expect test or additional cases in `loop_analysis.ml` built
from the same shapes.

Shapes I probed that are not in the tests (results from my runs; all
consistent with the proof's intent):

| Shape | Result |
|---|---|
| Header entered via a `Call` continuation (counter = call result) | deleted |
| Header exits to a parameterless trampoline that then does `goto b(k)`, `k` a header constant, `b` returning its param | deleted (the trampoline is the exit; `k` is live-out and invariant) |
| Header `Switch` with duplicate targets, exit test in latch | kept |
| Second BIV with loop-invariant *variable* step, dead | kept (see F6) |
| Step 0 | kept |
| `Isub min_int` step | kept |
| `Ceq` continue test, step 1 | deleted |
| `Cult` test | kept |
| Header computes invariant value returned after the loop | deleted; output correct |
| Header computes IV-dependent value returned after the loop | kept |
| Two sequential loops sharing an exit | both deleted |
| Loop 1 exits into the parameterless header of loop 2 | loop 1 deleted |
| `try … with` with a live handler around the loop | kept (gate) |
| `wrap2`: `while i < n do i += 2` with unconstrained `n` | kept (correct: genuinely non-terminating for `n = max_int`) |
| 2^59-iteration empty loop whose result depends only on bound/start | deleted, correct result, instant |

Suggested additions to the testsuite: the `try`/gate case end-to-end, the
header-invariant live-out case, the shared-exit case, a `Ceq` loop, and a
check that the three existing files' deletion counts are what the comments
say.

## 7. Other findings

**F5 (low, incompleteness + misleading comment).** `spin_downto` in
`delete_empty_loops.ml` is kept, and the comment said the increment "could
wrap below `min_int` … for an arbitrary 64-bit bound register". The bound
is `>>s 1`-shaped, exactly like the `upto` case that *is* deleted. Two
things stop the negative-step case: `LoopComparisons.bound_in_range`
(`:166`) requires `-ocaml_max_int <= b` where `-ocaml_max_int - 1 <= b`
would do (`iv >= b >= -2^62` and `step >= -2^62` give `iv + step >=
-2^63`); and, more fundamentally, the lower bound `-2^62` of a one-bit
arithmetic shift cannot be stated as an affine fact with `int` constants,
so `AffineExpr.shr_range_facts` omits it. Fixing the comparison alone would
not make `downto` loops deletable.

**F6 (low, incompleteness).** A header parameter fed by
`Omitted_since_unused` on every edge (a dead accumulator whose update
`finish_graph` already pruned) is not a BIV, so `loop_is_useless` fails and
the loop is kept. Flambda2 usually removes such parameters earlier (my
source-level `dead_acc` *was* deleted), but graphs built directly show the
limitation. Treating an all-omitted parameter as trivially dead would be a
small extension; its register is `None` and never read.

**F7 (low, doc).** `LoopTermination.bound_in_range (Const_bound k)` tests
`k <=? max_int`, a tautology for an OCaml `int`; harmless, but a comment
should say the content is entirely in `continue_terminates` for literal
bounds. `DeleteEmptyLoops.v` header: "a induction variable" (typo).

**F8 (info).** `switches_in_range` is only assumed from the header onward
under the *exact* semantics; a Switch in the prefix with an out-of-range
index is UB in the IR, so nothing is lost. The obligations document says
this correctly.

**F9 (info).** `is_loop_invariant` accepts `Const_float`/`Const_symbol`/
vector constants as invariant. Correct (they are constants) and they can
only be reached as opaque atoms.

## 8. Summary of recommendations

1. (R1) Document the simulation argument (2.3) and the disjointness
   argument for multiple deletions.
2. (F1) Replace the trap-marker part of `graph_supported` by a
   `Context_trap_marker` rule, so functions with exception handlers keep
   the optimisation; keep the result-count part of the gate.
3. (F4) Make the testsuite assert deletion counts, and add the cases in 6.2.
4. (F5) Fix the `spin_downto` comment or the negative-step range check.
5. (F2, F3, F7) Small documentation touches in `SsaContext.v`,
   `SsaModel.v`, `LoopTermination.v`, `DeleteEmptyLoops.v`.
6. (F6) Optional: accept all-omitted header parameters as dead.

---

# Part II: can the structure be simplified for human review?

The question is what a human has to read to be convinced, and whether the
development could be arranged so that this is less. I measured rather than
guessed: I printed every constant of the 33 non-extraction modules
(`Print`, 763 constants: 461 lemmas/theorems, 302 definitions/inductives)
and computed two closures: the *proof cone* of `find_deletions_eligible`
(everything its proof term mentions, transitively) and the *statement
closure* (everything its type mentions, transitively through definition
bodies only, never through proofs).

## What the numbers say

| Class | Count | Needs human review? |
|---|---|---|
| Lemmas and theorems in the proof cone | 439 of 461 | No: checked by Rocq. Only the final theorem's statement matters. |
| Lemmas and theorems outside the cone | 22 | No; they are dead or sanity theorems (list below). |
| Definitions in the statement closure that are *the algorithm* (reachable from `find_deletions`/`InductionVar.analyze`) | 155 | Only for extraction fidelity (the `.ml` is what runs), not for meaning: the theorem holds for whatever they compute. |
| Definitions in the statement closure that give the theorem its *meaning* | **54** (+ the `SsaModel.v` parameters/axioms and the `*Extract.v` mappings) | **Yes.** This is the whole semantic trusted surface. |
| Definitions used only inside proofs | 80 | No. |
| Definitions outside the cone | 13 | No; dead. |

The 54 semantic definitions are, by file: `SsaSemantics` (20: `register`,
`registers`, `write_register`, `read_values`, `read_arguments`,
`bind_parameters`, `comparison_value`, `modeled_operation`, `eval_operation`,
`execute_instruction`, `state`, `enter`, `step`, `steps`, `executes_insns`,
`bounded_registers`, `parameter_layout`, `is_trap_marker`, `register_eqb`,
`register_of_value`), `SsaDominance` (8: `path`, `dominance_semantics`,
`point`, `entry_point`, `point_edge`, `point_path`, `point_dominates`,
`point_reachable`), `OxCamlInt64` (5: `wrap64`, `unsigned64`, `in_int64`,
`two63`, `two64`), `SsaLiveness` (4), `SsaContext` (4), `SsaProgress` (4),
`SsaExecution` (3: `result_definition`, `value_definition`,
`well_formed_ssa`), `SsaGraph` (3: `control_edges`,
`switch_edge_multiplicity`, `op_def_correct`), `IntegerComparison.eval`,
`LoopExecution.region_steps`, `LoopEligibility.eligible_entry`. About 700
lines of Rocq, spread over 11 files that total 4,500 lines with their
lemmas.

So the development is already in good shape in one respect: almost nothing
is dead, and the meaning of the result rests on a small set of definitions.
The problem is presentational: that set is not identified anywhere, it is
interleaved with 3,500 lines of proof-only material, and the documentation
(each file's "review parts 1 and 2 by eye", and `ROCQ-REVIEWER-OBLIGATIONS.md`
§6) still directs reviewers to the Part-2 "intended meaning" predicates
(`biv_spec`, `dead_spec`, `deletion_certificate`, `loop_invariant_value`,
`reaches`, `op_semantics`, `loop_exits`, `entails_sound`, ...). Those were
the specification when the result was a collection of per-analysis
certificates; since the operational theorem was added they are internal
lemmas, and reviewing them is wasted effort. Of the 80 proof-only
definitions, 29 are such former specifications.

## Recommendations, in order of payoff

### S1. Take the natural loop out of the statement (medium effort, large payoff)

`find_deletions_eligible` concludes `exists loop bivs, In (loop, bivs)
(InductionVar.analyze defs blocks) /\ header = loop.(header) /\ ... eligible_entry
loop exit header_regs`. The `bivs` are not used at all, and `loop` is used
only for `loop.(body)` in `region_steps` and the two `set_mem` conjuncts.
This drags `InductionVar.analyze`, `find_loops`, `natural_loop_body`,
`walk`, `add_back_edge` and the `biv` record into the statement: a
reviewer who takes the statement literally must understand the loop
discovery algorithm to know what is being claimed.

The body is only there to pin "the first arrival at `exit`". That can be
said directly:

```coq
(* [steps_until target s t]: [t] is the first state of the execution
   from [s] whose block is [target]. *)
Inductive steps_until (target : block) : state -> state -> Prop :=
  | Until_here : forall s, current_block s = target -> steps_until target s s
  | Until_step : forall s s' t, current_block s <> target ->
      step s s' -> steps_until target s' t -> steps_until target s t.

Definition eligible_entry (header exit : block) (header_regs : registers) :=
  params exit = []
  /\ exists first_header_regs exit_regs,
       executes_insns header_regs (block_body header) first_header_regs
       /\ steps_until exit {| current_block := header; remaining := [];
                              current_registers := first_header_regs |}
                          (enter exit exit_regs)
       /\ agree_on_live (entry_point exit) first_header_regs exit_regs.
```

and the theorem concludes `eligible_entry header exit header_regs` with no
existential. This is implied by the current result (`region_steps` with
`exit ∉ body` is a `steps_until`; `region_steps_execution` is the proof
already), so it is a wrapper plus a renaming, and it removes ~30
definitions and the whole of `NaturalLoop`/`InductionVar` from the
statement closure. The simulation argument (§7 of the obligations
document) needs nothing more than this. If "and it stays inside the loop"
is wanted as extra information, it can be a separate corollary.

### S2. Bundle the graph premises into one named contract (low effort, large payoff)

The theorem has eleven graph premises (closure of predecessors and
successors, `dominance_semantics`, `dominance_complete`, `control_edges`,
`well_formed_ssa`, `control_layout`, `op_def_correct`,
`switch_edge_multiplicity`, `NoDup (strict_dominators header)`, membership
of strict dominators), four of them hidden as `Section` hypotheses. A
single record

```coq
Record finished_graph (blocks : list block) (entry : block) (defs : op_def) : Prop := { ... }
```

with one documented field per guarantee of `Ssa.finish_graph` would make the
theorem a five-line statement, make the Section unnecessary, and give the
compiler-side review (obligations §3) one definition to check against
`ssa.ml`. Likewise a record `defined_inputs initial_regs header_regs` for
the four input premises.

### S3. Separate specification from proof, physically (medium effort, large payoff)

Put the 54 semantic definitions (plus `SsaModel.v`, which already is one)
into files that contain no lemmas, and say so in their headers:

- `SsaModel.v` — the interface (as now);
- `SsaSpec.v` — registers, `step`, `steps`, `executes_insns`, `context_step`,
  `live_at`, `agree_on_live`, points and point dominance, `well_formed_ssa`,
  `control_layout`, `control_edges`, `switch_edge_multiplicity`,
  `op_def_correct`, `dominance_semantics`, `bounded_registers`,
  `live_registers_bound`, `switches_in_range`;
- `LoopEligibility.v` — `eligible_entry`, `steps_until` and the final theorem,
  nothing else.

Then the reviewer's instruction is: read `SsaModel.v`, `SsaSpec.v`, the
final theorem, and the `*Extract.v` files; everything else is either the
algorithm or a proof. The present mixing (e.g. `SsaSemantics.v` is 30
definitions and 34 lemmas; `SsaGraph.v` has the algorithm's
`acyclic_except`, the contract `control_edges` and the proof-only
`region_edge` side by side) is what makes the "what must I read" question
hard today.

### S4. Retire the certificate layer from the review path (low effort)

Demote `biv_spec`, `dead_spec`, `deletion_certificate`, `loop_graph_properties`,
`loop_invariant_value`, `reaches`, `body_sound`, `op_semantics`,
`test_result`, `guards_taken`, `loop_continues`, `iv`, `bound_in_range`
(LoopComparisons) and the `*_spec` theorems that produce them from "Part 2:
the intended meaning" to the lemma sections, and rewrite the per-file
reading guides, which currently say "Parts 1 and 2 are the part to check by
eye" for files whose Part 2 nobody needs to check. Update obligations §6
accordingly: it should say that nothing in those files needs reading.

Keeping them as lemmas is fine (they structure the proof); the point is to
stop presenting them as trusted.

### S5. Delete what is dead (low effort)

Outside the proof cone: definitions `SsaGraph.block_effect_free`,
`block_does_nothing`, `switch_operand`; `SsaSemantics.defined_value`,
`unique_definitions`, `return_state`; `SsaDominance.edge_on`;
`LoopTermination.bool_to_Z`, `bound_value`; `FourierMotzkin.add`, `neg`,
`sub` (the unchecked variants); lemmas `edge_on_every_path`, `path_edge_to`,
`block_effect_free_spec`, `block_eqb_neq`, `defined_value_identity`,
`executes_insns_deterministic`, `steps_trans`, `return_has_no_step`,
`add_wf`, `neg_wf`, `sub_wf`, `two62_pow`, `pow2_bounds`, `wrap64_unsigned`,
`filter_map_NoDup_keys`, `filter_map_keys_In`, `op_semantics_lsr_zero`.
With `block_effect_free` gone, the `has_side_effect` observer can leave
`SsaModel.v` and `SsaModelExtract.v`: one trusted mapping fewer.
`infinite_execution`, `stays_in_region`, `no_infinite_execution_in`,
`step_deterministic`, `region_exit_not_infinite` and `region_exit_progress`
serve only the two sanity theorems `eligible_entry_execution` and
`eligible_entry_progress`, which explain what `eligible_entry` rules out;
keep those if the explanation is wanted, but mark them as such.

### S6. One arithmetic semantics (low effort, maintenance)

`AffineSsa.op_semantics` restates the arithmetic of
`SsaSemantics.eval_operation` (eight clauses, same content);
`LoopValueSnapshot` then proves they agree. Defining
`op_semantics v := eval_operation op (map mval args) = Some (mval v)` for
the recognised shapes would remove the duplicate. It is proof-internal now,
so this is for maintainers rather than reviewers, but a reviewer who does
open `AffineSsa.v` currently finds a second semantics and has to wonder
which one is authoritative.

### S7. Make the trusted surface machine-checked, so it stays small (low effort)

The closures above took a 40-line script over `Print` output. A
`make -C rocq surface` target that prints the statement closure of the
final theorem, with the algorithm's constants filtered out, would turn
"what must a human read" into a reproducible list, and would show
immediately when a change enlarges it. (The existing `assumptions` target
answers a different question: axioms, not definitions.)

### Optional, smaller

- `op_def` could be computed in Rocq from `blocks` instead of being built
  by the veneer and constrained by `op_def_correct`: one premise and one
  piece of trusted OCaml fewer, at the cost of an association-list lookup
  or an axiomatised table like `blockset`.
- `strict_dominators` could be `filter (strictly_dominates · header) blocks`
  computed in Rocq rather than an observer, removing one `SsaModel`
  parameter and two premises; the order of the list only affects atom
  numbering.
- `LoopComparisons.bound_in_range` and `LoopTermination.bound_in_range` share
  a name with different types; rename one.

## What I would not change

- The decision to state the theorem on the original graph rather than
  model the rewrite and the reducer. Modelling the rewrite would move the
  simulation argument into Rocq but would add the reducer's block/value
  maps, parameter dropping and dead-code pruning to the trusted model; the
  present "retained header, first exit, live-out agreement" statement is
  shorter to check than that model would be.
- The eight operational proof files. Their decomposition (traversal to the
  next header or exit; invariance; counter arithmetic; snapshot valuation;
  guard outcomes; range facts; live-out; assembly) is reasonable proof
  engineering, and with S3/S4 a reviewer never opens them.
- The whitelist and the gate as the way to bound what the semantics must
  model.

## Effort estimate

S2, S4, S5, S7: a day in total. S1: a day (new definition, wrapper
theorem, documentation). S3: two days (moving definitions across files
and fixing imports; no proof changes). S6: a day of proof repair in
`LoopValueSnapshot.v`. All are independent of each other.
