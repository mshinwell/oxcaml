# Part 22 — Termination

Back to [index](README.md).

**Summary: termination is not guaranteed.** There is no ranking function, no
well-founded measure, and no proof. What LLVM has instead is a bounded outer
loop, an unbounded inner loop, a fixpoint *verifier* used in testing, and a
body of review conventions — backed up by a steady stream of bug fixes.

This matters for a port more than almost anything else in the catalogue: the
rule set is only terminating because people keep making it so.

---

## 22.1 The two loops

```
combineInstructionsOverFunction()          // InstructionCombining.cpp:5851
  └─ while (true)                          //   OUTER: bounded
       prepareWorklist(F)                  //     re-seed from scratch, RPO
       IC.run()                            //     ─┐
                                           //      │ INNER: unbounded
InstCombinerImpl::run()                    //      │ line 5463
  └─ while (!Worklist.isEmpty())           //     ─┘
       I = Worklist.removeOne()
       if (Instruction *R = visit(*I)) { replace/mutate; re-push R and users }
```

The distinction is the whole story:

| | Outer loop | Inner loop |
|---|---|---|
| What it does | re-seed the entire function and drain again | drain the worklist |
| Bound | `Opts.MaxIterations` | **none** |
| Non-convergence looks like | missed optimisation (production) or a hard error (tests) | **the compiler hangs** |

### The outer loop is bounded — at 1

```cpp
// llvm/include/llvm/Transforms/InstCombine/InstCombine.h:29
static constexpr unsigned InstCombineDefaultMaxIterations = 1;
bool VerifyFixpoint = false;
```

The default optimisation pipeline constructs `InstCombinePass()` from C++, so
it gets these defaults: **one drain, then stop.** InstCombine in production
does not iterate to a fixpoint and does not check whether it reached one.

`parseInstCombineOptions` (`PassBuilder.cpp:1047`) flips `VerifyFixpoint` to
`true` when the pass is named in a `-passes=` string, which is how
`llvm/test/Transforms/InstCombine` runs. Reading the loop at line 5880:

* **Production** (`MaxIterations=1`, `VerifyFixpoint=false`): run one drain;
  break. Never errors, never verifies.
* **Tests** (`MaxIterations=1`, `VerifyFixpoint=true`): run a drain; if it
  changed anything, run a second; if *that* changed anything,
  `reportFatalUsageError` — "did not reach a fixpoint after 1 iterations".

So the fixpoint verifier is a **test-only tripwire for outer-loop
divergence**. It cannot catch an inner-loop cycle, because that never returns.

### Why one iteration is enough (empirically)

From the commit that made this change (`41895843b5915`, May 2023), measured
over llvm-test-suite:

| Outcome | Count |
|---|---|
| no fold performed | 411,380 |
| fixpoint after 1 iteration | 117,921 |
| needed 3 iterations | 236 |
| needed ≥ 4 iterations | 2 |

0.04% of functions need more than one iteration. The commit message is
explicit that this "does accept that we will not reach a fixpoint in all
cases", mitigated by InstCombine running 8+ times in the pipeline.

Only **13 test files** currently carry `no-verify-fixpoint`, and 9 use the
`instcombine-no-verify-fixpoint` function attribute — the complete set of
acknowledged non-convergent cases.

## 22.2 The worklist does not help

`InstructionWorklist` (`llvm/include/llvm/Transforms/Utils/InstructionWorklist.h`):

* `Worklist` is a `SmallVector` + `WorklistMap` — a **deduplicated stack**.
  `push` is a no-op if the instruction is already queued; `removeOne` pops
  from the back (LIFO).
* `Deferred` is a `SmallSetVector`, drained before the main worklist.

The dedup prevents an instruction being queued twice *simultaneously*. It does
**not** bound how many times an instruction is visited, and a rewrite that
creates a fresh instruction each round produces a fresh pointer every time.
Two rules that undo each other spin forever regardless.

## 22.3 The partial measures that do exist

A real termination proof needs a well-founded measure that strictly decreases
on every rewrite. InstCombine has three *partial* ones, none sufficient alone:

**1. Instruction count.** Most rules reduce it; the contributor guide requires
multi-use tests proving a transform "does not increase instruction count"
(guide §"Add multi-use tests"). This is what nearly all `m_OneUse` conditions
encode. But it is **non-strict** — canonicalisations preserve it exactly — so
it is at best the first component of a lexicographic order.

**2. `getComplexity`** (`InstCombiner.h:143`) — a total preorder on values:

| Value | Rank |
|---|---|
| `undef` | 0 |
| other constants | 1 |
| cast, `neg`, `not`, `fneg` | 2 |
| everything else | 3 |

`SimplifyAssociativeOrCommutative` sorts commutative operands so the
higher-ranked one is first. This *is* a strict decrease, and it is why
operand-swapping terminates — but it only orders operand positions, not rule
application.

**3. Canonical form.** The guide's canonicalisation table (`sext → zext nneg`,
`ashr → lshr`, `add → or disjoint`, `mul C → shl`, `select → and/or`, non-strict
predicate → strict, …) implicitly defines a direction for each rewrite pair.
Termination relies on **nobody implementing the reverse direction**. This is a
social constraint, enforced by code review, not by the code.

> The missing piece is a formal second lexicographic component: a rank on
> canonical forms. If you want a termination proof for a ported rule set, this
> is the thing you have to invent. LLVM never has.

## 22.4 The hand-written guards, by kind

Every one of these exists solely to break a potential cycle. Grepping the
source for loop-avoidance comments yields a clean taxonomy:

**(a) Consume-at-least-one.** `isFreeToInvert(V, _, &Consumes)` reports whether
building `~V` *removes* an existing `not`. Rules that invert both operands fire
only when at least one `not` disappears.
> `InstCombineAddSub.cpp:2429` — *"Need to ensure we can consume at least one
> of the `not` instructions, otherwise this can inf loop."*
> Bug: `abe4677d9f8ab` "Fix infinite loop due to incorrect `DoesConsume`".

**(b) `m_ImmConstant` instead of `m_Constant`.** A `ConstantExpr` operand can
be re-folded into a different `ConstantExpr`, swapping back and forth forever.
> `InstCombineAndOrXor.cpp:5208` — *"we completely avoid the fold for
> constantexprs, at least to avoid endless combine loop."*
> `InstCombineAddSub.cpp:3127` — `X - C → X + (-C)` is skipped for constant
> expressions *"because there's an inverse fold for `X + (-Y) → X - Y`."*
> Bugs: `002da67d01b23` "Require ImmConstant in shift of shift fold";
> `27eaa8a40ef33` "Prevent infinite loop with two shifts" — `(C2 << X) << C1`
> swapping `X` and `C1` forever.

**(c) Don't disturb an idiom another visitor owns.** `visitICmpInst` and
`visitFCmpInst` both bail out when their sole user is a min/max select, and
`visitSub` refuses the Negator on an `abs` shape.
> `InstCombineCompares.cpp:6897` — *"Don't break up a clamp pattern … could
> lead to conflict with select canonicalization and infinite looping."*
> `InstCombineCompares.cpp:1409` — *"Avoid an infinite loop with min/max
> canonicalization."*

**(d) Explicit "must be strictly simpler".**
> `InstCombineSelect.cpp:1372` — *"Make sure that V is always simpler than
> TrueVal, otherwise we might end up in an infinite loop."*
> `InstCombineCompares.cpp:5926` — *"Avoid infinite loops by checking if RHS
> is an identity for the BinOp."*

**(e) Backedge guards.** Pushing an operation across a loop backedge lets it
be pushed again next visit, forever.
> `InstructionCombining.cpp:1934` (`foldOpIntoPhi`) — *"Do not push the
> operation across a loop backedge. This could result in an infinite combine
> loop."*
> `InstCombineNegator.cpp:312` — *"Don't negate indvars to avoid infinite
> loops."* Bug: `48ae61470104e`.

**(f) Fold the inverse immediately.** When a rewrite creates a pattern that
another rule would revert, the code applies the reverting rule itself, in the
same step, rather than returning and risking a cycle.
> `InstCombineAndOrXor.cpp:4662` and `:4708` — *"folded back, reconstructing
> our initial pattern, and causing an infinite combine loop, so immediately
> manually fold it away"* → `freelyInvertAllUsersOf(NewLogicOp)`.
> `InstCombineCasts.cpp:2676` — *"Explicitly perform load combine to make sure
> no opposing transform can remove the bitcast in the meantime and trigger an
> infinite loop."*

**(g) Speculative construction with rollback.** The Negator builds its result
into a side list and **erases every new instruction** if the attempt fails.
> `InstCombineNegator.cpp:537` — *"We must cleanup newly-inserted
> instructions, to avoid any potential endless combine looping."*

**(h) Intra-visitor ordering.** Two rules in the same visitor can cycle if
tried in the wrong order.
> `InstCombineCompares.cpp:7660` — *"Do this after checking for min/max to
> prevent infinite looping."*

## 22.5 How well it works

`git log -i --grep='infinite loop' -- llvm/lib/Transforms/InstCombine/`:
**67 commits since 2020.** A sample:

| Commit | Cause |
|---|---|
| `27eaa8a40ef33` | `(C2 << X) << C1` swapping constant and variable forever |
| `abe4677d9f8ab` | `isFreeToInvert` reporting the wrong `Consumes` value |
| `48ae61470104e` | negating a PHI that is an induction variable |
| `9f45c5e1a65a1`, `5e2dcfe42cd4a` | select value-equivalence substitution |
| `57a8ea8553850` | insert/extract element combine |
| `002da67d01b23`, `707bb42163714` | `m_Constant` where `m_ImmConstant` was needed |

These are found by fuzzing and by users hitting compiler hangs, not by any
static check.

## 22.6 Consequences for a port

1. **Budget for a bound.** Whatever you do about proofs, put a counter on the
   inner loop. LLVM's inner loop is the one that hangs and it has no counter;
   that is a design flaw you do not have to inherit.

2. **Build the fixpoint verifier on day one.** It is cheap (re-run and compare)
   and it is the only automated check LLVM has. Enable it in tests, disable it
   in production, exactly as LLVM does.

3. **Write the canonical-form rank down.** The guide's table is a list, not an
   order. If you assign each canonical form an integer rank and require every
   non-count-reducing rule to strictly increase it, you get a genuine
   lexicographic measure `(instruction count, −canonical rank)` and a real
   termination proof. This is the single biggest improvement available over
   the LLVM design.

4. **Keep the guards when transcribing, then relax under test.** The `m_OneUse`
   and `isFreeToInvert` conditions catalogued in the other parts are frequently
   *termination* conditions rather than correctness or profitability ones, and
   the source rarely says which. Removing one without a fixpoint check is how
   you get a hang.

5. **Treat rule ordering within a visitor as load-bearing.** Part of the
   catalogue records source line numbers precisely because "this fold must run
   after that one" is sometimes the only thing preventing a cycle (§22.4(h)).
