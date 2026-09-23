# `InstructionCombining.cpp` — Part 21: the driver and shared helpers

Back to [index](README.md).

Everything the other files call "Part 12" or "Part 21" lives here. Two halves:
**the fixpoint engine** and **the opcode-independent folds**.

---

## 21.1 The fixpoint engine

### `combineInstructionsOverFunction` (line 5851)

```
repeat:
    IC.prepareWorklist(F)      // seed in reverse post-order, constant-fold,
                               // drop unreachable blocks
    IC.run()                   // drain the worklist
until nothing changed, or MaxIterations reached
```

* **`VerifyFixpoint`** (default on in the new pass manager): if the pass is
  still making changes after `MaxIterations`, it **reports a fatal error**.
  Suppressed by `instcombine<no-verify-fixpoint>` or the
  `instcombine-no-verify-fixpoint` function attribute. A port that keeps this
  discipline gets a strong guard against oscillating rules.
* Newly created instructions are added to the worklist by an
  `IRBuilderCallbackInserter`; `llvm.assume` calls are also registered with
  the `AssumptionCache` at creation.
* `LowerDbgDeclare` runs once at the start (controllable by
  `-instcombine-lower-dbg-declare`).

### `InstCombinerImpl::run` (line 5463)

Per worklist item:

1. Drain the *deferred* list, erasing trivially dead instructions.
2. Pop one instruction; erase if trivially dead.
3. **Code sinking** (`-instcombine-code-sinking`, default on): if every
   non-droppable use of `I` is in a single other block `UserParent`, and
   either `UserParent`'s unique predecessor is `I`'s block or `UserParent`
   has no successors, sink `I` there. Capped by `-instcombine-max-sink-users`.
4. Run `visit(I)`; if it returns an instruction, replace or mutate and
   re-queue.

**Rule-ordering consequences for a port:**

* Because every rewrite re-queues the result, rules do not need to be
  confluent individually — but they must not *cycle*. Most `1u` checks and
  the `isFreeToInvert` guards exist to prevent cycles, not for profitability.
* The worklist is seeded in **reverse post-order**, so operands are generally
  visited before users.

### `getComplexity` — the canonical operand order

Used by `SimplifyAssociativeOrCommutative` and by both compare visitors. The
ranking (most to least complex) is roughly: non-constant instructions >
arguments > unary operators / casts > constants. Commutative operands are
sorted so the more complex one is on the left, which is why **constants always
end up on the right** and why so many rules only match one operand order.

## 21.2 `SimplifyAssociativeOrCommutative` (line 449)

Six transformations, applied in a loop:

| # | Rule | Condition |
|---|---|---|
| A1 | order operands by complexity | commutative op — **[canon]** |
| A2 | `(A op B) op C → A op (B op C)` | associative; `B op C` simplifies |
| A3 | `A op (B op C) → (A op B) op C` | associative; `A op B` simplifies |
| A4 | `(A op B) op C → (C op A) op B` | assoc+comm; `C op A` simplifies |
| A5 | `A op (B op C) → B op (C op A)` | assoc+comm; `C op A` simplifies |
| A6 | `(A op C1) op (B op C2) → (A op B) op (C1 op C2)` | assoc+comm; both constants |

**Flag handling is the subtle part.** After any reassociation,
`ClearSubclassDataAfterReassociation` (line 348) **clears all
subclass-optional data** (`nsw`, `nuw`, `exact`, `disjoint`), preserving only
fast-math flags. The one exception is `maintainNoSignedWrap` (line 307), which
re-establishes `nsw` when both reassociated constants are known and the folded
constant arithmetic provably does not signed-overflow — for `add`, `sub`,
`mul` only.

`simplifyAssocCastAssoc` (line 364) handles constants separated by a cast:
`(op (zext (op X, C2)), C1) → (op (zext X), foldedC)`. Currently restricted to
`zext` and bitwise-logic ops, and **drops poison-generating flags** on both
the cast and the binop.

## 21.3 Distributive laws

### The relation tables

`leftDistributesOverRight(LOp, ROp)` (line 618):

| `LOp` | distributes over |
|---|---|
| `and` | `or`, `xor` |
| `or` | `and` |
| `mul` | `add`, `sub` |

`rightDistributesOverLeft` (line 639): the commutative mirror, **plus** the
rule that any bitwise-logic op right-distributes over any shift
(`(A shift C) op (B shift C) = (A op B) shift C`).

### `foldUsingDistributiveLaws` (line 1153)

Two directions, each with three outcomes:

* **Expand** `(A op' B) op C → (A op C) op' (B op C)` when **both** halves
  simplify (`simplifyBinOp`). Counted as `NumExpand`.
* **Absorb** — if one half simplifies to the *identity* of the inner opcode,
  the result is just the other half combined with `C`.
* Otherwise fall through to `SimplifySelectsFeedingBinaryOp`.

The simplify query is `getWithoutUndef()`: reasoning with `undef` here would
be unsound because the operand is duplicated.

### `tryFactorization` (line 695) / `tryFactorizationFolds` (line 1110)

The reverse direction: `(A op' B) op (A op' C) → A op' (B op C)`.
`getBinOpsForFactorization` (line 667) lets a `shl` by a constant be treated
as a `mul` (for `add`/`sub` at the top) and lets an `lshr` of a non-negative
value be treated as an `ashr` (for bitwise ops), so more pairs match.
`getIdentityValue` (line 654) supplies a missing operand when one side is a
bare value rather than a matching binop.

## 21.4 Sinking an operation into `select` / `phi`

These are cited constantly by the other parts.

| Helper | Rule | Key conditions | Line |
|---|---|---|---|
| `FoldOpIntoSelect` (line 1728) | `op (select C, A, B), X → select C, (op A, X), (op B, X)` | at least one arm must *simplify* (`simplifyOperationIntoSelectOperand`, line 1697), unless `FoldWithMultiUse`. **Refuses** if the operation could trap on the un-simplified arm and is not speculatable. Drops `prof` metadata mismatches | 1728 |
| `foldOpIntoPhi` (line 1821) | `op (phi …), X → phi (op …)` | every incoming value must let the operation *simplify* (`simplifyInstructionWithPHI`, line 1781), or there must be at most one non-simplifying predecessor into which the operation can be speculated. The predecessor's terminator must allow insertion | 1821 |
| `foldBinopWithPhiOperands` (line 2094) | both operands are PHIs in the same block → one PHI of binops | identical incoming blocks; the binop must be safe to speculate into each predecessor | 2094 |
| `foldBinOpIntoSelectOrPhi` (line 2209) | the two above, tried in order | | 2209 |
| `foldBinopWithRecurrence` (line 1991) | a binop whose operand is a simple recurrence | | 1991 |
| `SimplifySelectsFeedingBinaryOp` (line 1309) | `(select C, A, B) op (select C, D, E) → select C, (A op D), (B op E)` | same condition; at least one side must simplify | 1309 |

## 21.5 Inversion utilities

| Helper | Meaning | Line |
|---|---|---|
| `isFreeToInvert(V, WillInvertAllUses, &Consumes)` | `~V` can be formed without extra instructions. `Consumes` reports whether producing it removes an existing `not` | `InstCombiner.h` |
| `getFreelyInvertedImpl` (line 2750) | actually build `~V`; handles constants, `not`, compares, `select`, `min`/`max`, `phi`, and `xor` with an invertible constant | 2750 |
| `canFreelyInvertAllUsersOf` | every user of `V` can absorb an inversion | `InstCombiner.h` |
| `freelyInvertAllUsersOf` (line 1389) | perform that rewrite | 1389 |
| `dyn_castNegVal` (line 1442) | recognise `-V` in any spelling | 1442 |

The `Consumes` flag is what makes the `(~X) op (~Y)` rules terminate: a rule
fires only if at least one existing `not` disappears.

## 21.6 Other shared folds

| Helper | Rule | Line |
|---|---|---|
| `foldVectorBinop` (line 2276) | push a binop through matching shuffles / splats / inserts; `unshuffleConstant` (line 2239) reverses a shuffle applied to a constant | 2276 |
| `narrowMathIfNoOverflow` (line 2501) | `ext(X) op ext(Y) → ext(X op Y)` when the narrow op provably cannot overflow | 2501 |
| `foldBinOpShiftWithShift` (line 905) | `(X shift C) op (Y shift C) → (X op Y) shift C` for the cases the distributive table does not cover | 905 |
| `tryFoldInstWithCtpopWithNot` (line 800) | `ctpop(~X)` rewrites shared by `add`, `sub`, `or`, `icmp` | 800 |
| `foldBinOpOfSelectAndCastOfSelectCondition` (line 1051) | a binop of a select and a cast of the same condition | 1051 |
| `foldFBinOpOfIntCasts` (line 1646) / `…FromSign` (line 1486) | `(sitofp X) op (sitofp Y) → sitofp (X op Y)` when the integer op cannot overflow and the conversion is exact | 1646 |
| `foldBinopOfSextBoolToSelect` (line 1677) | `(sext i1 C) op Y → select C, (op -1, Y), (op 0, Y)` | 1677 |
| `matchSymmetricPair` (line 1273) | recognise two values that are the same pair in either order (including through PHIs) — used by the commutative compare canonicalisation | 1273 |
| `shouldChangeType` (line 263) | whether retyping from one width to another is desirable for this data layout (legal types, and `isDesirableIntType`, line 244) | 263 |
| `EmitGEPOffset` (line 198) / `EmitGEPOffsets` (line 219) | materialise a GEP's byte offset as integer arithmetic | 198 |

## 21.7 `visitGetElementPtrInst` (line 3079)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| G1 | `simplifyGEPInst` | | 3085 |
| G2 | `SimplifyDemandedVectorElts` | vector GEP | 3090 |
| G3 | canonicalise index types to the index type of the address space; zero out indices into zero-sized types | — **[canon]** | 3101 |
| G4 | `gep T, P, <all constant> → getelementptr i8, P, TotalOffset` | the element type is not already `i8` — **[canon]** to `ptradd` | 3126 |
| G5 | `gep → ptradd` generally | `shouldCanonicalizeGEPToPtrAdd` (line 2940) — **[canon]** | 3134 |
| G6 | scalarise splat operands of a vector GEP | | 3141 |
| G7 | `visitGEPOfGEP` (line 2624) | merge a GEP of a GEP; `shouldMergeGEPs` (line 2223) gates it, and `getMergedGEPNoWrapFlags` (line 2556) computes the **intersection** of the two no-wrap flag sets | — |
| G8 | `foldGEPOfPhi` (line 2969) | sink a GEP into a PHI | — |
| G9 | `foldSelectGEP` (line 2563) | `gep (select C, P, Q), I → select C, (gep P, I), (gep Q, I)` | — |
| G10 | `canonicalizeGEPOfConstGEPI8` (line 2590) | merge adjacent constant byte offsets | — |

## 21.8 Allocation and control-flow folds

| Helper | Rule | Line |
|---|---|---|
| `visitAllocSite` (line 3556) | remove an allocation whose only users are "non-escaping" (`isNeverEqualToUnescapedAlloc`, line 3376; `isRemovableWrite`, line 3388): stores into it, lifetime markers, comparisons against null, and the matching free | 3556 |
| `visitFree` (line 3813) | remove `free(null)`; `tryToMoveFreeBeforeNullTest` (line 3729) hoists a `free` above its null guard so the guard can be deleted | 3813 |
| `visitReturnInst` (line 3853) | drop `undef` return values | 3853 |
| `visitUnreachableInst` (line 3915) / `removeInstructionsBeforeUnreachable` (line 3888) | delete instructions that cannot have side effects before an `unreachable` | 3915 |
| `visitUnconditionalBranchInst` (line 3920) | merge trivially mergeable blocks | 3920 |
| `addDeadEdge` / `handleUnreachableFrom` / `handlePotentiallyDeadBlocks` / `handlePotentiallyDeadSuccessors` (lines 3944–4006) | the CFG-pruning side of the pass: when a branch condition becomes constant, the dead edge is removed and the newly unreachable blocks cleaned up | 3944 |
| `visitSwitchInst` (line ~4180) | narrow the switch condition to the smallest type that holds every case value | 4180 |

## 21.9 Tunables

| Option | Default | Effect |
|---|---|---|
| `-instcombine-max-iterations` | 1 (NPM default from `InstCombineOptions`) | fixpoint iteration cap |
| `-instcombine-code-sinking` | on | the sinking step in `run()` |
| `-instcombine-max-sink-users` | 32 | cap for that step |
| `-instcombine-maxarray-size` | 1024 | limit for constant-array folds (`foldCmpLoadFromIndexedGlobal`) |
| `-instcombine-negator-enabled` / `-max-depth` | on / `NegatorDefaultMaxDepth` | the Negator |
| `-instcombine-simplify-vector-elts-depth` | 10 | demanded-elements recursion |
| `-instcombine-verify-known-bits` | off | cross-check the two known-bits implementations |
| `-instcombine-max-num-phis` | 512 | `SliceUpIllegalIntegerPHI` |
| `-instcombine-guard-widening-window` | 1 | `llvm.experimental.guard` merging |

