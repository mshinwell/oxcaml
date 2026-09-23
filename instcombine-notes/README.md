# InstCombine Peephole Rule Catalogue

A rule-by-rule inventory of `llvm/lib/Transforms/InstCombine/`, written for two
purposes:

1. **Proving the rules correct** (e.g. in Alive2/Coq/Lean, or by hand).
2. **Porting them to another compiler.**

Source: LLVM 21.1.0, tree at `llvm/lib/Transforms/InstCombine/`.

## Contents

| Part | Source | File |
|---|---|---|
| 1–2 | `InstCombineAddSub.cpp` — integer `add`, `sub` | [01-addsub-integer.md](01-addsub-integer.md) |
| 3 | `InstCombineAddSub.cpp` — `fadd`, `fsub`, `fneg` | [02-addsub-float.md](02-addsub-float.md) |
| 4 | `InstCombineNegator.cpp` | [03-negator.md](03-negator.md) |
| 5 | `InstCombineMulDivRem.cpp` — `mul` | [04-mul.md](04-mul.md) |
| 6 | `InstCombineMulDivRem.cpp` — `fmul` | [05-fmul.md](05-fmul.md) |
| 7 | `InstCombineMulDivRem.cpp` — `udiv`, `sdiv` | [06-idiv.md](06-idiv.md) |
| 8–9 | `InstCombineMulDivRem.cpp` — `fdiv`, `urem`, `srem`, `frem` | [07-fdiv-rem.md](07-fdiv-rem.md) |
| 10 | `InstCombineShifts.cpp` | [08-shifts.md](08-shifts.md) |
| 11a | `InstCombineAndOrXor.cpp` — shared helpers | [09-andorxor-shared.md](09-andorxor-shared.md) |
| 11b | `InstCombineAndOrXor.cpp` — `visitAnd`/`visitOr`/`visitXor` | [10-andorxor-visitors.md](10-andorxor-visitors.md) |
| 11c | `InstCombineAndOrXor.cpp` — logic of comparisons | [11-andorxor-cmps.md](11-andorxor-cmps.md) |
| 12 | `InstCombineCasts.cpp` | [12-casts.md](12-casts.md) |
| 13a | `InstCombineCompares.cpp` — `icmp` framework, `icmp X, C` | [13-icmp-constants.md](13-icmp-constants.md) |
| 13b | `InstCombineCompares.cpp` — `icmp`, general | [14-icmp-general.md](14-icmp-general.md) |
| 13c | `InstCombineCompares.cpp` — `fcmp` | [15-fcmp.md](15-fcmp.md) |
| 14 | `InstCombineSelect.cpp` | [16-select.md](16-select.md) |
| 15, 19 | `InstCombinePHI.cpp`, `InstCombineAtomicRMW.cpp` | [17-phi-atomicrmw.md](17-phi-atomicrmw.md) |
| 16 | `InstCombineVectorOps.cpp` | [18-vectorops.md](18-vectorops.md) |
| 17 | `InstCombineLoadStoreAlloca.cpp` | [19-loadstorealloca.md](19-loadstorealloca.md) |
| 18 | `InstCombineCalls.cpp` | [20-calls.md](20-calls.md) |
| 20 | `InstCombineSimplifyDemanded.cpp` | [21-simplifydemanded.md](21-simplifydemanded.md) |
| 21 | `InstructionCombining.cpp` — driver and shared helpers | [22-driver.md](22-driver.md) |
| 22 | **Termination** — why the rule set converges (and when it does not) | [23-termination.md](23-termination.md) |

All 17 source files are covered. Cross-references of the form "Part 12" or
"Part 21" for shared helpers point at
[22-driver.md](22-driver.md).

---

# Part 0 — Preliminaries

Everything below depends on a handful of LLVM-IR semantic notions. Get these
right first; most "surprising" side conditions in the rule list are consequences
of them rather than of arithmetic.

## 0.1 Poison and `undef`

* **`poison`** is a value that taints: almost any instruction with a poison
  operand yields poison. It justifies *refining* a program (replacing a
  well-defined value with poison is illegal; replacing poison with anything is
  legal). Every rule below must be read as: *the new value is at least as
  defined as the old one, for every input.*
* **`undef`** is the older, weaker notion (each *use* may independently observe
  a different value). LLVM is migrating away from it, but several rules still
  guard against it explicitly via `isGuaranteedNotToBeUndef`, because a rule
  that duplicates a use of an `undef` value is unsound (two uses could read
  different bits).
  - Example: `SimplifyAddWithRemainder` bails out unless
    `isGuaranteedNotToBeUndef(X)`, because it rewrites `X` into two new uses.
* **Practical porting note:** if your IR has no poison (all operations total),
  every `nsw`/`nuw`/`exact`/`disjoint` side condition below simply becomes
  *unavailable*, and the corresponding rules must be dropped or re-proved under
  wrapping semantics.

## 0.2 Poison-generating flags

| Flag | On | Meaning (result is `poison` if violated) |
|---|---|---|
| `nsw` | `add sub mul shl trunc` | signed overflow / signed truncation loses bits |
| `nuw` | `add sub mul shl trunc` | unsigned overflow / unsigned truncation loses bits |
| `exact` | `udiv sdiv lshr ashr` | a nonzero remainder / a shifted-out nonzero bit |
| `disjoint` | `or` | the operands have a bit set in common |
| `nneg` | `zext` | the operand is negative when read as signed |
| `samesign` | `icmp` | the operands differ in sign |
| `inbounds` | `getelementptr` | the arithmetic leaves the allocated object |

Two directions matter and are easy to conflate:

* **Consuming a flag** (the rule requires `nsw` on an input): sound, because the
  premise lets you assume no overflow.
* **Producing a flag** (the rule puts `nsw` on the output): a *proof obligation*
  — you must show the new operation genuinely cannot overflow, otherwise you
  introduce poison that did not exist. Most of the trickiest LLVM bugs in this
  pass have been mis-set output flags.

The catalogue records flag transfer explicitly wherever the code does.

## 0.3 The one-use condition (`m_OneUse`)

`m_OneUse(P)` requires the matched value to have exactly one use. This is
**almost always a profitability condition, not a correctness condition**: it
stops the rewrite from duplicating computation when the intermediate value is
still needed elsewhere. When porting, you may relax or re-tune these freely; when
proving, you may ignore them.

The exception is where one-use stands in for "this value is consumed, so we may
replace it with something less defined" — rare, and noted where it occurs.

## 0.4 Commutative matching

* `m_c_Add(A, B)` matches both operand orders; likewise `m_c_And`, `m_c_Or`,
  `m_c_Xor`, `m_c_Mul`, `m_c_FAdd`, `m_c_FMul`, `m_c_ICmp` (which also swaps the
  predicate), `m_c_BinOp`, `m_c_UMin`, etc.
* Rules written with `m_c_` therefore stand for 2^k rules. The catalogue writes
  the canonical order and marks it **[comm]**.
* Operand *canonicalisation* (`SimplifyAssociativeOrCommutative` and the
  complexity ranking in `getComplexity`) runs first and guarantees, e.g., that
  constants sit on the RHS. Many rules only match one order because of this,
  so a port needs the same canonicalisation to get the same coverage.

## 0.5 Constant matchers

| Matcher | Meaning |
|---|---|
| `m_APInt(C)` | scalar constant, or vector splat; binds the `APInt` |
| `m_Constant(C)` | any constant, incl. non-splat vectors and `ConstantExpr` |
| `m_ImmConstant(C)` | a constant that is *not* a `ConstantExpr` (no relocations / no folding hazards) |
| `m_SpecificInt(N)` | exactly that value |
| `m_SpecificIntAllowPoison(N)` | that value, but vector lanes may be `poison` |
| `m_Power2(C)` | `C` is a power of two |
| `m_NegatedPower2(C)` | `-C` is a power of two |
| `m_LowBitMask(C)` | `C` is `2^k - 1` |
| `m_One`, `m_Zero`, `m_AllOnes` | 1, 0, -1 |

`m_SpecificIntAllowPoison` matters for vectors: a rule allowing poison lanes in
the *matched* constant must not rely on the value of those lanes in the result.

## 0.6 Analysis-backed side conditions

Several rules are conditioned on a dataflow query rather than a syntactic
pattern. These are the ones a port most often lacks:

| Query | Meaning |
|---|---|
| `computeKnownBits(V)` | per-bit "known zero"/"known one" lattice |
| `MaskedValueIsZero(V, M)` | all bits of `M` are known zero in `V` |
| `ComputeNumSignBits(V)` | number of leading bits equal to the sign bit |
| `isKnownNonZero(V)` | `V != 0` on all paths reaching here |
| `haveNoCommonBitsSet(A, B)` | `A & B == 0` |
| `willNotOverflowSignedAdd(A, B, I)` | proves `nsw` may be added |
| `willNotOverflowUnsignedAdd(A, B, I)` | proves `nuw` may be added |
| `isFreeToInvert(V)` / `getFreelyInverted(V)` | `~V` costs no extra instruction |
| `isGuaranteedNotToBeUndef(V)` | safe to duplicate the use |

These are *context-sensitive*: they consult dominating conditions, `llvm.assume`,
and the instruction's position. Porting a rule without the matching analysis
strength will silently lose coverage (which is safe) — but porting the *rule*
while approximating the *query* in the unsound direction is a correctness bug.

## 0.7 Reading order

`InstCombine` is a fixpoint worklist pass, not an ordered rewrite sequence. Each
`visitXxx` runs top to bottom and returns as soon as one rule fires; the
rewritten instruction goes back on the worklist. So:

* Rules are tried in source order — **order is a tie-break, not a semantic
  property**, but it does determine which of two overlapping rules wins.
* Every `visitXxx` starts by calling the corresponding `simplifyXxxInst` from
  `InstructionSimplify.cpp` — the *identity/absorbing-element* folds that return
  an existing value rather than building a new instruction. Those live outside
  this directory and are catalogued separately (see Part 99, TODO).
* Canonicalisations (rules that do not reduce instruction count but move toward
  a normal form) are marked **[canon]**. A port that omits them will find later
  rules stop matching.

---

# Part 99 — Using this for proofs and for porting

## What is *not* here

* **`InstructionSimplify.cpp`.** Every `visitXxx` starts by calling
  `simplifyXxxInst`, which handles identities, absorbing elements and
  anything that returns an *existing* value rather than building a new
  instruction (`X + 0`, `X & X`, `X udiv X`, …). Those rules live in
  `llvm/lib/Analysis/InstructionSimplify.cpp` and are a separate catalogue.
* **`ValueTracking.cpp`.** `computeKnownBits`, `ComputeNumSignBits`,
  `isKnownNonZero`, `computeKnownFPClass`, `matchSelectPattern`,
  `decomposeBitTest` and the overflow predicates are all analyses, not
  rewrites. Their *interfaces* are catalogued in
  [Part 0 §0.6](#06-analysis-backed-side-conditions); their implementations
  are not.
* **Target-specific intrinsic folds** reached through
  `targetInstCombineIntrinsic`.
* **`LibCallSimplifier`**, reached from `tryOptimizeCall`.

## Suggested order for a correctness effort

1. **Fix the semantics first** — Part 0. Every side condition in the
   catalogue is stated against LLVM's poison/`undef`/flag model. If your
   target model differs, most rules change meaning rather than merely losing
   applicability.
2. **Do the bit-code machinery** ([11c §0(b)](11-andorxor-cmps.md)). One
   proof covers dozens of comparison rules.
3. **Do the range machinery** (`ConstantRange`, used by
   `foldAndOrOfICmpsUsingRanges`, `foldICmpAddConstant`, `foldICmpDivConstant`,
   `foldICmpUSubSatOrUAddSatWithConstant`, `foldXorOfICmps`). Another large
   family from one proof.
4. **Then the flag-sensitive arithmetic** — [Parts 1–2](01-addsub-integer.md),
   [5](04-mul.md), [7](06-idiv.md), [10](08-shifts.md). These are where
   incorrect flag *production* has historically caused miscompiles, so they
   repay per-rule verification. Alive2 covers this class directly.
5. **FP last** — [Parts 3](02-addsub-float.md), [6](05-fmul.md),
   [8](07-fdiv-rem.md), [13c](15-fcmp.md). The FMF intersection rules
   (§3.0) are the part most worth re-deriving rather than transcribing.

## Rules whose side conditions are worth extra scrutiny

Collected from the notes above; these are the places where the code
documents an asymmetry, a near-miss, or an explicitly rejected dual:

* [S13](01-addsub-integer.md) — the asymmetric `nuw` condition on
  `(W+X) - (Y+Z) → X - Z`.
* [M3](04-mul.md) and the `PreserveNSW` logic in
  [`simplifyIRemMulShl`](07-fdiv-rem.md) — `shl nsw` at shift amount `N-1`
  is *not* `mul nsw`.
* [CX5](09-andorxor-shared.md) — the documented-invalid dual, a ready-made
  negative test.
* [D27/D28](06-idiv.md) — the four distinct flag combinations for cancelling
  a shift across a division.
* [FD17](07-fdiv-rem.md) — `ninf` required because an *integer* exponent
  negation can wrap.
* [FR17/FR18](05-fmul.md) — integer overflow conditions inside FP rules.
* [§3.0 #1](02-addsub-float.md) — clearing `ninf` when `nnan` is absent.
* [foldShiftedShift](08-shifts.md) — the deliberate dropping of
  `nuw`/`nsw`/`exact` when a shift amount changes.
* [`disableWrapFlagsBasedOnUnusedHighBits`](21-simplifydemanded.md) — the
  same issue inside the demanded-bits analysis.
* [`foldLShrOverflowBit`](08-shifts.md) — the new `add` must *not* get
  no-wrap flags, because observing the carry is the point.

## Termination

There is **no termination guarantee** — no ranking function and no proof. A
large fraction of the `m_OneUse`, `m_ImmConstant` and `isFreeToInvert`
conditions in this catalogue exist to stop two rules undoing each other, and
the source usually does not say which conditions those are. See
[Part 22](23-termination.md) for the full analysis: the bounded outer loop,
the unbounded inner loop, the test-only fixpoint verifier, the taxonomy of
hand-written cycle guards, and what a port should do differently.
