# `InstCombineSelect.cpp` — Part 14: `select`

Back to [index](README.md). `visitSelectInst`, line 3914.

## 14.0 Why `select` is special

`select C, T, F` is the **only** LLVM instruction that is poison-blocking on
one operand: if `C` is not poison, the result does not depend on the unselected
arm. That gives it two roles:

1. **A value-level `if`**, so it is where most idiom recognition happens
   (min/max, abs, saturating arithmetic, clamp, sign, `copysign`, `bit_ceil`).
2. **The short-circuit form of `and`/`or`** on `i1`:
   `select C, X, false` = logical and, `select C, true, X` = logical or.
   These match `m_LogicalAnd` / `m_LogicalOr`, which also match the bitwise
   forms — so a fold matching `m_LogicalAnd` must be poison-safe.

**Two recurring correctness conditions:**

* **`impliesPoisonOrCond(V, Cond, Expected)`** — can `V` be converted from a
  short-circuited operand to an always-evaluated one? Only if `V` being poison
  implies `Cond == Expected`, so no new poison is observed.
* **Freeze insertion** — several folds that merge two nested selects insert a
  `freeze` on the shared condition when the two selects could disagree about
  poison (e.g. `foldSelectOfBools`, lines 3402 and 3414).

## 14.1 Canonicalisation

| # | Rule | Side conditions | Line |
|---|---|---|---|
| SC1 | `canonicalizeSelectToShuffle` (line 2312): a vector select with a constant condition → `shufflevector` | all condition lanes must be constant `true`/`false` (poison lanes allowed) | 3923 |
| SC2 | `canonicalizeScalarSelectOfVecs` (line 2351): a scalar condition selecting vectors → splat the condition | | 3926 |
| SC3 | substitute `Cond := true/false` inside each arm | `simplifyWithOpReplaced` with `AllowRefinement = true`, plus `replaceInInstruction`. Only for integer selects with matching vector-ness | 3932 |
| SC4 | `select C, 1, 0 → zext C` | integer, not `i1` | 3956 |
| SC5 | `select C, -1, 0 → sext C` | | 3959 |
| SC6 | `select C, 0, 1 → zext (~C)` | | 3961 |
| SC7 | `select C, 0, -1 → sext (~C)` | | 3966 |
| SC8 | `select (~C), T, F → select C, F, T` | unless `shouldAvoidAbsorbingNotIntoSelect` (the swap would break a min/max shape). Swaps `prof` metadata too — **[canon]** | 4177 |
| SC9 | `select (fcmp u*), X, Y → select (fcmp o*-inverted), Y, X` | `1u` on the fcmp; the compare's operands must be the two select arms. `nnan`/`ninf` are *added* to the new select's FMF from the fcmp | 3977 |

## 14.2 `foldSelectOfBools` (line 3227) — `i1` selects

Only for `i1`/`<n x i1>` result with a non-constant condition.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| B1 | `select C, true, F → C \| F` | `impliesPoisonOrCond(F, C, false)` | 3240 |
| B2 | `select (select A, true, B), true, F → A \|\| (B \| F)` | `1u`; `impliesPoisonOrCond(F, B, false)` | 3246 |
| B3 | `select (A && B), true, (C && D) → …` | factorise on the common operand; `1u` on one | 3253 |
| B4 | `select C, T, false → C & T` | `impliesPoisonOrCond(T, C, true)` | 3286 |
| B5 | `select (select A, B, false), T, false → A && (B & T)` | `1u`; `impliesPoisonOrCond(T, B, true)` | 3291 |
| B6 | `select (A \|\| B), (C \|\| D), false → …` | factorise; `1u` on one | 3298 |
| B7 | `select C, false, F → select (~C), F, false` | — **[canon]** | 3331 |
| B8 | `select C, T, true → select (~C), true, T` | — **[canon]** | 3336 |
| B9 | `(~A) && (~B) → ~(A \|\| B)` | `1u` on one; neither a `ConstantExpr` | 3342 |
| B10 | `(~A) \|\| (~B) → ~(A && B)` | same | 3347 |
| B11 | `select (select A, true, B), true, B → select A, true, B` | | 3353 |
| B12 | `~(A && B) && (A \|\| B) → A ^ B` | commuted | 3363 |
| B13 | four rewrites pulling a `not` out of the condition into a nested select | `1u` on the condition; `getFreelyInverted` where needed | 3368 |
| B14 | `isCheckForZeroAndMulWithOverflow` | the `umul.with.overflow` zero-check idiom; **inserts a `freeze`** | 3399 |
| B15 | `foldBooleanAndOr(..., IsLogical=true)` | the whole comparison-folding machinery of [11c](11-andorxor-cmps.md), in poison-safe mode | 3407 |
| B16 | four folds using `isImpliedCondition` to drop a redundant conjunct/disjunct | | 3413 |
| B17 | `select (C && A), true, ((~C) && B) → select C, A, B` | **inserts a `freeze` on `C`** when both are real selects and the inner values are inverses | 3443 |

## 14.3 `select` of an `icmp` — `foldSelectInstWithICmp` (line 1974)

| # | Helper | What it recognises | Line |
|---|---|---|---|
| I1 | `canonicalizeSPF` (line 1254) | canonicalise a select-pattern-flavour (min/max/abs) compare | 1977 |
| I2 | `foldSelectInstWithICmpConst` (line 1758) | compare against a constant: substitute the constant into the matching arm | 1981 |
| I3 | `canonicalizeClampLike` (line 1484) | two nested selects forming `clamp(X, Lo, Hi)` — a long function with careful handling of the boundary constants and predicate strictness | 1985 |
| I4 | `tryToReuseConstantFromSelectInComparison` | reuse the select's constant in the compare to remove one | 1989 |
| I5 | `foldSelectICmpEq` (line 1859) | equality compare: replace uses of the compared value in the matching arm | 1998 |
| I6 | `select (X >s -1), T, F → select (X <s 0), F, T` | `1u` on the compare; neither arm constant — **[canon]** | 2002 |
| I7 | `foldSelectICmpMinMax` (line 571) | `select (X pred Y), X, Y` shapes → `smin`/`smax`/`umin`/`umax` | 2015 |
| I8 | `foldSelectICmpAndAnd` (line 632) | `select ((X & C) == 0), (Y & ~C), Y` → an `and` | 2018 |
| I9 | `foldSelectICmpAndZeroShl` (line 680) | `select ((X & (1<<Y)) == 0), 0, (Z << Y)` shapes | 2023 |
| I10 | `foldSelectCtlzToCttz` (line 1146) | `select (X == 0), N, (N-1 - ctlz(bitreverse X))` → `cttz` | 2026 |
| I11 | `foldSelectZeroOrOnes` (line 1734) | selects between `0` and `-1` → sign/zero extension of a compare | 2029 |
| I12 | `foldSelectICmpLshrAshr` (line 718) | `select (X <s 0), (Y a>> Z), (Y >>u Z)` → a single shift | 2032 |
| I13 | `foldSelectCttzCtlz` (line 1189) | `select (X == 0), BitWidth, cttz/ctlz(X)` → drop the `is_zero_poison` flag on the intrinsic | 2035 |
| I14 | `canonicalizeSaturatedSubtract` (line 925) | `select (X >u Y), (X - Y), 0` → `usub.sat(X, Y)` | 2039 |
| I15 | `canonicalizeSaturatedAdd` (line 992) | the `uadd.sat` shapes | 2042 |
| I16 | `foldAbsDiff` (line 1096) | `select (X >u Y), (X - Y), (Y - X)` → `abs(sub)`/`usub.sat` pairs | 2045 |
| I17 | `foldSelectWithConstOpToBinOp` (line 1882) | `select (X == C1), C2, (op X, C3)` → a single binop when the arithmetic lines up | 2048 |
| I18 | `foldSelectICmpAnd` (line 123) | `select ((X & C) != 0), A, B` → shift/mask arithmetic | via I2 |
| I19 | `foldSelectICmpAndBinOp` (line 773) | `select ((X & C) != 0), (Y op C2), Y` | via I2 |

## 14.4 Arithmetic idioms

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A1 | `foldSelectBitTest` (line 3851) | `select ((X & C) != 0), T, F` where `T`/`F` differ by a single bit | 4034 |
| A2 | `foldAddSubSelect` (line 2077) | `select C, (A + B), A` → `A + select C, B, 0`; also the negation shapes forming `abs`/`nabs` | 4037 |
| A3 | `foldOverflowingAddSubSelect` (line 2153) | `select (overflow check), sat, (A + B)` → a saturating intrinsic | 4040 |
| A4 | `foldSetClearBits` (line 841): `select C, (X & ~M), (X \| M) → X \| select(C, 0, M)` | `1u` on the `or`; the constants must be exact complements | 4043 |
| A5 | `foldSelectZeroOrMul` (line 881): `select (X == 0), 0, (X * Y) → X * Y` | equality compare against zero | 4046 |
| A6 | `foldSelectOpOp` (line 244) | both arms are the **same opcode**: sink the select below it. Refuses when the result would break an existing min/max | 4051 |
| A7 | `foldSelectExtConst` (line 2267): `select C, (ext X), C1 → ext (select C, X, C1')` | the constant must round-trip through the narrow type | 4055 |
| A8 | `foldSelectWithSRem` (line 2773): `select (X %s 2 == 0), X, (X-1)` style parity idioms | | 4058 |
| A9 | `select C, (gep P, Idx), P → gep P, (select C, Idx, 0)` | the GEP has exactly one index, `1u`, and the same base as the other arm; also mirrored | 4082 |
| A10 | `foldSelectIntoOp` (line 495) | `select C, (X op Y), X → X op (select C, Y, identity)`. `getSelectFoldableOperands` (line 221) says which operand position is foldable per opcode (both for `add mul and or xor fadd fmul`; only the RHS for `sub fsub fdiv shl lshr ashr`). The non-folded operand must be a constant forming a "select 0/1" pattern (`isSelect01`). **FP:** requires the other arm to be known-never-NaN, and the new binop's `nnan`/`ninf`/`nsz` are intersected with the select's | 4092 |
| A11 | `foldSelectIntoAddConstant` (line 3791) | `select C, (X + C1), (X + C2)` → `X + select(C, C1, C2)` | 4324 |
| A12 | `foldRoundUpIntegerWithPow2Alignment` | `(X + A - 1) & -A` style alignment round-up | 4321 |
| A13 | `foldBitCeil` (line 3582) | the `std::bit_ceil` idiom → a shift of `1` by `N - ctlz(X-1)`; `isSafeToRemoveBitCeilSelect` (line 3487) decides whether the guarding select can go and whether no-wrap flags must be dropped | 4360 |
| A14 | `foldSelectToCmp` (line 3640) | a three-way select → `scmp`/`ucmp` | 4363 |
| A15 | `foldSelectEqualityTest` (line 1443) | `select (A == B), A, B` → `B` shapes | 4366 |

## 14.5 Min/max and select-pattern-flavour

`matchSelectPattern` (in ValueTracking) classifies a select as `SPF_SMIN`,
`SPF_UMAX`, `SPF_ABS`, `SPF_FMINNUM`, … `visitSelectInst` uses it twice:

* `foldSPFofSPF` (line 2056) — a min/max whose operand is itself a min/max:
  collapse nested extrema (`max(max(a,b),a) → max(a,b)`, etc.).
* **Re-canonicalisation** (line 4101): if the min/max's compare operands are
  not exactly the select's arms (or a cast is involved), rebuild the compare
  from the arms so the pattern is in canonical form.

FP min/max → intrinsics (line 4001):

| Rule | Conditions |
|---|---|
| `select (fcmp ogt/ugt X, Y), X, Y → maxnum(X, Y)` | select is **`nnan`**, and **`nsz`** — or `1u` and the single user can ignore the sign of zero (`canIgnoreSignBitOfZero`). `nnan`/`ninf` on the new intrinsic come from the **fcmp** |
| `select (fcmp olt/ult X, Y), X, Y → minnum(X, Y)` | same |

`nnan` is required because `maxnum` has defined NaN behaviour that the select
does not; `nsz` because `maxnum(+0,-0)` is unspecified.

## 14.6 FP-specific

| # | Rule | Side conditions | Line |
|---|---|---|---|
| F1 | `foldSelectWithFCmpToFabs` (line 2879) | the full family of `select (X <o 0), -X, X → fabs(X)` and its inversions/negations, each with its own `nsz`/`nnan` requirement | 4033 |
| F2 | `select (fcmp oeq X, C), Y, X → X` | `matchFMulByZeroIfResultEqZero` (line 3745) — when `Y` is `X * 0` and the result would be zero anyway | 3989 |
| F3 | `foldSelectToCopysign` (line 2563) | `select (X <s 0), -Y, Y` on bitcast FP → `copysign(Y, X)` | 4318 |
| F4 | `foldSelectBinOpIdentity` (line 56) | `select (X == identity), (X op Y), Z → select …, Y, Z` — the compare proves the binop is the identity. **FP requires `nsz` on the binop or `cannotBeNegativeZero(Y)`**, and allows `+0.0`/`-0.0` to match the identity | 4313 |

## 14.7 Nested selects and control flow

| # | Rule | Side conditions | Line |
|---|---|---|---|
| N1 | `select C, (select C', T', F), F → select (C && C'), T', F` | `1u` on the inner select; matching condition types | 4142 |
| N2 | `select C, T, (select C', T, F') → select (C \|\| C'), T, F'` | same | 4157 |
| N3 | `simplifyNestedSelectsUsingImpliedCond` (line 2849) | replace a nested select whose condition is implied by the outer one | 4139 |
| N4 | sink the select into a `1u` binop arm whose operand is a select on the **same condition** | the binop must not be an integer div/rem (speculation hazard) | 4190 |
| N5 | `foldSelectToPhi` (line 2752) / `foldSelectToPhiImpl` (line 2691) | when the condition is determined by which predecessor we came from, turn the select into a PHI | 4319 |
| N6 | `foldNestedSelects` (line 3123) | a general nested-select simplifier | 4357 |
| N7 | `foldSelectOfSymmetricSelect` | two selects that are mirror images | 4354 |
| N8 | `foldSelectWithFrozenICmp` (line 2822): `select (freeze (X == Y)), X, Y → Y` | | 4322 |
| N9 | `select (phi ...), T, F` → sink into the phi | `foldOpIntoPhi` | 4134 |
| N10 | `select (C1 & C2), T, F` → nested selects | fires when substituting one conjunct simplifies the select; `1u` on the condition for the `canonicalizeSPF` variant | 4375 |

## 14.8 Miscellaneous

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M1 | resolve the select from `llvm.assume` | `computeKnownBits` on the condition shows it constant; scalar only, and only when assumptions exist | 4300 |
| M2 | `foldSelectCmpBitcasts` (line 2372) | `select C, (bitcast X), (bitcast Y) → bitcast (select C, X, Y)` | 4308 |
| M3 | `foldSelectCmpXchg` (line 2439) | `select (extractvalue cmpxchg, 1), …` | 4311 |
| M4 | `foldSelectFunnelShift` (line 2492) | `select (ShAmt == 0), X, (or (shl X, S), (lshr Y, N-S))` → `fshl`/`fshr` | 4315 |
| M5 | `foldVectorSelect` (line 2606) | vector-specific select folds | 4297 |
| M6 | `select C, (masked.load … poison), 0 → masked.load … 0` | the mask must be the select condition; the passthru operand is rewritten in place | 4327 |
| M7 | `select C, 0, (masked.load … M)` → fold into the load | requires `simplifyAndInst(C, M)` to be zero | 4337 |
| M8 | `select C, T, F → C ^ F` | `isKnownInversion(F, T)` and the condition has the select's type | 4399 |
| M9 | replace an arm with a constant | using `CondContext`: the condition's implications make the arm's `computeKnownBits` constant. Only when at least one arm is non-constant | 4403 |
| M10 | `select (trunc nuw X), X, F → select …, 1, F` | the `nuw` trunc to `i1` proves the value is 0 or 1 | 4427 |
| M11 | `select (trunc nsw X), X, F → select …, -1, F` | the `nsw` trunc to `i1` proves 0 or -1 | 4436 |
| M12 | `sinkNotIntoOtherHandOfLogicalOp` | | 4358 |

