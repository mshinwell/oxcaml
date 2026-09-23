# `InstCombineMulDivRem.cpp` — Part 3: `udiv`, `sdiv`

Back to [index](README.md).

**Semantic reminder.** In LLVM, `udiv`/`sdiv`/`urem`/`srem` by zero is
**immediate UB** (not poison), and `sdiv INT_MIN, -1` / `srem INT_MIN, -1` are
also UB. `exact` on a div means the remainder is zero (else poison). Several
rules below exploit the UB-on-zero to *assume* the divisor is nonzero — a port
to a language where division by zero traps or returns a value must re-derive
them.

## 7.1 `commonIDivRemTransforms` (line 1270) — shared by all four ops

| # | Rule | Side conditions | Line |
|---|---|---|---|
| D1 | `X op <..., 0, ...>` → `poison` | any element of a **fixed-width vector** constant divisor is zero or `undef` | 1277 |
| D2 | `foldBinopWithPhiOperands` | Part 12 | 1289 |
| D3 | simplify the divisor knowing it is nonzero | `simplifyValueKnownNonZero`, see M37–M39 | 1293 |
| D4 | `X op (Cond ? 0 : Y) → X op Y` | and then `Cond` is **propagated as a known constant** into dominating uses, scanning backwards while `isGuaranteedToTransferExecutionToSuccessor` | 1097 |
| D5 | `X op (Cond ? Y : 0) → X op Y` | same | 1097 |
| D6 | `C op (Cond ? C1 : C2) → Cond ? (C op C1) : (C op C2)` | `Op0` and both arms are `m_ImmConstant`; allowed even with multiple uses | 1304 |

> **D4/D5 is more than a peephole.** Because `div X, 0` is UB, reaching the
> division proves the select did not pick the zero arm, hence proves `Cond`.
> The backward scan then substitutes that fact. This is a miniature dominating-
> condition propagation embedded in InstCombine.

## 7.2 `commonIDivTransforms` (line 1317) — shared by `udiv`/`sdiv`

With a constant divisor `C2`:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| D7 | `(X / C1) / C2 → X / (C1 * C2)` | `C1 * C2` must not overflow (signed or unsigned to match) | 1330 |
| D8 | `(X *nsw/nuw C1) / C2 → X / (C2 / C1)` | `C2` is a multiple of `C1` (`isMultiple`, which also rejects `C1 == 0` and `INT_MIN / -1`); `exact` copied | 1344 |
| D9 | `(X *nsw/nuw C1) / C2 → X * (C1 / C2)` | `C1` a multiple of `C2`. New mul gets `nuw` only if unsigned and the old mul was `nuw`; `nsw` copied | 1352 |
| D10 | `(X <<nsw/nuw C1) / C2 → X / (C2 >> C1)` | signed needs `C1 < N-1`, unsigned `C1 < N`; `2^C1` divides `C2` | 1370 |
| D11 | `(X <<nsw/nuw C1) / C2 → X * (2^C1 / C2)` | `C2` divides `2^C1` | 1378 |
| D12 | `((X *nsw C2) +nsw C1) / C2 → X + (C1 / C2)` | signed: `C1` must be a multiple of `C2`; result is `nsw` | 1392 |
| D13 | `((X *nuw C2) +nuw C1) / C2 → X + (C1 udiv C2)` | unsigned: **no** multiple requirement; result is `nuw` | 1398 |
| D14 | `foldBinOpIntoSelectOrPhi` | only if `C2 != 0` | 1404 |

> **Why D13 needs no multiple condition but D12 does.** Unsigned:
> `(X·C2 + C1) / C2 = X + C1/C2` holds by Euclidean division as long as
> `X·C2 + C1` does not wrap, which `nuw` on both gives. Signed division
> truncates toward zero, so a negative remainder would round the wrong way;
> requiring `C2 | C1` removes the remainder entirely.

With `Op0 == 1`:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| D15 | `1 /s Y → (Y + 1) u< 3 ? Y : 0` | **`Y` frozen** if not known non-undef (two new uses) | 1410 |
| D16 | `1 /u Y → zext(Y == 1)` | uses UB-on-zero to ignore `Y == 0` | 1423 |

General:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| D17 | `SimplifyDemandedInstructionBits` | Part 11 | 1430 |
| D18 | `(X - (X % Y)) / Y → X / Y` | matching signedness of the `rem`. *Usually arises from `((X/Y)*Y)/Y`* | 1435 |
| D19 | `(Y <<nsw Y) /s Y → 1 <<nsw Y` | dividend is `shl nsw` of the divisor | 1442 |
| D20 | `(Y <<nuw Y) /u Y → 1 <<nuw Y` | as above with `nuw` | 1445 |
| D21 | `X / (X * Y) → 1 / Y` **[comm on the mul]** | the mul must have `nsw` (signed) / `nuw` (unsigned). Rewritten in place | 1449 |
| D22 | `(X <<nuw Z) /u (X * Y) → (1 <<nuw Z) /u Y` | unsigned only; `1u` on the mul, which must be `nuw`; `exact` copied | 1461 |
| D23 | `((Op1 * X) / Y) / Op1 → X / Y` **[comm on the mul]** | the mul needs `nuw` (udiv) / `nsw` (sdiv). `exact` only if **both** divides were exact | 1476 |
| D24 | `(X * Y) / (X * Z) → Y / Z` **[comm]** | signed: both muls `nsw` and `Z` a constant `!= -1`. unsigned: both muls `nuw`; *or* the outer mul `nuw` and `Y`, `Z` constants with `Z <= Y` | 1494 |

## 7.3 `foldIDivShl` (line 1189)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| D25 | `(X * Y) /u (X << Z) → Y >>u Z` | mul and shl **both `nuw`**; `exact` copied | 1211 |
| D26 | `(X * Y) /s (X << Z) → Y /s (1 << Z)` | mul and shl both `nsw`; `1u` on one operand | 1214 |
| D27 | `(X << Z) /u (Y << Z) → X /u Y` | (both shl `nuw`) **or** (Shl0 `nuw`+`nsw` and Shl1 `nsw`) | 1229 |
| D28 | `(X << Z) /s (Y << Z) → X /s Y` | both shl `nsw` **and** the divisor's shl also `nuw` | 1239 |
| D29 | `(X << Y) / (X << Z) → (1 << Y) >>u Z` | both shl `nsw` (signed) or both `nuw` (unsigned). The new dividend `shl` is `nuw`; its `nsw` is derived from the originals' flags | 1248 |

> These are the most flag-sensitive rules in the file. Each corresponds to a
> distinct cancellation lemma, e.g. D27 unsigned: `(x·2^z)/(y·2^z) = x/y`
> requires both products exact in the unsigned sense, which `nuw` gives.
> The alternative `nuw`+`nsw`/`nsw` condition covers the case where the values
> are known non-negative.

## 7.4 `visitUDiv` (line 1671)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| U1 | `(X >>u C1) /u C2 → X /u (C2 << C1)` | `C2 << C1` must not overflow unsigned; `exact` only if both were exact | 1685 |
| U2 | `Op0 /u C → zext(Op0 >=u C)` | `C` is **negative** as a signed value, i.e. `C > 2^(N-1)`, so the quotient is 0 or 1 | 1703 |
| U3 | `Op0 /u sext(i1 X) → zext(Op0 == -1)` | `X == 0` makes the div UB, so only the `-1` case matters | 1708 |
| U4 | `((Op1 *nuw A) >>u B) /u Op1 → A >>u B` **[comm on the mul]** | `exact` iff both were exact | 1721 |
| U5 | `Op0 /u Op1 → Op0 >>u log2(Op1)` | `tryGetLog2(Op1, AssumeNonZero=true)` must fold away | 1731 |
| U6 | `Op0 /u Op1 → Op0 >>u cttz(Op1)` | `isKnownToBeAPowerOfTwo(Op1, OrZero=true)`. **Deliberately increases instruction count** — a `cttz`+`lshr` beats a divide | 1735 |

### `narrowUDivURem` (line 1629), shared with `urem`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| U7 | `(zext X) op (zext Y) → zext(X op Y)` | same source type; `1u` on one | 1636 |
| U8 | `(zext X) op C → zext(X op C')` | `1u` on the zext; `C` must round-trip losslessly through the narrow type (`getLosslessUnsignedTrunc`) | 1645 |
| U9 | `C op (zext X) → zext(C' op X)` | same | 1656 |

## 7.5 `visitSDiv` (line 1751)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S1 | `Op0 /s -1 → -Op0` | result is `nsw neg`. Also matches `sext(i1 X)` as the divisor (`X == 0` would be UB) | 1763 |
| S2 | `X /s INT_MIN → zext(X == INT_MIN)` | — | 1768 |

With `exact`:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S3 | `X /sexact 2^C → X a>>exact C` | `2^C` must be **non-negative** (excludes `INT_MIN`) | 1773 |
| S4 | `X /sexact (1 <<nsw ShAmt) → X a>>exact ShAmt` | the `shl` must be `nsw`, which makes it non-negative | 1780 |
| S5 | `X /sexact (-2^C) → -(X a>>exact C)` | result is `nsw neg` | 1784 |

With a constant divisor:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S6 | `(sext X) /s C → sext(X /s C)` | `1u` on the sext; `C` fits in the source type (`getSignificantBits`). Safe because the `C == -1` case was handled by S1 | 1797 |
| S7 | `(-X) /s C → X /s (-C)` | the neg must be `nsw`; `C != INT_MIN`; `exact` copied | 1815 |
| S8 | `(-X) /s Y → -(X /s Y)` | `1u` on the `nsw neg`; result is `nsw neg`; `exact` copied | 1824 |
| S9 | `abs(X) /s X → X >s -1 ? 1 : -1` **[comm]** | `1u`; the `abs` must be `is_int_min_poison` | 1831 |

Known-bits driven:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S10 | infer `exact` on the `sdiv` | divisor is ±2^C and the dividend has at least `countr_zero(C)` known trailing zeros | 1839 |
| S11 | `X /s Y → X /u Y` | **both** operands known non-negative; `exact` copied | 1848 |
| S12 | `X /s (-2^C) → -(X >>u C)` | dividend known non-negative | 1854 |
| S13 | `X /s (1 << Y) → X /u (1 << Y)` | dividend known non-negative and `isKnownToBeAPowerOfTwo(Op1, OrZero=true)`. Sound because the only negative power of two is `INT_MIN`, and a non-negative `X` divided by `INT_MIN` is 0 either way | 1863 |
| S14 | `(-X) /s X → X == INT_MIN ? 1 : -1` | `isKnownNegation(Op0, Op1)` | 1874 |

## 7.6 `takeLog2` / `tryGetLog2` (line 1528)

A recursive, *speculative* helper: with `DoFold = false` it only reports
whether a symbolic `log2` exists; callers then re-run it with `DoFold = true`
to build the value. `AssumeNonZero` says the caller has already established the
operand is nonzero.

| # | `log2(V)` where `V` = | Result | Requirement |
|---|---|---|---|
| L1 | a constant power of two | the exponent | — |
| L2 | `zext X` | `zext(log2 X)` | — |
| L3 | `trunc X` | `trunc(log2 X)` | `AssumeNonZero` or the trunc is `nuw` |
| L4 | `X << Y` | `log2(X) + Y` | `AssumeNonZero`, or the `shl` is `nuw` or `nsw` |
| L5 | `X >>u Y` | `log2(X) - Y` | `AssumeNonZero` or the `lshr` is `exact` |
| L6 | `X & Y` | `log2(X)` or `log2(Y)` | **`AssumeNonZero` required** — `X & Y` can be zero when `X != Y` |
| L7 | `Cond ? X : Y` | `Cond ? log2 X : log2 Y` | — |
| L8 | `umin/umax(X, Y)` | `umin/umax(log2 X, log2 Y)` | `1u`; unsigned only; the recursion is forced to **`AssumeNonZero = false`**, because otherwise `log2(umax(X,Y)) != umax(log2 X, log2 Y)` |

Depth-limited by `MaxAnalysisRecursionDepth`.

