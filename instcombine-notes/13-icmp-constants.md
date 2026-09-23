# `InstCombineCompares.cpp` — Part 13a: `icmp` framework and `icmp X, C`

Back to [index](README.md). This file (8832 lines) is split into three:

* **13a (this file)** — the `visitICmpInst` pipeline, canonicalisation, and the
  `icmp op(...), Constant` dispatch tree.
* **[13b](14-icmp-general.md)** — `icmp` of binops/casts with a non-constant RHS,
  equality folds, overflow idioms.
* **[13c](15-fcmp.md)** — `fcmp`.

---

## 13a.0 The `visitICmpInst` pipeline (line 7583)

Order matters here more than anywhere else in the pass, because many folds
assume earlier canonicalisations have run. In order:

1. **Operand canonicalisation** — swap so the higher-`getComplexity` operand is
   on the left (constants therefore end up on the right).
2. `simplifyICmpInst`.
3. `(select C, X, -X) != 0 → X != 0` (and the mirror).
4. `foldICmpTruncWithTruncOrExt`.
5. `canonicalizeICmpBool` (only for `i1` operands).
6. `canonicalizeCmpWithConstant` — **[canon]** turn `X <u C` into `X <=u C-1`
   etc. where that yields a "nicer" constant (`getFlippedStrictnessPredicateAndConstant`).
7. `canonicalizeICmpPredicate` — **[canon]** prefer the non-inverted predicate
   when all users can be inverted.
8. `foldICmpWithConstant`, `foldICmpWithDominatingICmp`,
   `foldICmpUsingBoolRange`, `foldICmpUsingKnownBits`.
9. **Bail out** if the sole user is a `select` forming a recognised min/max
   pattern — do not disturb min/max idioms (line 7629).
10. `foldICmpWithZero`.
11. `foldICmpBinOp` (13b), `foldICmpInstWithConstant` (this file),
    `foldSignBitTest`, `foldICmpInstWithConstantNotInt`.
12. `foldICmpCommutative` in both operand orders.
13. Select/select, sub-vs-add, alloca, bitcast, cast folds.
14. `foldICmpEquality` (13b), `foldICmpPow2Test`, `foldICmpOfUAddOv`,
    `foldICmpWithHighBitMask`, `foldVectorCmp`, `foldICmpInvariantGroup`,
    `foldReductionIdiom`.

### Predicate helpers used throughout

| Helper | Meaning |
|---|---|
| `isSignBitCheck(Pred, C, &TrueIfSigned)` | the compare is exactly a sign-bit test; `TrueIfSigned` says which way |
| `isSignTest(Pred, C)` | `X >s -1` or `X <s 0` (line 79) |
| `getFlippedStrictnessPredicateAndConstant` | `X <u C` ↔ `X <=u C-1` |
| `ConstantRange::makeExactICmpRegion(Pred, C)` | the set of `X` satisfying `icmp Pred X, C` |
| `CR.getEquivalentICmp(P, C, Offset)` | turn a range back into `icmp P (X+Offset), C` |
| `samesign` | on an `icmp`, asserts the operands have the same sign; **must be cleared** by any fold that keeps the compare but changes its operands' relationship |

`ConstantRange` is the workhorse. A port without it will lose a large fraction
of this file.

---

## 13a.1 Canonicalisations

| # | Rule | Side conditions | Line |
|---|---|---|---|
| K1 | swap operands by complexity | — | 7589 |
| K2 | `X >u SMAX → X <s 0` | | 7654 |
| K3 | `X <u SMIN → X >s -1` | | 7659 |
| K4 | `canonicalizeICmpBool` (line 7184) | `i1` operands: every predicate becomes a logic op, e.g. `A ==  B → ~(A^B)`, `A <u B → ~A & B`, `A >s B → A & ~B`, … | 7620 |
| K5 | `canonicalizeCmpWithConstant` (line 7141) | strict ↔ non-strict predicate swap when it makes the constant simpler | 7623 |
| K6 | `canonicalizeICmpPredicate` (line 7162) | invert the predicate when the compare's users can all be freely inverted | 7626 |
| K7 | `icmp (X ^ Y), 0` **[both operands freely invertible]** `→ icmp (swapped) ~X, ~Y` | both `isFreeToInvert` and at least one *consuming* | 7742 |
| K8 | `matchSymmetricPair` | for commutative predicates, canonicalise the operand pair | 7676 |

## 13a.2 Analysis-driven folds

| # | Rule | Line |
|---|---|---|
| KB1 | `foldICmpUsingKnownBits` (line 6839) — resolve the compare, or narrow the constant, from the operands' known bits and constant ranges. Also calls `getDemandedBitsLHSMask` (line 6697) to let `SimplifyDemandedBits` see which bits the compare actually needs | 7638 |
| KB2 | `foldICmpUsingBoolRange` (line 7052) — the same for operands known to be 0/1 | 7635 |
| KB3 | `foldICmpWithDominatingICmp` (line 1370) — intersect the compare's range with that implied by a **dominating branch** on the same value. Empty intersection → `false`; empty difference → `true`; a single-element intersection/difference → an `eq`/`ne`. **Skipped** when the compare is an equality, when it is a sign-bit test feeding a branch, or when its sole user is a min/max — those forms are better left alone | 7632 |

## 13a.3 `foldICmpWithZero` (line 1230)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| Z1 | `smin(A, B) >s 0 → B >s 0` | `isKnownPositive(A)` (or the mirror) | 1235 |
| Z2 | `foldIRemByPowerOfTwoToBitTest` (line 1180): `(X % Y) ==/!= 0 → (X & (Y-1)) ==/!= 0` | `1u` on the rem; `isKnownToBeAPowerOfTwo(Y, OrZero=true)` | 1246 |
| Z3 | `(X %u Y) ==/!= 0 → X ==/!= 0` | `X` has at most 1 possible set bit and `Y` has at least 2 known set bits, so `X < Y` always | 1252 |
| Z4 | `(X * Y) ==/!= 0 → Y ==/!= 0` | `X` is known odd (`countMaxTrailingZeros() == 0`); or the mul is `nuw`/`nsw` and `X` is known nonzero | 1262 |
| Z5 | `stripNullTest` | peels wrappers that don't change nullness | 1290 |

## 13a.4 `icmp (binop X, C1), C2` — the dispatch tree

`foldICmpInstWithConstant` (line 3561) → `foldICmpBinOpWithConstant` (line 3987)
switches on the binop opcode, then always falls through to
`foldICmpBinOpEqualityWithConstant` (line 3608) and
`foldICmpBinOpWithConstantViaTruthTable` (line 3100).

### `xor` — `foldICmpXorConstant` (line 1592)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CX1 | `(X ^ C1) <s 0 → X <s 0` | the compare is a sign-bit test and `C1` is **non-negative** (so it does not flip the sign bit) | 1606 |
| CX2 | `(X ^ C1) <s 0 → X >s -1` | sign-bit test, `C1` negative — the test inverts | 1609 |
| CX3 | `(X ^ signmask) <u C → X <s (C ^ signmask)` | `1u`; **flips the signedness of the predicate** | 1621 |
| CX4 | `(X ^ SMAX) <u C → X >s (C ^ SMAX)` | `1u`; flips signedness **and** swaps | 1627 |
| CX5 | `(X ^ ~C) >u C → X <u ~C` | `C+1` a power of two | 1634 |
| CX6 | `(X ^ C) >u C → X >u C` | `C+1` a power of two | 1637 |
| CX7 | `(X ^ -C) <u C → X >u ~C` | `C` a power of two | 1643 |
| CX8 | `foldICmpXorShiftConst` (line 1664): `(X ^ (X a>> S)) <u 2^k → (X + 2^k) <u 2^(k+1)` | `1u`; `S != 0`; the constant must be a power of two; also the `ugt` form. *This is `abs(X) < 2^k`* | 1595 |

### `and` — `foldICmpAndConstant` (line 1927) / `foldICmpAndConstConst` (line 1780)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CA1 | `(X & 1) != 0 → trunc X to <n x i1>` | vector compare, constant 0 | 1784 |
| CA2 | `(X & C2) >s C1 → X >s ~C2` | `C1 <=u ~C2`; `C2` a negated power of two | 1793 |
| CA3 | `(X & C2) <s C1 → X <s -C2` | `C1` not the sign mask; `(C1-1) <=u ~C2`; `C2` a negated power of two, not the sign mask | 1799 |
| CA4 | `(X & signmask) ==/!= 0 → X >=s/<s 0` | `1u` on the and | 1810 |
| CA5 | `(X & C2) ==/!= 0 → X <u/>=u -C2'` | `1u`; `C2'` = `C2` widened with `X`'s known leading zeros must be a negated power of two | 1817 |
| CA6 | `((trunc W) & C2) pred C1 → (W & zext C2) pred zext C1` | `1u` on the trunc; equality, or both constants non-negative; scalar only | 1831 |
| CA7 | `foldICmpAndShift` (line 1693) | see below | 1845 |
| CA8 | `((X \| (X >>u B)) & 1) ==/!= 0 → (X & ((1 <<nuw B) \| 1)) ==/!= 0` | unsigned; constant 0; a use-count budget (≥1 removed use if `B` is constant, ≥3 otherwise) | 1849 |
| CA9 | `(bitcast(F) & expmask) == 0 → is_fpclass(F, fcZero\|fcSubnormal)` | equality; `1u`; IEEE-like FP; no `noimplicitfloat`. With `C1 == C2` the mask is `fcNan\|fcInf` instead | 1880 |
| CA10 | `((X-1) & ~X) <s 0 → X == 0` | sign-bit test | 1936 |
| CA11 | `((-X) & X) <s 0 → X == INT_MIN` | sign-bit test | 1945 |
| CA12 | `foldCmpLoadFromIndexedGlobal` (line 109) | the `and` masks a load from a constant global array indexed by a variable — the compare becomes a bit-test against a computed magic constant | 1961 |
| CA13 | `(X & Y) == Y → X >u (Y-1)` | `C` is a negated power of two and equals the mask | 1973 |
| CA14 | `((zext i1 X) & Y) ==/!= 0/1 → (trunc Y) & X` (possibly negated) | `1u` on both | 1980 |
| CA15 | `((-1 << X) & Y) == 0 → (Y >>u X) == 0` | `1u` on both; constant 0 | 1991 |
| CA16 | `((A + Addend) & LowMask) == C → (A & LowMask) == ((C - Addend) & LowMask)` | `1u` on the add; `C <=u LowMask` | 2001 |

#### `foldICmpAndShift` (line 1693)

`icmp ((X shift C3) & C2), C1` → `icmp (X & C2'), C1'` with the constants
shifted the other way. Conditions:

* For `shl`: refuse if the compare is signed and either constant is negative.
* For `lshr`: refuse if signed and either *new* constant is negative.
* For `ashr`: require `NewAndCst.ashr(C3) == C2` (the mask must round-trip).
* If any bit of `C1` is shifted out, the **equality compare folds to a
  constant** (`false` for `eq`, `true` for `ne`).

Plus: `((X shift Y) & 1) ==/!= 0 → (X & (1 shift' Y)) ==/!= 0` — move the
shift onto the mask; `1u` on the shift, not an arithmetic shift, and either
the mask is `1` or the shifted value is not a constant.

### `or` — `foldICmpOrConstant` (line 2083)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CO1 | `signum(V) <s 1 → V <s 1` | `C == 1` | 2087 |
| CO2 | `(X \|disjoint C1) ==/!= C → X ==/!= (C1 ^ C)` | the `or` must be `disjoint` | 2094 |
| CO3 | `(X \| C1) ==/!= C1 → X <=u/>u C1` | `C == C1` and `C1+1` a power of two | 2103 |
| CO4 | `(X \| C1) ==/!= C → (X & ~C1) ==/!= (C ^ C1)` | `1u` on the or | 2108 |
| CO5 | `((X-1) \| X) <s 0 → X <s 1` | sign-bit test | 2117 |
| CO6 | `(X \| C1) <s C → X <s 0` | `C >= 0` and `C1 >=s C` (the `or` can only make it larger) | 2126 |
| CO7 | `(ptrtoint P \| ptrtoint Q) ==/!= 0 → (P == 0) & (Q == 0)` | `1u`; equality with zero | 2160 |
| CO8 | `foldICmpOrXorSubChain` (line 2024): `(A^B \| C^D \| …) ==/!= 0 → (A==B) & (C==D) & …` | equality with zero; `1u` on the whole chain; `sub` counts as `xor` here | 2173 |

### `mul` — `foldICmpMulConstant` (line 2184)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CM1 | `(X * X) ==/!= 0 → X ==/!= 0` | the mul is `nuw` or `nsw` | 2190 |
| CM2 | `(X *nsw C) >s -1 / <s 0 → X >s -1 / <s 0` | `isSignTest`; predicate **swapped if `C < 0`** | 2199 |
| CM3 | `(X *nsw C) ==/!= K → X ==/!= K/C` | `K srem C == 0` | 2211 |
| CM4 | `(X * C) ==/!= K → X ==/!= K udiv C` | `K urem C == 0` **and** (`C` is odd, or the mul is `nuw`) | 2216 |
| CM5 | `(X *nsw C) <s K → X <s RoundingSDiv(K, C, UP)` | signed predicate; `nsw`; predicate swapped if `C < 0`; `INT_MIN`/`-1` excluded. `SLE`/`SGT` use `DOWN` | 2226 |
| CM6 | `(X *nuw C) <u K → X <u RoundingUDiv(K, C, UP)` | unsigned predicate; `nuw`; `ULE`/`UGT` use `DOWN` | 2256 |

### `shl` — `foldICmpShlConstant` (line 2325)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CS1 | `foldICmpShlConstConst` (line 1049) | `icmp eq/ne (C2 << Y), C1` — a direct analysis of which shift amount, if any, makes the constants equal; folds to `Y == shift`, `Y >=u k`, or a constant | 2330 |
| CS2 | `(X <<nuw,nsw C) pred K → X pred K` | `K <= 0` | 2336 |
| CS3 | `(X << C) ==/!= 0 → X ==/!= 0` | the shl is `nuw` or `nsw` | 2341 |
| CS4 | `(X <<nsw C) >s/<s K → X >s/<s K` | `K` is 0, or `-1` for `sgt` / `1` for `slt` | 2346 |
| CS5 | `(X <<nsw C) >s K → X >s (K a>> C)` | | 2360 |
| CS6 | `(X <<nsw C) ==/!= K → X ==/!= (K a>> C)` | the shift must round-trip: `(K a>> C) << C == K` | 2366 |
| CS7 | `(X <<nsw C) <s K → X <s ((K-1) a>> C) + 1` | | 2372 |
| CS8 | `(X <<nuw C) >u/==/<u K → X …` | the `lshr` analogues of CS5–CS7 | 2381 |
| CS9 | `(X << C) ==/!= K → (X & lowmask) ==/!= (K >>u C)` | `1u`; equality | 2400 |
| CS10 | `(X << C) <s 0 → (X & (1 << (N-C-1))) != 0` | `1u`; sign-bit test | 2409 |
| CS11 | `(X << C) <=u K → (X & ~K>>C) == 0` | `1u`; `K+1` a power of two | 2419 |
| CS12 | `(X << C) <u K → (X & ~(K-1)>>C) == 0` | `1u`; `K` a power of two | 2429 |
| CS13 | `(X << C) pred K → (trunc X) pred' (K a>> C)` | `1u`; `C != 0`; `shouldChangeType` to `N-C` bits; `K`'s low `C` bits must be zero (after a strictness flip if needed). The `trunc` gets `nsw` iff the `shl` had it | 2440 |
| CS14 | `foldICmpShlLHSC` (line 2275): `(C2 <<nuw Y) pred K → Y pred' log2(K/C2)` | unsigned: `C2 != 0`, `C2 <=u K`; the predicate is tightened if `K/C2` is not an exact power of two. Signed with `C2 == 1`: `(1 << Y) >s K` (`K <= 0`) → `Y != N-1` | 2376 |

### `lshr`/`ashr` — `foldICmpShrConstant` (line 2505)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CR1 | `(X >>exact C) ==/!= 0 → X ==/!= 0` | | 2510 |
| CR2 | `foldICmpShrConstConst` (line 990) | `icmp eq/ne (C2 >> Y), C1` — analysis on the constants; for `ashr` additionally requires `C2 != -1`, matching signs, and `C2 <=s C1` | 2518 |
| CR3 | `(C2 >>u Y) <s 0 / >s -1 → Y ==/!= 0` | `C2` negative; sign-bit test | 2521 |
| CR4 | `(C2 >>u Y) >u/<u K → Y <u/>=u (clz K - clz C2)` | `C2` a power of two | 2527 |
| CR5 | `(X a>>exact C) <s K → X <s ((K-1) << C) + 1` | `K-1` a power of two; `clz(K) > C` | 2551 |
| CR6 | `(X a>> C) <s K → X <s (K << C)` | `exact`, or the predicate is `slt`/`ult`; the shift must round-trip | 2557 |
| CR7 | `(X a>> C) >s K → X >s ((K+1) << C) - 1` | round-trip conditions, `K != SMAX` | 2565 |
| CR8 | `(X a>> C) >u K → X >u ((K+1) << C) - 1` | round-trip, or the shifted value is `INT_MIN` | 2574 |
| CR9 | `(X a>> C) >u K → X <s 0` | `N > 2` and `numSignBits(K) <= C` — the comparison can only be true for negative `X` | 2582 |
| CR10 | `(X >>u C) <u K → X <u (K << C)` | round-trip | 2594 |
| CR11 | `(X >>u C) >u K → X >u ((K+1) << C) - 1` | round-trip | 2601 |
| CR12 | `(X >>exact C) ==/!= K → X ==/!= (K << C)` | | 2615 |
| CR13 | `(X >> C) ==/!= 0 → X <u/>u (1 << C) [- 1]` | equality with zero | 2618 |
| CR14 | `(X >> C) ==/!= K → (X & highmask) ==/!= (K << C)` | `1u` on the shift | 2626 |

### `srem`, `udiv`, `sdiv`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CD1 | `(X %s C) >u K → (X %s C) <s 0` | the normalised constant must be `>=u |C|-1`, i.e. the unsigned test can only be satisfied by a negative remainder | 2673 |
| CD2 | `(X %s 2^k) pred K → (X & (signmask \| (2^k-1))) pred' …` | `1u`; `K == 0` for `sgt`/`slt`, `K > 0` for equality | 2716 |
| CD3 | `(C2 /u Y) >u K → Y <=u (C2 udiv (K+1))` | the dividend is the constant | 2762 |
| CD4 | `(C2 /u Y) <u K → Y >u (C2 udiv K)` | | 2771 |
| CD5 | `foldICmpDivConstant` (line 2784) | the general "div by constant vs. constant" range analysis: computes the exact interval of dividends mapping to `C` and emits a range check. Handles both `udiv` and `sdiv`, including the rounding-toward-zero asymmetry around 0 | 2784 |

### `sub` — `foldICmpSubConstant` (line 2966)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CU1 | `(C2 - Y) ==/!= C → Y ==/!= (C2 - C)` | | 2973 |
| CU2 | `(C2 - Y) pred C → Y pred' (C2 - C)` | unsigned+`nuw` or signed+`nsw`; the constant subtraction must not overflow | 2985 |
| CU3 | `(X - Y) ==/!= 0 → X ==/!= Y` | **and no user of the sub is a PHI** (avoids a loop-carried regression) | 2990 |
| CU4 | `(X -nsw Y) >s -1 → X >=s Y` etc. | `1u`; four predicate/constant combinations | 2998 |
| CU5 | `(C2 - Y) <u 2^k → (Y \| (2^k-1)) == C2` | `(C2 & (C-1)) == C-1` | 3009 |
| CU6 | `(C2 - Y) >u C → (Y \| C) != C2` | `C+1` a power of two; `(C2 & C) == C` | 3013 |
| CU7 | `(C2 - Y) pred C → (Y + ~C2) pred' ~C` | the general fallback; flags carried | 3017 |

### `add` — `foldICmpAddConstant` (line 3139)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CN1 | `(zext/sext i1 A + zext/sext i1 B) pred C → logic(A, B)` | both extends are of `i1`; builds a 4-entry truth table and calls `createLogicFromTable` | 3145 |
| CN2 | `(X + C2) pred C → X pred (C - C2)` | `nsw` with a signed strict predicate, or `nuw` with unsigned strict; the constant subtraction must not overflow | 3179 |
| CN3 | `(X +nsw C2) <u C → X <s (C - C2)` | the range of `X + C2` must be provably all-non-negative | 3190 |
| CN4 | `(X + C2) pred C → X <u/>=u Bound` | via `ConstantRange`: when the shifted range starts at the sign mask or the minimum value, the compare becomes one-sided | 3197 |
| CN5 | four `SMAX`/`SMIN` boundary cases turning a signed compare into an unsigned one and vice versa | | 3213 |
| CN6 | `(X + -1) <u C → X <=u C` | `isKnownNonZero(X)` | 3226 |
| CN7 | `(X + C2) <u 2^k → (X & -2^k) == -C2` | `1u`; `(C2 & (C-1)) == 0` | 3236 |
| CN8 | `(X + C2) <u -C2 → (X & C) != 2C` | `1u`; `C2` a power of two | 3240 |
| CN9 | `(X + C2) >u C → (X & ~C) != -C2` | `1u`; `C+1` a power of two, `(C2 & C) == 0` | 3245 |
| CN10 | `(X + C2) >u C → (X + (C2-C-1)) <u ~C` | `1u`; the general `ugt` fallback | 3250 |
| CN11 | `(zext V + C2) pred C → V pred' C'` | `1u`; the range fits in the narrow type; `shouldChangeType` | 3256 |

### Equality with a constant — `foldICmpBinOpEqualityWithConstant` (line 3608)

A per-opcode table for `icmp eq/ne (binop X, Y), C` covering the cases not
handled above (e.g. `srem`, `udiv`, `add`, `and`, `or`, `xor`, `sub`, `mul`,
`shl`, shifts). Its distinguishing feature is that equality lets it use exact
constant arithmetic rather than range reasoning.

### `foldICmpBinOpWithConstantViaTruthTable` (line 3100)

```
icmp Pred (binop (select A, C1, C2), (select B, C3, C4)), C
```
Both operands are selects of constants, and the select conditions have the
compare's type. The four combinations are constant-folded and compared against
`C`, giving a 4-bit truth table; `createLogicFromTable` (line 3050) then emits
the corresponding logic expression over `A` and `B` (all 16 tables are
handled; the seven that need two instructions require `1u` on the binop).

**This is a complete decision procedure for its pattern class** and is the
single most portable idea in the file: enumerate, tabulate, synthesise.

### Intrinsics — `foldICmpIntrinsicWithConstant` (line 4192)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CI1 | `uadd_sat`/`usub_sat` vs. constant | `foldICmpUSubSatOrUAddSatWithConstant` (line 4045): combine the no-wrap region with the compare's region via exact union/intersection, then emit the equivalent `icmp`. `1u` | 4199 |
| CI2 | `ucmp`/`scmp` vs. constant → a direct `icmp` on the operands | `foldICmpOfCmpIntrinsicWithConstant` (line 4104): a small table over the predicate and the constant (`0`, `1`, `-1`) | 4209 |
| CI3 | `ctpop(X) >u (N-1) → X == -1` | | 4224 |
| CI4 | `ctpop(X) <u N → X != -1` | | 4227 |
| CI5 | `ctlz(X) >u K → X <u (1 << (N-K-1))` | `K < N` | 4234 |
| CI6 | `ctlz(X) <u K → X >u lowmask(N-K)` | `1 <= K <= N` | 4240 |
| CI7 | `cttz(X) >u K → (X & lowmask(K+1)) == 0` | `1u`; `K < N` | 4249 |
| CI8 | `cttz(X) <u K → (X & lowmask(K)) != 0` | `1u` | 4255 |
| CI9 | `ssub_sat(A,B) pred 0/1/-1 → A pred' B` | signed predicates only | 4263 |
| CI10 | `foldCtpopPow2Test` (line 3763) | `ctpop` against a power-of-two constant | 4205 |
| CI11 | `foldICmpEqIntrinsicWithConstant` (line 3801) | the equality-only table for `bswap`, `bitreverse`, `ctlz`, `cttz`, `ctpop`, `abs`, `fshl/fshr`, … | 4217 |

### Non-integer constants — `foldICmpInstWithConstantNotInt` (line 4300)

Sinks the compare into a `phi` (`foldOpIntoPhi`) or a `select`
(`foldSelectICmp`, line 4335).

