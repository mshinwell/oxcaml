# `InstCombineMulDivRem.cpp` — Part 1: `mul`

Back to [index](README.md). `visitMul`, line 189.

Preamble: `simplifyMulInst`; `SimplifyAssociativeOrCommutative`;
`foldVectorBinop`; `foldBinopWithPhiOperands`; `foldUsingDistributiveLaws`.

## 5.1 Constant multipliers → shifts

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M1 | `X * -1 → 0 - X` | output `nsw` iff the mul had `nsw` | 211 |
| M2 | `(X << C2) * C1 → X * (C1 << C2)` | `C1`, `C2` are `m_ImmConstant`. Output `nuw` iff mul and shl both `nuw`; output `nsw` iff mul and shl both `nsw` **and** `C1 << C2 != INT_MIN` | 222 |
| M3 | `X * 2^C → X << C` | `getExactLogBase2` must succeed (per-lane for vectors). Output `nuw` copied. Output `nsw` copied **only if `C != N-1`** | 240 |
| M4 | `(X >>exact N) * (2^N + 1) → X + (X >>exact N)` | `N > 2` bitwidth; the shift must be `exact`; `MulAP - 1` a power of two with `ShiftC == log2(MulAP)`. If the mul is `nuw` and the shift is an `ashr` with `1u`, the shift is rewritten to `lshr exact`. Output `nsw` iff mul `nsw` **and** (mul `nuw` ∨ shift is `lshr` ∨ `ShiftC < N-1`) | 258 |

> **M3's `nsw` caveat.** `X * 2^(N-1)` is `X << (N-1)`, and `shl nsw` requires
> the shifted-out bits *and* the new sign bit to agree with the original sign,
> which is a strictly stronger condition than `mul nsw` at that shift amount.
> Concretely for `i8`: `mul nsw i8 3, 128` is already poison, so nothing is
> lost — but `mul nsw i8 1, 128` is poison too while `shl nsw i8 1, 7` is
> `-128`, defined. Hence the exclusion.

## 5.2 Negated-power-of-two multipliers (`Op0` has `1u`, `Op1` is `-2^C`)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M5 | `X * (-2^C) → (-X) * 2^C` | only if `Negator::Negate` succeeds on `X`. Output `nuw` forced false; `nsw` iff mul `nsw` and `-Op1 != INT_MIN` | 285 |
| M6 | `(zext/sext X) * (-2^C) → (zext (-X)) << C` | `C >= BitWidth - SrcWidth` — the shift must clear every bit the extension could have differed in, which is what makes `zext` sound for an `sext` input | 298 |

## 5.3 Distribution over add/or

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M7 | `(X + C1) * MulC → X*MulC + C1*MulC` | `1u` on the add; `MulC`, `C1` are `m_ImmConstant`. Also matches `or disjoint` (`m_AddLike`). Output `nuw` iff mul `nuw` and the add-like was `nuw` (an `or` counts as `nuw`) | 335 |

## 5.4 Negation and `abs`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M8 | `abs(X) * abs(X) → X * X` | literally the same value on both sides | 358 |
| M9 | `abs(X) * abs(Y) → abs(X *nsw Y)` | **mul must be `nsw`**; both `abs` must be `is_int_min_poison` (`m_One()` second arg); `1u` on both | 363 |
| M10 | `(-X) * C → X * (-C)` | — **[canon]** | 375 |
| M11 | `(-X) * (-Y) → X * Y` | output `nsw` iff mul and both negs `nsw` | 379 |
| M12 | `(-X) * Y → -(X * Y)` **[comm]** | `1u` on the neg | 388 |
| M13 | `(-X * Y) * (-X) → (X * Y) * X` | `Op1` is a neg and `Negator` succeeds on `Op0` | 393 |

## 5.5 Division cancellation

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M14 | `(X /exact C0) * C1 → X /exact (C0 / C1)` | `1u` on the div; **unsigned:** `C0 % C1 == 0`; **signed:** `C0 sdiv C1` exact **and** the quotient is not `-1` (else `X /s -1` can be UB at `INT_MIN`) | 405 |
| M15 | `(X / Y) * Y → X - (X % Y)` | `1u` on the div; `X` **frozen** if not `isGuaranteedNotToBeUndef` (its use count increases) | 424 |
| M16 | `(X / Y) * (-Y) → (X % Y) - X` | same | 424 |
| M17 | `(X /exact Y) * Y → X` | the `exact` makes the remainder zero | 441 |
| M18 | `(X /exact Y) * (-Y) → -X` | same | 444 |

> **The freeze in M15/M16 is a correctness condition, not profitability.** `X`
> appears once on the left and twice on the right; if `X` were `undef`, the two
> uses could observe different values and `X - (X % X_other)` is not `X`.

## 5.6 Boolean / single-bit multiplies

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M19 | `mul i1 X, Y → X & Y` | type is `i1` | 456 |
| M20 | `(X & 1) * (Y & 1) → (X & 1) & (Y & 1)` | both operands masked to one bit | 456 |
| M21 | `zext(i1 X) * zext(i1 Y) → zext(X & Y)` | same source type; `1u` on one operand or `X == Y` | 470 |
| M22 | `sext(i1 X) * sext(i1 Y) → zext(X & Y)` | same. *(-1 · -1 = 1)* | 470 |
| M23 | `sext(i1 X) * zext(i1 Y) → sext(X & Y)` **[comm]** | same. *(-1 · 1 = -1)* | 481 |
| M24 | `zext(i1 X) * Y → X ? Y : 0` **[comm]** | — | 491 |
| M25 | `sext(i1 X) * Y → X ? -Y : 0` **[comm]** | `1u` on the sext; the `neg` inherits `nsw` | 499 |
| M26 | `sext(i1 X) * C → X ? -C : 0` | `C` is `m_ImmConstant` | 507 |
| M27 | `(X a>> (N-1)) * C → (X <s 0) ? -C : 0` | `1u` on the ashr | 514 |
| M28 | `(X l>> (N-1)) * Y → (X <s 0) ? Y : 0` **[comm]** | deliberately **no** one-use check | 525 |
| M29 | `(X & 1) * Y → trunc(X) ? Y : 0` **[comm]** | `1u` on the and | 532 |
| M30 | `((X a>> (N-1)) \| 1) * X → abs(X)` **[comm]** | the `abs` gets `is_int_min_poison = mul.nsw` | 540 |

## 5.7 Shifted-one factors (`foldMulShl1`, line 142; called twice, both orders)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M31 | `X * (1 << Z) → X << Z` | output `nuw` from the mul; `nsw` iff mul and inner shl both `nsw` | 151 |
| M32 | `X * ((1 << Z) + 1) → (X << Z) + X` | `1u` on the add and the shl; **`X` frozen** if not known non-undef; flags as above | 161 |
| M33 | `X * ~(-1 << Z) → (X << Z) - X` | `1u` on the not and the shl; **`X` frozen**; no flags propagated | 176 |

## 5.8 Select-shaped multiplies (`foldMulSelectToNegate`, line 100)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M34 | `(Cond ? 1 : -1) * Y → Cond ? Y : -Y` **[comm]** | `1u` on the select; the `neg` is `nsw` iff the mul had `nsw` **or** `nuw` | 105 |
| M35 | `(Cond ? -1 : 1) * Y → Cond ? -Y : Y` **[comm]** | same | 114 |

## 5.9 Log2-based

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M36 | `mul Op0, Op1 → Op1 << log2(Op0)` **[comm]** | `tryGetLog2(Op0, AssumeNonZero=false)` must succeed *without creating instructions* (see `takeLog2`, §6.7). Only `nuw` is propagated | 561 |

## 5.10 Flag inference

Line 574: add `nsw` if `willNotOverflowSignedMul`; add `nuw` if
`willNotOverflowUnsignedMul` (which is passed the freshly-updated `nsw`).

## 5.11 `simplifyValueKnownNonZero` (line 47)

A helper used by the div/rem visitors on a *divisor* known non-zero. Requires
`1u`.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| M37 | `(1 << A) >>u B → 1 << (A - B)` | valid only because the value is known non-zero, which forces `B <= A` | 57 |
| M38 | infer `exact` on an `lshr` of a power of two | `isKnownToBeAPowerOfTwo(operand)` and the value is non-zero | 75 |
| M39 | infer `nuw` on a `shl` of a power of two | same | 80 |

