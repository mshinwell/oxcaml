# `InstCombineMulDivRem.cpp` — Part 4: `fdiv`, `urem`, `srem`, `frem`

Back to [index](README.md).

# 8. `fdiv` (`visitFDiv`, line 2111)

Preamble: `simplifyFDivInst`; `foldVectorBinop`; `foldBinopWithPhiOperands`;
`foldFDivConstantDivisor`; `foldFDivConstantDividend`; `foldFPSignBitOps`
(P2/P4/P6 above).

## 8.1 `foldFDivConstantDivisor` (line 1891)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FD1 | `(-X) / C → X / (-C)` | the negated constant must fold | 1898 |
| FD2 | `X / +0.0 → copysign(inf, X)` | requires `nnan`. With `nsz` as well, any zero divisor qualifies | 1905 |
| FD3 | `X / C → X * (1/C)` | `C` has an **exact** FP inverse; **or** `arcp` and `C` is a normal FP. In both cases the computed reciprocal must itself be **normal** (denormals rejected: target behaviour varies) | 1919 |

## 8.2 `foldFDivConstantDividend` (line 1936)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FD4 | `C / (-X) → (-C) / X` | negated constant must fold | 1944 |
| FD5 | `C / (X * C2) → (C / C2) / X` | needs **`reassoc` and `arcp`**; result constant must be normal | 1955 |
| FD6 | `C / (X / C2) → (C * C2) / X` | same | 1958 |

## 8.3 `visitFDiv` body

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FD7 | the `1/sqrt(a)` group rewrite | `isFSqrtDivToFMulLegal`, see [§6.5](05-fmul.md) | 2152 |
| FD8 | `C / select(...)`, `select(...) / C` | `FoldOpIntoSelect` | 2159 |
| FD9 | `X / fabs(X) → copysign(1.0, X)` **[comm]** | requires **`nnan` and `ninf`** | 2222 |
| FD10 | `pow(X, Y) / X → pow(X, Y-1)` | requires `reassoc`; `1u` on the pow | 2238 |
| FD11 | `foldPowiReassoc` | FR19/FR20 | 2247 |

### Requires `reassoc && arcp`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FD12 | `(X / Y) / Z → X / (Y * Z)` | `1u` on the inner fdiv; not both `Y` and `Z` constants (else FD5/FD6 loop) | 2170 |
| FD13 | `Z / (X / Y) → (Y * Z) / X` | same | 2176 |
| FD14 | `Z / (1.0 / Y) → Y * Z` | **no one-use check**: even with multiple uses the instruction count is unchanged and a division becomes a multiplication | 2187 |
| FD15 | `Z / pow(X, Y) → Z * pow(X, -Y)` | `1u` on the intrinsic. Creates an extra instruction, judged worthwhile | 1971 |
| FD16 | `Z / exp(Y) → Z * exp(-Y)`, same for `exp2` | same | 2004 |
| FD17 | `Z / powi(X, Y) → Z * powi(X, -Y)` | **also requires `ninf`** — the integer exponent negation `-INT_MIN` wraps, and the comment argues the resulting `0.0`/`~1.0`/`INF` confusion is only acceptable if INF is ruled out | 1994 |
| FD18 | `X / sqrt(Y / Z) → X * sqrt(Z / Y)` | the `sqrt` and the inner `fdiv` must each have `reassoc` (+`arcp` on the sqrt), each `1u` | 2017 |

### Requires `reassoc` only

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FD19 | `sin(X) / cos(X) → tan(X)` | `1u` on both; the target must have a `tan` libfunc (`hasFloatFn`) | 2196 |
| FD20 | `cos(X) / sin(X) → 1.0 / tan(X)` | same | 2196 |

### Requires `reassoc && nnan`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FD21 | `X / (X * Y) → 1.0 / Y` **[comm]** | `nnan` lets `X/X → 1.0`; the source notes `X = Inf` is fine because `Inf/Inf = NaN` is excluded by `nnan` | 2212 |

---

# 9. `urem` / `srem`

## 9.1 `commonIRemTransforms` (line 2370)

Runs `commonIDivRemTransforms` (D1–D6) first.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| R1 | `select(...) % C` → sink into the select | `FoldOpIntoSelect` | 2378 |
| R2 | `phi(...) % C` → sink into the phi | **only if the rem cannot fault after speculation**: `C != 0`, and for `srem` also `C != INT_MIN`. `foldOpIntoPhi` speculates into predecessors | 2382 |
| R3 | `SimplifyDemandedInstructionBits` | Part 11; only when `Op1` is a constant | 2395 |
| R4 | `simplifyIRemMulShl` | §9.2 | 2400 |

## 9.2 `simplifyIRemMulShl` (line 2261)

Matches `rem (mul X, Y), (mul X, Z)` where a `shl` by a constant counts as a
multiply by `2^k`, and `shl C, X` counts too (then `X` is the shift amount and
the constants are the bases). Let `RemYZ = Y srem/urem Z`.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| R5 | `→ 0` | `RemYZ == 0` and `Op0` has the relevant no-wrap flag (`nsw` for `srem`, `nuw` for `urem`) | 2340 |
| R6 | `→ X * Y` (or `Y << X`) | `RemYZ == Y` and **`Op1`** has the no-wrap flag. Output `nsw` set if `srem` or `Op0` had `nsw`; `nuw` set if `urem` or `Op0` had `nuw` | 2356 |
| R7 | `→ X * RemYZ` | `Y >=u Z`; for `srem`, both `Op0` and `Op1` need `nsw`; for `urem`, `Op0` needs `nuw`. Output always `nsw`; `nuw` copied from `Op0` | 2363 |

> **`PreserveNSW` subtlety** (line 2277): when a `shl X, k` is reinterpreted as
> `mul X, 2^k`, its `nsw` may only be believed if `k < N-1`. At `k == N-1`,
> `shl nsw` and `mul nsw` are not the same condition — same issue as `mul` rule
> M3.

## 9.3 `visitURem` (line 2406)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| UR1 | `narrowUDivURem` | U7–U9 | 2416 |
| UR2 | `X %u Y → X & (Y - 1)` | `isKnownToBeAPowerOfTwo(Y, OrZero=true)`. **May increase instruction count** — `Y` need not be constant | 2422 |
| UR3 | `1 %u X → zext(X != 1)` | — | 2431 |
| UR4 | `Op0 %u C → Op0 <u C ? Op0 : Op0 - C` | `C` is negative-as-signed (`C >= signbit`), so the quotient is 0 or 1. **`Op0` frozen** | 2439 |
| UR5 | `Op0 %u sext(i1 X) → (Op0 == -1) ? 0 : Op0` | the divisor is `-1` or `0`; the latter is UB. **`Op0` frozen** | 2453 |
| UR6 | `(X + 1) %u Op1 → ((X+1) == Op1) ? 0 : X+1` | `simplifyICmpInst(X <u Op1)` must prove true. **`Op0` frozen** | 2466 |

## 9.4 `visitSRem` (line 2478)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| SR1 | `X %s (-C) → X %s C` | `C != INT_MIN` | 2490 |
| SR2 | `(-X) %s Y → -(X %s Y)` | `1u` on the `nsw neg`; result is `nsw neg` | 2495 |
| SR3 | `X %s Y → X %u Y` | sign bit known zero in **both** operands | 2501 |
| SR4 | flip negative lanes of a constant vector divisor positive | not applied if any element is missing/undef; skipped if the result equals the original (avoids looping on `INT_MIN`) | 2508 |

## 9.5 `visitFRem` (line 2549)

Only `simplifyFRemInst`, `foldVectorBinop` and `foldBinopWithPhiOperands` —
**no peepholes at all**. A useful data point for a port: `frem` is rarely worth
rewriting.

