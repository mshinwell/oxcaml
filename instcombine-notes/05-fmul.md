# `InstCombineMulDivRem.cpp` — Part 2: `fmul`

Back to [index](README.md). `visitFMul`, line 953. FMF conventions: see
[Part 3 §3.0](02-addsub-float.md).

Preamble: `simplifyFMulInst`; `SimplifyAssociativeOrCommutative`;
`foldVectorBinop`; `foldBinopWithPhiOperands`; `foldBinOpIntoSelectOrPhi`;
`foldMulSelectToNegate` (M34/M35 in FP form); `foldFPSignBitOps`;
`foldFBinOpOfIntCasts`.

## 6.1 `foldFPSignBitOps` (line 586) — shared with `fdiv`

These are sound **without any FMF** because they only rearrange sign bits.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| P1 | `(-X) * (-Y) → X * Y` | flags copied from the original | 596 |
| P2 | `(-X) / (-Y) → X / Y` | same | 596 |
| P3 | `fabs(X) * fabs(X) → X * X` | literally the same `Value` twice | 601 |
| P4 | `fabs(X) / fabs(X) → X / X` | same | 601 |
| P5 | `fabs(X) * fabs(Y) → fabs(X * Y)` | `1u` on one operand | 606 |
| P6 | `fabs(X) / fabs(Y) → fabs(X / Y)` | same | 606 |

> P5/P6 hold for all inputs including NaN and Inf: `|x|·|y|` and `|x·y|` agree
> in magnitude, and the result sign of the left side is always `+`.
> NaN payload/sign differences are not observable in LLVM's FP model.

## 6.2 Unconditional `fmul` rules

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FM1 | `X * -1.0 → -X` | — | 979 |
| FM2 | `X * ±0.0 → copysign(0.0, ±X)` | needs (`ninf` **and** `isKnownNeverNaN(X)`) **or** `isKnownNeverNaN` of the whole `fmul`. The sign flip on `X` happens only for `-0.0` | 986 |
| FM3 | `(-X) * C → X * (-C)` | the negated constant must fold | 998 |
| FM4 | `SimplifySelectsFeedingBinaryOp` | see Part 12 | 1027 |
| FM5 | `minimum(X,Y) * maximum(X,Y) → X * Y` **[comm]** | **clear `ninf` if not `nnan`** — same reasoning as `fadd` (§3.0 #1) | 1071 |

### Requires `nnan && nsz`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FM6 | `uitofp(i1 X) * Y → X ? Y : 0.0` **[comm]** | `nnan`+`nsz` needed because `Inf * 0.0 == NaN` | 1009 |

### Requires `contract`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FM7 | `tan(X) * cos(X) → sin(X)` **[comm]** | `1u` on both intrinsics; `fpmath` metadata is carried over | 1083 |

### Requires `fast` (all FMF)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FM8 | `log2(X * 0.5) * Y → log2(X)*Y - Y` **[comm]** | `1u` on the `log2` and the inner `fmul` | 1042 |

### Recurrence

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FM9 | an `fmul` recurrence whose PHI start value is `0.0` → `0.0` | `nnan && nsz`; `matchSimpleRecurrence` | 1063 |

---

## 6.3 `foldFMulReassoc` (line 776) — requires `reassoc` on the `fmul`

Note the recurring idiom: when folding `I` with `Op0`, the new instruction's
FMF is the **intersection** `I.getFastMathFlags() & Op0BinOp->getFastMathFlags()`,
not a copy. The inner operation's licences must also hold.

### Constant reassociation (`C` finite and nonzero, `Op0` a `reassoc` binop)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FR1 | `(C1 / X) * C → (C * C1) / X` | `1u` on the fdiv; the folded constant must be **normal** (`isNormalFP`) | 795 |
| FR2 | `(X / C1) * C → X * (C / C1)` | folded constant normal. *(Source FIXME: arguably should also require `arcp`)* | 802 |
| FR3 | `(X / C1) * C → X / (C1 / C)` | fallback when FR2's constant was denormal; `1u`; result normal | 810 |
| FR4 | `(X + C1) * C → (X * C) + (C * C1)` | `1u` on the fadd | 818 |
| FR5 | `(C1 - X) * C → (C * C1) - (X * C)` | `1u` on the fsub | 826 |

> The `isNormalFP` guards exist because materialising a **denormal** constant
> can be slower than the original, and on FTZ targets changes results. They
> are a correctness-adjacent profitability check — keep them when porting to a
> target with flush-to-zero.

### General reassociation

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FR6 | `(X / Y) * Z → (X * Z) / Y` **[comm]** | `1u` on the fdiv; the **intersected** FMF must still have `reassoc` | 837 |
| FR7 | `sqrt(X) * sqrt(Y) → sqrt(X * Y)` | **requires `nnan`** — without it, `X,Y < 0` gives `NaN·NaN = NaN` on the left but `sqrt(positive)` = a number on the right | 851 |
| FR8 | `(1.0/sqrt(X)) * X → X / sqrt(X)` **[comm]** | **requires `nsz`**; no one-use check (deliberate) | 863 |
| FR9 | `(X/sqrt(Y)) * (X/sqrt(Y)) → (X*X) / Y` | `nnan && nsz`; the operand must have exactly 2 uses | 877 |
| FR10 | `(sqrt(Y)/X) * (sqrt(Y)/X) → Y / (X*X)` | same | 883 |
| FR11 | `(X*Y) * X → (X*X) * Y` | `1u` on the inner fmul; `Y != X`. Shortens the critical path and forms a power | 934 |

> **FR9/FR10 need `nsz`** for the reason given in the source: `sqrt(-0.0) =
> -0.0`, and `(-0.0)·(-0.0) = +0.0`, so squaring loses the sign of zero.

### `pow`/`exp`/`powi` reassociation

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FR12 | `pow(X, Y) * X → pow(X, Y+1)` **[comm]** | `1u` on the `pow` | 890 |
| FR13 | `pow(X,Y) * pow(X,Z) → pow(X, Y+Z)` | `I.isOnlyUserOfAnyOperand()` | 903 |
| FR14 | `pow(X,Y) * pow(Z,Y) → pow(X*Z, Y)` | same | 910 |
| FR15 | `exp(X) * exp(Y) → exp(X + Y)` | same | 918 |
| FR16 | `exp2(X) * exp2(Y) → exp2(X + Y)` | same | 925 |
| FR17 | `powi(X, Y) * X → powi(X, Y+1)` **[comm]** | `1u`; the `powi` must itself carry `reassoc`; **`willNotOverflowSignedAdd(Y, 1)`** — the exponent is an *integer* and must not wrap | 632 |
| FR18 | `powi(X,Y) * powi(X,Z) → powi(X, Y+Z)` | `isOnlyUserOfAnyOperand`; both `powi` carry `reassoc`; exponent types equal | 645 |

> **FR17/FR18: the exponent arithmetic is integer.** Overflow there is a real
> soundness issue distinct from the FP semantics, which is why
> `willNotOverflowSignedAdd` appears in an FP fold.

---

## 6.4 `foldPowiReassoc` for `fdiv` (line 617)

Requires `reassoc && nnan` on the `fdiv`.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FR19 | `powi(X, Y) / X → powi(X, Y-1)` | `1u`; inner `reassoc`; `willNotOverflowSignedSub(Y, 1)` | 666 |
| FR20 | `powi(X,Y) / (X * Z) → powi(X, Y-1) / Z` | same, plus the `fmul` carries `reassoc` | 676 |

---

## 6.5 The `1/sqrt` multi-instruction rewrite (lines 693–775)

`getFSqrtDivOptPattern` / `isFSqrtDivToFMulLegal` recognise a *group* of
instructions, not a single one:

```
X  = 1.0 / sqrt(a)      (or -1.0 / sqrt(a))
R1 = X * X              (all such users of X)
R2 = a / sqrt(a)        (all such users of sqrt(a))
   ⟹
r1 = 1/a ;  r2 = sqrt(a) ;  X = r1 * r2
```

Legality (all must hold):

* the `sqrt` call has **`reassoc`, `nnan`, `nsz`, `ninf`**;
* the `fdiv` `X` has **`reassoc`, `arcp`, `ninf`**;
* the `fdiv` and at least one of the multiply groups are in the **same basic
  block** (otherwise the rewrite can execute more work than before);
* every instruction in `R1` is in one block and has `reassoc`; likewise `R2`.

The source notes that `arcp` is being "rather abused" here — the rewrite is an
algebraic one, not a reciprocal substitution. Worth flagging if you re-derive
the FMF requirements for a port.

