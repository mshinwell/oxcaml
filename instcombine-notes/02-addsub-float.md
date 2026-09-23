# `InstCombineAddSub.cpp` — Part 3: `fadd`, `fsub`, `fneg`

Back to [index](README.md).

## 3.0 Fast-math flags — the FP analogue of `nsw`/`nuw`

Almost every FP rule below is gated on fast-math flags (FMF). Unlike integer
no-wrap flags, FMF are a *licence to be inaccurate*, not (only) a poison
premise. Getting the propagation right is the hard part of porting these.

| Flag | Licence |
|---|---|
| `nnan` | assume no operand and no result is NaN (else poison) |
| `ninf` | assume no operand and no result is ±Inf (else poison) |
| `nsz` | the sign of a zero result is not observed — `+0.0` and `-0.0` are interchangeable |
| `arcp` | `X / Y` may become `X * (1/Y)` |
| `contract` | may fuse into FMA |
| `afn` | may use a lower-precision approximation |
| `reassoc` | may reassociate and distribute |

Rules of thumb that the code follows:

* **`reassoc` alone is not enough** for most algebraic rewrites; the pass
  almost always demands `reassoc && nsz` together (`I.hasAllowReassoc() &&
  I.hasNoSignedZeros()`). Reason: reassociation that cancels terms can turn
  `-0.0` into `+0.0`. e.g. `(0.0 + -0.0) = +0.0` but `-0.0 + 0.0 = +0.0`, while
  `X - X = +0.0` under default rounding regardless of `X`'s sign — so any fold
  producing a literal zero needs `nsz`.
* **New instructions copy FMF from the instruction being replaced** — that is
  what the `...FMF(..., &I)` builder suffix means. This is *not* always sound
  on its own; see the explicit intersections below.
* **Intersecting rather than copying** is required whenever the new operation
  has a special-value behaviour the old one did not. The code does this in
  three places and they are the places most worth re-deriving when porting.

### The three explicit FMF intersections

1. **`minimum(X,Y) + maximum(X,Y) → X + Y`** (`visitFAdd`, line 2085).
   If the result is not `nnan`, `ninf` must be **cleared** on the new `fadd`.
   *Why:* with `X = NaN`, `Y = Inf`, the original computes `NaN + NaN`; the new
   one computes `NaN + Inf`. Under `ninf` the new form is poison where the old
   was not.
2. **`-(C / X) → (-C) / X`** (`foldFNegIntoConstant`, line 2921).
   `nsz` and `ninf` on the new `fdiv` are the **conjunction** of the `fneg`'s
   and the `fdiv`'s, because the special-value exceptions that justified those
   flags on the `fneg` may not hold for the `fdiv`.
3. **`-(X * C) → X * (-C)`** (line 2905). Uses
   `FastMathFlags::unionValue ∪ intersectRewrite`, then forces
   `ninf = fneg.ninf && fmul.ninf`. The union/intersect split distinguishes
   flags that are *value assertions* about operands (unioned, since the operand
   set is unchanged) from flags that *licence rewrites* (intersected).
4. **`fneg (copysign X, Y) → copysign X, (fneg Y)`** (line 3046): FMF are
   intersected, because `copysign` has a second value input whose flags the
   `fneg` never covered.
5. **`fneg (select ...)`** (line 2999): `nsz` must be **dropped** unless the
   original select had it, the two arms do not share the common operand, and
   the condition is guaranteed not undef/poison.

---

## 3.1 `visitFNeg` (line 2975)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FN1 | `-(X * C) → X * (-C)` | `1u` on the operand; FMF intersection #3 above | 2905 |
| FN2 | `-(X / C) → X / (-C)` | `1u` | 2916 |
| FN3 | `-(C / X) → (-C) / X` | `1u`; FMF intersection #2 | 2920 |
| FN4 | `-(X + C) → (-C) - X` | `1u`; **requires `nsz`**. Counter-example without it: `-(-0.0 + 0.0) = -0.0` but `0.0 + -0.0 = +0.0` | 2937 |
| FN5 | `-(X - Y) → Y - X` | **requires `nsz`**; `1u` | 2984 |

Everything below additionally requires `1u` on the `fneg` operand.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FN6 | `-(X * Y) → X * (-Y)` | pushes the negation to the RHS (more likely to fold) — **[canon]** | 2944 |
| FN7 | `-(X / Y) → (-X) / Y` | — | 2951 |
| FN8 | `-ldexp(X, E) → ldexp(-X, E)` | FMF are unioned; metadata preserved | 2957 |
| FN9 | `-(Cond ? -P : Y) → Cond ? P : -Y` | `nsz` handling per #5 above | 3005 |
| FN10 | `-(Cond ? X : -P) → Cond ? -X : P` | same | 3013 |
| FN11 | `-(Cond ? X : C) → Cond ? -X : -C` | at least one arm is an `m_ImmConstant` | 3022 |
| FN12 | `fneg (copysign X, Y) → copysign X, (fneg Y)` | FMF intersected, per #4 | 3033 |
| FN13 | `fneg (shuffle X, poison, M) → shuffle (fneg X), M` | second shuffle operand must be `poison` | 3045 |
| FN14 | `fneg (vector.reverse X) → vector.reverse (fneg X)` | — | 3049 |

---

## 3.2 `visitFAdd` (line 1988)

Preamble: `simplifyFAddInst`; `SimplifyAssociativeOrCommutative`;
`foldVectorBinop`; `foldBinopWithPhiOperands`; `foldBinOpIntoSelectOrPhi`.

### Unconditional (no FMF required)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FA1 | `(-X) + Y → Y - X` **[comm]** | — **[canon]** | 2007 |
| FA2 | `((-X) * Y) + Z → Z - (X * Y)` **[comm]** | `1u` on the `fmul` | 2013 |
| FA3 | `((-X) / Y) + Z → Z - (X / Y)` **[comm]** | `1u` on the `fdiv`; also matches `X / (-Y)` | 2021 |
| FA4 | `foldFBinOpOfIntCasts` | see Part 12 — merges `sitofp`/`uitofp` operands into an integer add | 2031 |
| FA5 | `SimplifySelectsFeedingBinaryOp` | see Part 12 | 2037 |
| FA6 | `minimum(X,Y) + maximum(X,Y) → X + Y` **[comm]** | FMF intersection #1 (clear `ninf` if not `nnan`) | 2085 |

### Requires `reassoc && nsz`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FA7 | `(X*Z) + (Y*Z) → (X+Y)*Z` | `1u` on both operands; bail out if `X+Y` folds to a **denormal** constant | 1943 |
| FA8 | `(X/Z) + (Y/Z) → (X+Y)/Z` | same | 1943 |
| FA9 | `(Y * (1.0 - Z)) + (X * Z) → Y + Z*(X - Y)` | lerp; `1u` throughout; 8 commuted variants | 1927 |
| FA10 | `a*a + 2ab + b*b → (a+b)²` | `foldSquareSumFP`; `2x` matched as `x * 2.0` | 1069 |
| FA11 | `vector.reduce.fadd(±0.0, X) + Y → vector.reduce.fadd(Y, X)` **[comm]** | `1u` on the reduction; start value must be any zero FP | 2048 |
| FA12 | `vector.reduce.fadd(StartC, X) + C → vector.reduce.fadd(C + StartC, X)` | `1u` | 2057 |
| FA13 | `(X * MulC) + X → X * (MulC + 1.0)` **[comm]** | `MulC` is an `m_ImmConstant`; the new constant must actually constant-fold | 2067 |
| FA14 | `((-X) - Y) + (X + Z) → Z - Y` **[comm]** | — | 2076 |
| FA15 | `FAddCombine::simplify` | the n-ary reassociation engine, see §3.4 | 2081 |

---

## 3.3 `visitFSub` (line 3067)

Preamble: `simplifyFSubInst`; `foldVectorBinop`; `foldBinopWithPhiOperands`.

### Unconditional

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FS1 | `fsub -0.0, X → fneg X` | **[canon]** — `-0.0 - X` *is* the canonical spelling of `fneg`. Also `fsub nsz 0.0, X → fneg nsz X`. **Known gap:** the matcher ignores FTZ/DAZ, where `-0.0 - denorm` flushes to `±0` but `fneg denorm` does not | 3082 |
| FS2 | `foldFNegIntoConstant` | FN1–FN4 above, applied to the `fsub`-as-`fneg` form | 3085 |
| FS3 | `Z - (X - Y) → Z + (Y - X)` | needs `nsz` **or** `cannotBeNegativeZero(Z)`; `1u` on the inner `fsub` — **[canon]** toward `fadd` | 3100 |
| FS4 | `(-X) - Y → -(X + Y)` | needs `nsz`; `1u` on the `fneg`; `Op0` must not be a `ConstantExpr` | 3108 |
| FS5 | `C - select(...)` → sink into the select | `FoldOpIntoSelect` | 3114 |
| FS6 | `X - C → X + (-C)` | `C` is an `m_ImmConstant` (not a `ConstantExpr`, because the inverse fold exists) — **[canon]** | 3122 |
| FS7 | `X - (-Y) → X + Y` | — | 3127 |
| FS8 | `X - fptrunc(-Y) → X + fptrunc(Y)` | `1u` | 3133 |
| FS9 | `X - fpext(-Y) → X + fpext(Y)` | `1u` | 3137 |
| FS10 | `Op0 - ((-X) * Y) → Op0 + (X * Y)` **[comm]** | `1u` on the `fmul` | 3143 |
| FS11 | `Op0 - ((-X) / Y) → Op0 + (X / Y)` | `1u`; also `X / (-Y)` | 3149 |
| FS12 | `SimplifySelectsFeedingBinaryOp` | Part 12 | 3156 |

### Requires `reassoc && nsz`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FS13 | `(Y - X) - Y → -X` | — | 3161 |
| FS14 | `Y - (X + Y) → -X` **[comm]** | — | 3166 |
| FS15 | `(X * C) - X → X * (C - 1.0)` | new constant must fold | 3170 |
| FS16 | `X - (X * C) → X * (1.0 - C)` | new constant must fold | 3177 |
| FS17 | `((X - Y) + Z) - W → (X + Z) - (Y + W)` | `1u` on the `fadd` and the inner `fsub`; shortens dependency chains | 3187 |
| FS18 | `reduce.fadd(A0,V0) - reduce.fadd(A1,V1) → reduce.fadd(A0, V0-V1) - A1` | `1u` on both; same vector type | 3199 |
| FS19 | `factorizeFAddFSub`: `(X*Z)-(Y*Z) → (X-Y)*Z`, `(X/Z)-(Y/Z) → (X-Y)/Z` | `1u` on both; denormal-result bail-out | 3210 |
| FS20 | `FAddCombine::simplify` | §3.4 | 3217 |
| FS21 | `(X - Y) - W → X - (Y + W)` | `1u` on the inner `fsub` | 3220 |

---

## 3.4 `FAddCombine` — the n-ary FP reassociation engine (lines 41–750)

This is not a peephole but a small symbolic simplifier, invoked from `visitFAdd`
and `visitFSub` under `reassoc && nsz`. Worth treating as a single unit when
porting (or skipping entirely — the source comment at line 3212 says its job
belongs in a dedicated reassociation pass).

**Representation.** An expression is a vector of *addends*, each a pair
`<C, V>` meaning `C * V`, where `C` is a small integer (range `[-4, 4]`) or an
`APFloat`, and `V == nullptr` denotes a constant addend.

**Decomposition** (`drillValueDownOneStep`, line 340):

| Input | Addends |
|---|---|
| `A + B` | `<1,A>, <1,B>` |
| `A - B` | `<1,A>, <-1,B>` |
| `0 - B` | `<-1,B>` |
| `C * A` | `<C,A>` |
| `A + C` | `<1,A>, <C,null>` |

Note zero operands are dropped, which is exactly where `nsz` is needed.

**Algorithm** (`simplifyFAdd`, line 514):
1. Flatten the `fadd`/`fsub` into at most 5 addends by drilling down one level
   through each operand (so at most two neighbouring instructions).
2. Sum the coefficients of addends with identical symbolic values.
3. Drop zero-coefficient addends.
4. Rebuild, but **only if the instruction count does not increase** — the quota
   is the original instruction count, and `createNaryFAdd` refuses to exceed it.

**Coefficient materialisation** (`createAddendVal`, line 723): coefficient `1`
emits the value itself, `-1` emits an `fneg`, anything else an `fmul`.

