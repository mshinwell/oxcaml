# `InstCombineCompares.cpp` — Part 13c: `fcmp`

Back to [index](README.md). `visitFCmpInst`, line 8518.

## 13c.0 FP comparison semantics

`fcmp` predicates come in **ordered** (`o*`, false if either operand is NaN)
and **unordered** (`u*`, true if either is NaN) flavours, plus `ord`/`uno`
(the NaN test itself). Two facts drive most rules here:

* `fcmp` is exact — it does not round — so unlike `fadd`/`fmul` there is no
  precision-loss condition. The side conditions are all about **NaN, ±0, ±Inf
  and denormals**.
* `-0.0 == +0.0` is `true`, so comparisons cannot distinguish the zeros. That
  is why so many rules canonicalise the RHS to `+0.0`.

**Denormal mode** matters: `Function::getDenormalMode(semantics)` reports
whether denormal inputs are flushed. Two rules below are gated on it.

## 13c.1 Canonicalisation

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FK1 | swap operands by complexity | | 8520 |
| FK2 | `fcmp u* X, X → fcmp uno X, 0.0` | `Op0 == Op1`; covers `uno`, `ult`, `ugt`, `une` | 8534 |
| FK3 | `fcmp o* X, X → fcmp ord X, 0.0` | covers `ord`, `oeq`, `oge`, `ole` | 8542 |
| FK4 | `fcmp ord/uno X, C → fcmp ord/uno 0.0, C` | `isKnownNeverNaN(X)`; the operand's *value* is irrelevant to a NaN test — **[canon]** | 8558 |
| FK5 | `fcmp Pred (-X), (-Y) → fcmp Pred' X, Y` | both negated; predicate swapped | 8567 |
| FK6 | `foldFCmpFNegCommonOp` (line 8384): `fcmp Pred X, (-X) → fcmp Pred X, 0.0` | | 8571 |
| FK7 | `fcmp Pred X, -0.0 → fcmp Pred X, +0.0` | any zero RHS — **[canon]** | 8584 |
| FK8 | `fcmp Pred (-X), C → fcmp Pred' X, (-C)` | the negated constant must fold | 8664 |
| FK9 | `fcmp Pred (X + ±0.0), Y → fcmp Pred X, Y` | adding a zero cannot change any comparison outcome | 8672 |
| FK10 | `matchSymmetricPair` | for commutative predicates | 8551 |
| FK11 | **Bail out** if the sole user is a `select` forming a min/max pattern | same guard as `icmp` | 8575 |

## 13c.2 Comparison with infinity (line 8589)

With `Op1` an infinity (the predicate is first swapped if it is `-Inf`):

| Rule | |
|---|---|
| `X <o Inf → X !=o Inf` | *(finite, given ordered)* |
| `X <=o Inf → ord X, 0.0` | |
| `X >=o Inf → X ==o Inf` | |
| `X <u Inf → X !=u Inf` | |
| `X >u Inf → uno X, 0.0` | |
| `X >=u Inf → X ==u Inf` | |

`ogt`/`ule` against `+Inf` are asserted to have been handled by InstSimplify.

## 13c.3 `fabs` — `foldFabsWithFcmpZero` (line 8223)

For `fcmp Pred (fabs X), +0.0`, the whole predicate table is rewritten to act
on `X` directly:

| Input | Output |
|---|---|
| `fabs(X) >o 0` | `X !=o 0` |
| `fabs(X) >u 0` | `X !=u 0` |
| `fabs(X) <=o 0` | `X ==o 0` |
| `fabs(X) <=u 0` | `X ==u 0` |
| `fabs(X) >=o 0` | `ord X, 0` *(requires the compare to not be `nnan` — else it simplifies)* |
| `fabs(X) <u 0` | `uno X, 0` *(same)* |
| `oeq ueq one une ord uno` | unchanged predicate, operand replaced by `X` |

A second case handles `fcmp Pred (fabs X), smallest_normal` **when the
denormal input mode is `PreserveSign` or `PositiveZero`** — then
`|X| < smallest_normal` is equivalent to `X == 0`:

| Input | Output |
|---|---|
| `fabs(X) <o smallest_normal` | `X ==o 0` |
| `fabs(X) >=u smallest_normal` | `X !=u 0` |
| `fabs(X) >=o smallest_normal` | `X !=o 0` |
| `fabs(X) <u smallest_normal` | `X ==u 0` |

## 13c.4 `sqrt` — `foldSqrtWithFcmpZero` (line 8324)

For `fcmp Pred (sqrt X), +0.0`. Because `sqrt` of a negative is NaN and
`sqrt(±0) = ±0`, the comparison against zero can be pushed onto `X`:

| Input | Output |
|---|---|
| `ult ule ogt oge oeq une` | same predicate on `X` |
| `sqrt(X) <=o 0` | `X ==o 0` |
| `sqrt(X) >u 0` | `X !=u 0` |
| `sqrt(X) ==u 0` | `X <=u 0` |
| `sqrt(X) !=o 0` | `X >o 0` |
| `ord sqrt(X), 0` | `X >=o 0` |
| `uno sqrt(X), 0` | `X <u 0` |

**`ninf` is cleared on the compare** if the `sqrt` call did not have it
(line 8338) — `sqrt` of a finite value is finite, but the reverse does not
follow once the operand is exposed.

## 13c.5 `floor` / `ceil` — `foldFCmpWithFloorAndCeil` (line 8449)

`fcmp Pred (floor X), X` and `fcmp Pred (ceil X), X` (operands swappable):

| Input | Output |
|---|---|
| `floor(X) <=o X` | `ord X, 0.0` *(always true for non-NaN)* |
| `floor(X) >o X` | `false` |
| `ceil(X) >=o X` | `ord X, 0.0` |
| `ceil(X) <o X` | `false` |
| …and the unordered duals | |

## 13c.6 Comparison with a constant, by LHS opcode (line 8620)

| LHS | Rule | Line |
|---|---|---|
| `select` | `fcmp eq/ne (select C, X, -X), ±0.0 → fcmp eq/ne X, ±0.0` | 8623 |
| `select` | `FoldOpIntoSelect` | 8628 |
| `fsub` | `foldFCmpFSubIntoFCmp` (line 8403) — see below | 8632 |
| `phi` | `foldOpIntoPhi` | 8637 |
| `sitofp`/`uitofp` | `foldFCmpIntToFPConst` (line 7937) — see below | 8642 |
| `fdiv` | `foldFCmpReciprocalAndZero` (line 8176) — see below | 8647 |
| `load` | `foldCmpLoadFromIndexedGlobal` (shared with `icmp`) | 8651 |

### `foldFCmpFSubIntoFCmp` (line 8403)

```
fcmp Pred (X - Y), 0.0   →   fcmp Pred X, Y
```

* **Always valid** for `ogt olt one ueq uge ule`.
* For `ugt ult une oeq oge ole` it needs the `fsub` to be `nnan` or `ninf`,
  or `isKnownNeverInfinity` on `X` or `Y` — because `Inf - Inf = NaN` would
  change the answer.
* **Requires `DenormalMode::getIEEE()`** for the type: with flush-to-zero, a
  tiny nonzero difference would compare equal to zero on the left but not on
  the right.
* `1u` on the `fsub`.

### `foldFCmpReciprocalAndZero` (line 8176)

```
fcmp Pred (C / X), 0.0   →   fcmp Pred X, 0.0      [predicate swapped if C < 0]
```
* Ordered relational predicates only (`ogt olt oge ole`).
* **Both the `fdiv` and the `fcmp` must have `ninf`** — otherwise `C/±Inf`
  is `±0` and the sign information is lost.
* `C` nonzero.

### `foldFCmpIntToFPConst` (line 7937)

`fcmp Pred (sitofp/uitofp X), C` → an `icmp` on `X`. The implementation
computes the exact integer range that maps to each side of `C`, handling:
rounding direction, whether `C` is representable exactly, constants outside
the integer type's range (folding to `true`/`false`), and the `ord`/`uno`
cases (an int→FP conversion is never NaN, so `ord` is `true`).

## 13c.7 Bit-level folds

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FB1 | `fcmp oeq/une (bitcast X), +0.0 → icmp eq/ne (X & ~signmask), 0` | `1u` on the element-wise bitcast. *Tests "is ±0" as an integer* | 8604 |
| FB2 | `fcmp olt (copysign C, X), 0.0 → icmp slt (bitcast X), 0` | `1u` on the `copysign`; `C` a nonzero non-NaN constant; RHS any zero | 8710 |

## 13c.8 `fpext`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FE1 | `fcmp Pred (fpext X), (fpext Y) → fcmp Pred X, Y` | same source type | 8680 |
| FE2 | `fcmp oeq (fpext X), C → false` | `C` is **not representable** in the narrow type | 8690 |
| FE3 | `fcmp one (fpext X), C → ord X, 0.0` | same | 8692 |
| FE4 | `fcmp ueq (fpext X), C → uno X, 0.0` | same | 8695 |
| FE5 | `fcmp une (fpext X), C → true` | same | 8698 |
| FE6 | `fcmp Pred (fpext X), C → fcmp Pred X, (fptrunc C)` | `C` **is** exactly representable, **and** the truncated value is zero or at least the smallest normal — denormal results are refused because targets differ | 8704 |

## 13c.9 `canonicalize` (line 8722)

| # | Rule | |
|---|---|---|
| FC1 | `fcmp Pred (canonicalize X), X → fcmp Pred X, X` | |
| FC2 | `fcmp Pred X, (canonicalize X) → fcmp Pred X, X` | |
| FC3 | `fcmp Pred (canonicalize X), (canonicalize Y) → fcmp Pred X, Y` | |

## 13c.10 Vectors

`foldVectorCmp` (line 7306), shared with `icmp`: push the compare through
`vector.reverse` and through identical shuffles, and re-splat a constant when
the shuffle mask is a splat.

