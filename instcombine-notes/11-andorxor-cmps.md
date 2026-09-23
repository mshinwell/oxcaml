# `InstCombineAndOrXor.cpp` — Part 11c: `and`/`or`/`xor` of comparisons

Back to [index](README.md). Helpers: [11a](09-andorxor-shared.md).
Visitors: [11b](10-andorxor-visitors.md).

This is the densest group in the pass. Three cross-cutting concepts first.

---

## 11c.0 Three framework concepts

### (a) `IsLogical` — bitwise vs. short-circuit

Every entry point takes an `IsLogical` flag. `IsLogical = true` means the
"and"/"or" is really a `select` (`select C, X, false` = logical and), which
**does not propagate poison from the RHS** when the LHS decides the result.
Consequences that recur throughout:

* A fold that moves the RHS's value into a position where it is always
  evaluated must first prove `isGuaranteedNotToBeUndefOrPoison(RHS)`, or
  insert a `freeze`.
* Where only one direction is safe, the code calls the helper twice: once with
  the real `IsLogical`, once with `IsLogical = false` and the operands swapped,
  with a comment explaining that poison from both sides propagates in that
  direction anyway.
* When a fold keeps the RHS compare alive but changes its meaning, the
  `samesign` flag must be dropped (`RHS->setSameSign(false)`).

**For a port:** if your IR has no short-circuit form at this level, you can
ignore `IsLogical` entirely and take the `false` path.

### (b) Predicate bit-codes

`getICmpCode` maps a predicate to a 3-bit mask over {LT, GT, EQ}; `getFCmpCode`
maps an FP predicate to a 4-bit mask over {UNO, LT, GT, EQ}. Then, for two
compares on the *same operands*:

```
(cmp P1 A, B) & (cmp P2 A, B)  →  cmp (code(P1) & code(P2)) A, B
(cmp P1 A, B) | (cmp P2 A, B)  →  cmp (code(P1) | code(P2)) A, B
(cmp P1 A, B) ^ (cmp P2 A, B)  →  cmp (code(P1) ^ code(P2)) A, B
```

`getNewICmpValue`/`getFCmpValue` turn a code back into a predicate, or into a
`true`/`false` constant when the code is all-ones/zero. For `icmp` the result
is signed if **either** input was signed (`predicatesFoldable` gates this: it
requires the two predicates to have compatible signedness). This single
mechanism subsumes dozens of hand-written rules — **the highest-value thing to
port from this file.**

### (c) The masked-icmp lattice

`getMaskedICmpType` (line 119) classifies `icmp eq/ne (A & B), C` into a
10-element bit-lattice:

| Flag | Meaning (for the `eq` case) |
|---|---|
| `AMask_AllOnes` | true iff `(A & B) == A`, i.e. all bits of `A` set in `B` |
| `BMask_AllOnes` | true iff `(A & B) == B` |
| `Mask_AllZeros` | true iff `(A & B) == 0` |
| `AMask_Mixed` | `(A & B) == C` with `C ⊆ A` |
| `BMask_Mixed` | `(A & B) == C` with `C ⊆ B` |
| `*_Not*` | the same with `!=` |

`conjugateICmpMask` (line 169) flips each flag to its `Not` partner, which is
what lets the code handle `or` by De Morgan on the `and` analysis.

`getMaskedTypeForICmpPair` (line 196) is the matcher: it finds the common
operand `A` across the two compares, writing them as
`icmp (A & B) ==/!= C` and `icmp (A & D) ==/!= E`. Two conveniences:

* Any `icmp` can be read as trivially masked, using `-1` as the mask (but a
  match against that synthetic `-1` is then rejected).
* `decomposeBitTestICmp` turns things like `icmp slt X, 0` into
  `icmp ne (X & signmask), 0` first.

Both predicates must end up being **equalities** or the whole thing bails.

---

## 11c.1 `foldLogOpOfMaskedICmps` (line 527)

Operates on the lattice intersection `Mask = LHSMask & RHSMask`, after
conjugating for `or`. `NewCC` is `eq` for `and`, `ne` for `or`.

| # | Lattice bit | Rule | Extra conditions | Line |
|---|---|---|---|---|
| MI1 | `Mask_AllZeros` | `(A&B)==0 & (A&D)==0 → (A&(B\|D))==0` | if `IsLogical`, `D` must be non-poison | 583 |
| MI2 | `BMask_AllOnes` | `(A&B)==B & (A&D)==D → (A&(B\|D))==(B\|D)` | same | 596 |
| MI3 | `AMask_AllOnes` | `(A&B)==A & (A&D)==A → (A&(B&D))==A` | same | 606 |
| MI4 | `Mask_NotAllZeros`/`BMask_NotAllOnes` | `→ LHS` or `→ RHS` | `B & D` equals one of `B`, `D` (one mask is a superset). If `IsLogical` and RHS is chosen, **drop its poison-generating flags** | 619 |
| MI5 | `AMask_NotAllOnes` | `→ LHS` or `→ RHS` | `B \| D` equals one of `B`, `D` | 637 |
| MI6 | `BMask_Mixed` | `(A&B)==C & (A&D)==E → (A&(B\|D))==(C\|E)` | requires `(B&D) & (C^E) == 0` (the shared bits must agree); otherwise the whole expression is a constant | 650 |
| MI7 | `BMask_NotMixed` | `(A&B)!=C & (A&D)!=E → (A&(B&D))!=(C&E)` | additionally `B ⊆ D` or `D ⊆ B` | 650 |
| MI8 | `Mask_NotAllZeros` | `(A&B)!=0 & (A&D)!=0 → (A&(B\|D))==(B\|D)` | **both `B` and `D` provably powers of two** (`OrZero=false`). If `IsLogical`, `D` is **frozen** | 704 |

### `foldLogOpOfMaskedICmps_NotAllZeros_BMask_Mixed` (line 346)

Handles the *asymmetric* case `Mask == 0`, i.e. `(A&B)!=0 & (A&D)==E`. All of
`B`, `D`, `E` must be constants. `E` is first normalised when `D` is a power of
two.

| # | Rule | Conditions | Line |
|---|---|---|---|
| MX1 | `→ isnan(A)` | `B` and `D` don't intersect; `D == E`; `A` is an element-wise bitcast of an IEEE-like FP value; `E` is the exponent-all-ones pattern and `B` is exactly the fraction bits. Requires **no `strictfp`**. Emits `fcmp uno` (or `ord` for `or`) | 382 |
| MX2 | `→ (A & (B\|D)) == ((B & (B^D)) \| E)` | `(B & D & E) == 0` and `B & (B^D)` is a power of two — *the single bit of `B` outside `D` must be one* | 425 |
| MX3 | `→ false` (or `true` for `or`) | `E == 0` and `B ⊆ D` — the two tests contradict | 456 |
| MX4 | `→ RHS` | `B ⊇ D` and `E != 0` — RHS implies LHS. **Drops `samesign` on RHS** | 470 |
| MX5 | `→ RHS` | `B ⊆ D` and `(B & E) != 0`. Drops `samesign` | 480 |
| MX6 | `→ false` (or `true`) | `B ⊆ D` and `(B & E) == 0` — contradiction | 489 |

> MX3–MX6 are a small decision procedure over the constants, not pattern
> matches. Porting them means porting the case analysis, which is short and
> mechanical; the `isReducible`-style reasoning is where mistakes hide.

---

## 11c.2 `foldAndOrOfICmps` (line 3334) — the main dispatcher

In source order:

| # | Rule | Conditions | Line |
|---|---|---|---|
| AO1 | bit-code combination `(cmp P1 A,B) op (cmp P2 A,B)` | `predicatesFoldable`; operands equal (possibly after a swap) | 3348 |
| AO2 | `foldAndOrOfICmpEqConstantAndICmp` (line 3289) | see below | 3364 |
| AO3 | `foldAndOrOfICmpsWithConstEq` (line 1269) | see below | 3374 |
| AO4 | `foldIsPowerOf2OrZero` (line 936) | see below | 3391 |
| AO5 | `simplifyRangeCheck` (line 717) | **`!IsLogical`** | 3399 |
| AO6 | `foldSignedTruncationCheck` (line 840) | **`IsAnd && !IsLogical`** | 3411 |
| AO7 | `foldIsPowerOf2` (line 966) | | 3415 |
| AO8 | `foldPowerOf2AndShiftedMask` (line 1074) | `IsAnd` only | 3418 |
| AO9 | `foldUnsignedUnderflowCheck` (line 1106) | `!IsLogical` | 3423 |
| AO10 | `(A != 0) \| (B != 0) → (A\|B) != 0` | same predicate and both constants zero; if `IsLogical`, `RHS0` must be non-poison | 3433 |
| AO11 | `(A != -1) \| (B != -1) → (A&B) != -1` | same shape with all-ones | 3444 |
| AO12 | `foldAndOrOfICmpsWithPow2AndWithZero` (line 777) | `!IsLogical` | 3455 |
| AO13 | `(trunc X)==C1 & (X&CA)==C2 → (X & (CA\|CMAX)) == (C1\|C2)` | `1u` on both; the low `SmallBitSize` bits of `CA` and `C2` must be zero | 3468 |
| AO14 | `(X&Y <s 0) \| (X\|Y >s -1) → (X^Y) >s -1` | *"same sign check"*; both must be sign-bit tests with **opposite** senses; `1u` on one | 3499 |
| AO15 | `(X & ExpMask) != 0 && != ExpMask → is_fpclass(X, fcNormal)` | `1u` on both; `X` an element-wise bitcast of IEEE FP; `MaskC` is the +Inf bit pattern; no `noimplicitfloat` | 3529 |
| AO16 | `foldAndOrOfICmpsUsingRanges` (line 1317) | the general fallback, below | 3546 |

### `foldAndOrOfICmpEqConstantAndICmp` (line 3289)

```
(X == C) | (Y u< (X - C))  →  (X - (C+1)) u>= Y       (and the & dual)
```
`1u` on one compare. `Other` is **frozen** when `IsLogical`.

### `foldAndOrOfICmpsWithConstEq` (line 1269) — equality substitution

```
(X == C) && (Y Pred X)  →  (X == C) && (Y Pred C)
(X != C) || (Y Pred X)  →  (X != C) || (Y Pred C)
```
`C` must be non-poison and `X` not itself a constant. If the substituted
compare does not simplify away, `1u` on the other compare is required. This is
the boolean identity `A && B ≡ A && B[A]`.

### `foldIsPowerOf2OrZero` (line 936) / `foldIsPowerOf2` (line 966)

| Rule | Note |
|---|---|
| `(ctpop(X) != 1) & (X != 0) → ctpop(X) u> 1` | **`dropPoisonGeneratingAnnotations()` on the ctpop** and re-queue it; the range attribute must be re-inferred |
| `(ctpop(X) == 1) \| (X == 0) → ctpop(X) u< 2` | same |
| `(X != 0) && (ctpop(X) u< 2) → ctpop(X) == 1` | same |
| `(X == 0) \|\| (ctpop(X) u> 1) → ctpop(X) != 1` | same |

### `simplifyRangeCheck` (line 717)

```
(x >=s 0) & (x <s n)  →  x <u n
(x <s 0)  | (x >s n)  →  x >u n
```
The lower bound must literally be `x >s -1` or `x >=s 0`. The upper compare may
apply a `sext` to `x`. **`n` must be provably non-negative** (`computeKnownBits`).

### `foldSignedTruncationCheck` (line 840)

Combines a *signed truncation check* — `icmp ult (X + 2^k), 2^(k+1)`, meaning
"all bits from `k` up are uniform" — with a bit test `(X & Mask) == 0` on
overlapping bits, into `icmp ult X, 2^k`. Requires the masks to intersect; if
the bit-test mask extends below the sign region, the threshold is lowered to
`umin` of the two. Handles a `trunc` between the two values.

### `foldNegativePower2AndShiftedMask` (line 1008) / `foldPowerOf2AndShiftedMask` (line 1074)

```
((X & B) == 0) & ((X & D) != D)  →  X u< D
```
`B` a negated power of two, `D == E` a shifted mask, and
`countLeadingOnes(B) == countLeadingZeros(D)`. Vector constants are validated
lane by lane; `B` may contain poison lanes.

### `foldUnsignedUnderflowCheck` (line 1106)

```
((A+B) u<  A) && ((A+B) != 0)  →  (0 - X) u<  Y
((A+B) u>= A) || ((A+B) == 0)  →  (0 - X) u>= Y
```
where `X` is whichever of `A`/`B` is **`isKnownNonZero`** and `Y` is the other.
`1u` on one compare.

### `foldAndOrOfICmpsUsingRanges` (line 1317) — the general engine

Both compares must be against constants on the same value `V` (an `add` of a
constant offset on either side is peeled off and subtracted from the range).
Each compare becomes a `ConstantRange` via `makeExactICmpRegion` (inverted for
`and`, so the problem is always a union). Then:

* If `CR1.exactUnionWith(CR2)` succeeds, emit the equivalent `icmp` for the
  union (inverted again for `and`), with an `add` of the range offset if needed.
* If not, and both compares are `1u` and neither range wraps: if the two ranges
  have **equal size and differ in exactly one bit** of both bounds, mask that
  bit off (`and V, ~LowerDiff`) and use the lower range.

This subsumes all "two constant comparisons on the same value" folds.

### `foldEqOfParts` (line 1183)

```
(X0 == Y0) & (X1 == Y1)  →  X01 == Y01
(X0 != Y0) | (X1 != Y1)  →  X01 != Y01
```
where the `Xi`/`Yi` are **adjacent bit-ranges** extracted from common values
(`matchIntPart`, line 1152, recognises `trunc(lshr V, S)` with `1u`). `1u` on
both compares. It also recognises the already-canonicalised spellings
`icmp ult (X^Y), 2^C` (for `eq` of high parts) and `icmp ugt (X^Y), 2^C-1`
(for `ne`), plus the `i1` form `trunc (X ^ Y)`.

---

## 11c.3 `foldLogicOfFCmps` (line 1421)

| # | Rule | Conditions | Line |
|---|---|---|---|
| FC1 | bit-code combination of two `fcmp`s | same operands (after swap). **FMF intersected** | 1442 |
| FC2 | `(ord x, 0) & (ord y, 0) → ord x, y` | **not for logical select**; both RHS must be `+0.0`; same types. FMF intersected | 1451 |
| FC3 | `(uno x, 0) \| (uno y, 0) → uno x, y` | same | 1451 |
| FC4 | `(ord x, 0) & (u* x, inf) → o* x, inf` | `IsAnd`, not logical; `stripSignOnlyFPOps` lets `fabs`/`fneg`/`copysign` wrappers match. *This is `isfinite`* | 1470 |
| FC5 | two `fcmp`s with constants → `llvm.is.fpclass(X, mask0 op mask1)` | `1u` on both; `fcmpToClassTest` must recognise both against the **same value** | 1487 |
| FC6 | `(x olt C) & (x ogt -C) → fabs(x) olt C` | `1u` on both; `PredR == swap(PredL)`; the constants are exact negations (`bitwiseIsEqual(neg(...))`). FMF are **unioned** unless logical, in which case only the LHS's | 1509 |

## 11c.4 `foldLogicOfIsFPClass` (line 1571) — and/or/**xor**

```
op (is_fpclass x, m0), (is_fpclass x, m1)  →  is_fpclass x, (m0 op m1)
```
`1u` on each operand. An operand may also be an `fcmp` that
`fcmpToClassTest` recognises (`matchIsFPClassLikeFCmp`, line 1553) — but at
least one side must already be a real `is_fpclass` call, so the fold never
*introduces* a new class test from two plain `fcmp`s. When one side is a real
intrinsic it is mutated in place.

## 11c.5 `foldXorOfICmps` (line 4349)

| # | Rule | Conditions | Line |
|---|---|---|---|
| XC1 | bit-code `xor` of two compares | `predicatesFoldable`; same operands | 4356 |
| XC2 | `(X >s -1) ^ (Y >s -1) → (X^Y) <s 0` | both are sign-bit tests, **same** sense; `1u` on one | 4375 |
| XC3 | `(X >s -1) ^ (Y <s 0) → (X^Y) >s -1` | sign-bit tests, **opposite** sense | 4375 |
| XC4 | range-based `xor` fold | same value and both constants. Computes `(CR1 ∪ CR2) ∩ ¬(CR1 ∩ CR2)` — the symmetric difference — and emits its equivalent `icmp`. Needs `1u` on one compare if no offset is required, on **both** otherwise | 4388 |
| XC5 | `((X&P)==0) ^ ((Y&P)==0) → ((X^Y)&P) != 0` | `P` a power of two (`OrZero`); both constants zero; `1u` on both. Result predicate is `ne` if the two input predicates matched, `eq` otherwise | 4414 |
| XC6 | `X ^ Y → X & ~Y` via the truth table | fires when **both** `simplifyBinOp(Or, LHS, RHS)` and `simplifyBinOp(And, LHS, RHS)` succeed and pick out one operand each. `Y`'s predicate is inverted **in place**; if `Y` has other uses they are rewritten to a fresh `not Y`, which is only allowed when `canFreelyInvertAllUsersOf(Y)` | 4429 |

> **XC6 is the interesting one.** `X ^ Y ≡ (X | Y) & ¬(X & Y)`. If InstSimplify
> can prove `X | Y ≡ X` and `X & Y ≡ Y` (i.e. `Y ⟹ X`), then
> `X ^ Y ≡ X & ¬Y`. The implementation exploits that the two simplify calls
> return *which* operand, so no implication engine is needed.

## 11c.6 `foldBooleanAndOr` (line 3547) — the entry point

Requires `i1`/`<n x i1>` type, then in order:
`foldLogOpOfMaskedICmps` → `foldAndOrOfICmps` (both `ICmpInst`) →
`foldLogicOfFCmps` (both `FCmpInst`) → `foldEqOfParts`.

Called from `visitAnd`, `visitOr`, and from `visitSelect` for the logical
forms.

