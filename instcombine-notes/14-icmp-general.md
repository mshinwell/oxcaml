# `InstCombineCompares.cpp` — Part 13b: `icmp` with non-constant operands

Back to [index](README.md). Framework and `icmp X, C`: [13a](13-icmp-constants.md).

---

## 13b.1 `foldICmpBinOp` (line 5139) — both sides may be binops

Runs only if at least one operand is a `BinaryOperator`.

### The no-wrap-problem framework (line 5201)

```cpp
hasNoWrapProblem(BO, Pred) =
    isEquality(Pred)                          // any wrap is fine
  || (isUnsigned(Pred) && BO.hasNoUnsignedWrap())
  || (isSigned(Pred)   && BO.hasNoSignedWrap())
  || BO is an `or`                            // `or` never wraps
```

This single predicate gates the whole "cancel a common addend" family. Note
the last case: an `or` is treated as having **both** `nuw` and `nsw`, which is
true because it never produces a carry.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| BX1 | `foldICmpXNegX` (line 4950): `icmp Pred (-nsw X), X → icmp Pred' X, 0` | signed → swapped; unsigned → **signedness flipped**. Equality form without `nsw`: `(-X) ==/!= X → (X & SMAX) ==/!= 0` with `1u` | 5148 |
| BX2 | `(X + Y) <u Y → (~Y) <u X` | `1u` on the add; `ult`/`uge` only | 5153 |
| BX3 | `((X + Y) + C) <u Y → (~C - X) <u Y` | `1u`; `ult`/`uge` | 5163 |
| BX4 | `(X & -2^k) ==/!= signmask → X <s/>=s (signmask - -2^k)` | equality; RHS is the sign mask | 5180 |
| BX5 | `((Y + (2^k-1)) & (2^k-1)) <u Y → Y != 0` | `ult`/`uge`, and the mirror for `ugt`/`ule` | 5192 |
| BX6 | `(A + B) pred B → A pred 0` | `hasNoWrapProblem` on the add | 5232 |
| BX7 | `(A + B) pred (C + D) → Y pred Z` | the two add-likes share an operand; `hasNoWrapProblem` on **both** | 5240 |
| BX8 | `(A + B) <u X → A <=u X` | relational only; `hasNoWrapProblem`; `ShareCommonDivisor`: the offset `B` is `±1`, or `|B|` is a positive constant that divides both `A` and `X` (`isMultipleOf`, line 5125, via `MaskedValueIsZero`). *Tightens strictness* | 5264 |
| BX9 | `(A + C1) pred (C + C2) → (A + (C1-C2)) pred C` | both no-wrap; `1u` on one; not unsigned; `C1`, `C2` same sign. New `nuw` only if the difference doesn't exceed the original | 5286 |
| BX10 | `(A - B) pred B → 0 pred B` | `hasNoWrapProblem` | 5330 |
| BX11 | `(A - B) >u A → B >u A` | plain unsigned reasoning about subtraction underflow | 5338 |
| BX12 | `(A - B) >=u A → B >u A` | plus `isKnownNonZero(B)`; tightens to strict | 5346 |
| BX13 | `(A - B) pred (C - B) → A pred C` | both no-wrap | 5356 |
| BX14 | `(A - B) pred (A - D) → D pred B` | both no-wrap | 5359 |
| BX15 | `(-X) pred C → X pred' (-C)` | signed; `hasNoWrapProblem`; `C != INT_MIN` | 5362 |
| BX16 | `foldICmpXorXX` (line 5079) | see below | 5371 |
| BX17 | `foldICmpOrXX` (line 5044) | see below | 5374 |
| BX18 | `(X * Z) pred (Y * Z)` → `X pred Y` | see the multiply block below | 5379 |
| BX19 | `(X %s Y) pred Y` → a sign test on `Y` | equality folds to a constant; `sgt`/`sge` → `Y >s -1`; `slt`/`sle` → `Y <s 0` | 5430 |
| BX20 | `(A op X) pred (B op X) → A pred B` | same opcode, same RHS operand, `1u` on one. Per-opcode conditions in the table below | 5452 |
| BX21 | `(Y & (X-1)) <u X → X != 0` | | 5534 |
| BX22 | `(X << 1) pred X → X pred' 0` | unsigned predicate becomes **signed** | 5545 |
| BX23 | `foldMultiplicationOverflowCheck` (line 4882) | recognises open-coded `umul`/`smul` overflow checks | 5556 |
| BX24 | `foldICmpAndXX` (line 4982) | see below | 5559 |
| BX25 | `foldICmpWithTruncSignExtendedVal` | in `InstCombineInternal` | 5562 |
| BX26 | `foldShiftIntoShiftInAnotherHandOfAndInICmp` | ditto | 5565 |

### BX20's per-opcode table (line 5452)

| Opcode | Condition |
|---|---|
| `add`, `sub`, `xor` | equality: always. Non-equality: the common operand must be the **sign mask** (flip signedness), or for `xor` the **max signed value** (flip signedness *and* swap) |
| `mul` | equality only; the constant must have trailing zeros, and the fold becomes `(A & lowmask) pred (B & lowmask)` masking off those bits |
| `udiv`, `lshr` | unsigned predicate and **both `exact`** |
| `sdiv` | equality or a non-negative divisor, and both `exact` |
| `ashr` | both `exact` |
| `shl` | both `nuw`, or both `nsw`; a signed predicate additionally requires `nsw` |

### The multiply block (line 5379)

`icmp (X * Z), (Y * Z)`:

* **Signed predicate, both `nsw`:** if `Z` is known strictly positive →
  `X pred Y`; known negative → swapped predicate. If `X <s Y` is statically
  true → the compare becomes a sign test on `Z`; likewise `X >s Y`.
* **Equality:** if both are `nsw` or both `nuw` and `isKnownNonEqual(X, Y)`
  → `Z == 0`. If `Z` is known odd → `X pred Y`. If `Z` is nonzero and both
  `nsw` → `X pred Y`.
* **Unsigned relational:** `Z` nonzero and both `nuw` → `X pred Y`.

### `foldICmpAndXX` (line 4982) — `icmp (X & Y), X`

| Rule | Condition |
|---|---|
| `(X & Y) <u X → (X & Y) != X` | — |
| `(X & Y) >=u X → (X & Y) == X` | — |
| `(X & Y) ==/!= X → (Y \| ~X) ==/!= -1` | equality; `1u`; `~X` freely invertible; `X` not an `m_ImmConstant` |
| `(X & Y) ==/!= X → (X & ~Y) ==/!= 0` | equality; `1u`; `~Y` freely invertible |
| signed → unsigned predicate | `Y` known negative |
| `(X & Y) <=s X → X >=s 0` | `Y` known non-negative; `sle`/`sgt` only |
| `(X & Y) <=s X → Y >=s 0` | `X` known negative |

### `foldICmpOrXX` (line 5044) — `icmp (X \| Y), X`

`(X|Y) <=u X → (X|Y) == X`; `(X|Y) >u X → (X|Y) != X`; and the two
equality-with-inversion forms mirroring `foldICmpAndXX`.

### `foldICmpXorXX` (line 5079) — `icmp (X ^ Y), X`

* Tighten a non-strict predicate to strict when `isKnownNonZero(Y)`.
* When `Y` is a **negative constant**: `(X^Y) <s X` and `(X^Y) >u X` both
  become `X <s 0`; `(X^Y) >s X` and `(X^Y) <u X` become `X >=s 0`.

## 13b.2 `foldICmpCommutative` (line 7471) — tried in both operand orders

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CC1 | `foldGEPICmp` | §13b.5 | 7474 |
| CC2 | `foldSelectICmp` (line 4335) | sink the compare into a select | 7478 |
| CC3 | `foldICmpWithMinMax` (line 5651) | §13b.3 | 7482 |
| CC4 | `(X + C) pred X → X pred' Bound` | `foldICmpAddOpConst` (line 940): converts a self-referential add comparison into an overflow test, e.g. `(X + C) <u X → X >u (UINT_MAX - C)` | 7488 |
| CC5 | `abs(X) pred X` → a constant or a sign test | complete case analysis over all eight predicates, branching on whether the `abs` is `is_int_min_poison` | 7494 |
| CC6 | `foldICmpWithLowBitMaskedVal` (line 4505) | `icmp Pred X, (Mask)` where `Mask` is a low-bit mask or zero (`isMaskOrZero`, line 4398) — canonicalises the whole family of `X & Mask` tests | 7531 |
| CC7 | `(X /u C) pred X → X pred' 0` | `C >u 1` | 7537 |
| CC8 | `(X /s C) pred X → X pred' 0` | `C >u 1`; not an unsigned predicate | 7541 |
| CC9 | `(X >>u C) pred X → X pred' 0` | `C != 0` | 7549 |
| CC10 | `(X >>s C) <s X → X <s 0` | `C != 0`; `slt`/`sge` only | 7554 |

## 13b.3 `foldICmpWithMinMax` (line 5651)

```
icmp Pred (min/max X, Y), Z
```

Signedness must agree between the predicate and the intrinsic — or, for an
unsigned predicate on a signed min/max, both `Z` and the min/max must be
provably non-negative (then the predicate's signedness is flipped).

The algorithm asks InstSimplify whether `X pred Z` and `Y pred Z` are
*statically known*. Given one known answer:

* **Relational predicate.** Let `IsSame = (minmax's predicate == strict(Pred))`.
  If `X pred Z` is true: `IsSame` → the whole compare is `true`, else it
  reduces to `Y pred Z`. If false: `IsSame` → `Y pred Z`, else `false`.
* **Equality.** More involved: if `(Pred == eq) == CmpXZ` then the result is
  `X ≤/≥ Y` with the min/max's non-strict predicate (inverted for `ne`);
  otherwise it consults `minmaxPred(X, Z)` to decide between a constant and
  `Y pred Z`.

`samesign` is dropped (`Pred.dropSameSign()`) before the analysis.

## 13b.4 `foldICmpEquality` (line 5972)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| EQ1 | `(A ^ B) == A → B == 0` | | 5979 |
| EQ2 | `(A ^ C1) == (C ^ C2) → A == (C ^ (C1^C2))` | `1u` on the RHS xor | 5986 |
| EQ3 | `(A ^ B) == (A ^ D) → B == D` | any shared operand | 5992 |
| EQ4 | `(X & Z) == (Y & Z) → ((X ^ Y) & Z) == 0` | shared operand `Z`; fires if `X ^ Y` is a negated power of two, **or** at least 2 "uses removed" (counting `1u` on each `and` and both other operands being constants) | 6005 |
| EQ5 | `(X \| C) == (Y \| C) → ((X ^ Y) & ~C) == 0` | `1u` on both | 6039 |
| EQ6 | `(B & lowmask) == (zext A) → (trunc B) == A` | the mask width exactly matches `A`'s type; `1u` on one | 6049 |
| EQ7 | `(A >> C) ==/!= (B >> C) → (A ^ B) <u/>=u (1 << C)` | same shift kind and amount; `1u` on both; `0 < C < N` | 6057 |
| EQ8 | `(A << C) ==/!= (B << C) → ((A ^ B) & lowmask(N-C)) ==/!= 0` | `1u` on both | 6075 |
| EQ9 | `(trunc (A >>u C)) ==/!= K → (A & mask) ==/!= K'` | `1u` on the trunc and the shift; **`A` must have more than one use** (else other folds are better) | 6090 |
| EQ10 | `foldICmpIntrinsicWithIntrinsic` | equality of two matching intrinsics | 6106 |
| EQ11 | `(trunc A a>> (N-1)) ==/!= (trunc (A >>u N)) → (A + 2^(N-1)) <u/>=u 2^N` | `A` is exactly twice as wide; `1u` on one — *a signed-range check on the low half* | 6110 |
| EQ12 | `(X & P) ==/!= P → (X & P) !=/== 0` | `isKnownToBeAPowerOfTwo(P, OrZero=false)` | 6124 |
| EQ13 | `A ==/!= fshr(A, A, B) → A ==/!= fshl(A, A, B)` | `1u` — **[canon]** | 6134 |
| EQ14 | `(A ^ C) ==/!= B → (A ^ B) ==/!= C` | `1u` on the xor; `C` an `m_ImmConstant`, `B` not | 6141 |
| EQ15 | `(A & (B op A)) ==/!= A/0 → (B & A) ==/!= A/0` | `op` ∈ {`add`, `xor`, `sub`}; `1u`; `isKnownToBeAPowerOfTwo(A, OrZero=true)` | 6147 |
| EQ16 | `foldICmpEqualityWithOffset` (line 5912) | uses `collectOffsetOp` (line 5851) to cancel matching offset chains on both sides | 6168 |

## 13b.5 GEP comparisons — `foldGEPICmp` (line 676)

**Signed predicates are refused outright.** For unsigned predicates the GEP
must carry a no-wrap flag (`CanFold`); equality needs nothing.

Main cases:
* Two GEPs with the **same base and identical indices** → compare the base
  pointers.
* Two `inbounds` GEPs off the same base, each with all-constant indices or
  `1u` → emit both offsets and compare them with the **signed** version of the
  predicate.
* Two GEPs of the same shape differing in **exactly one** index → compare just
  that index (same bit width required).
* Otherwise `transformToIndexedCompare` (line 632) / `rewriteGEPAsOffset`
  (line 538), which rewrites a whole GEP chain as integer offset arithmetic
  when `canRewriteGEPAsOffset` (line 424) allows.

`foldAllocaCmp` (line 862) separately folds comparisons of an `alloca`'s
address against anything it cannot alias.

`foldCmpLoadFromIndexedGlobal` (line 109) turns
`icmp (load (gep @constant_array, i)), C` into a bit-test on `i` against a
magic constant computed by evaluating the predicate at every array index —
a complete decision procedure for arrays up to the bit width.

## 13b.6 Casts

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CT1 | `icmp (ptrtoint P), (ptrtoint Q) → icmp P, Q` | pointer and integer widths must match | 6407 |
| CT2 | `icmp (inttoptr X), (inttoptr Y) → icmp X, Y` | ditto | 6422 |
| CT3 | `foldICmpWithTrunc` (line 6225) | `1u` on the trunc; RHS constant. Uses `decomposeBitTestICmp` to turn the compare into an `and`+compare in the wide type; also re-dispatches `cttz`/`ctlz` intrinsics whose result provably fits in the narrow type | 6439 |
| CT4 | `icmp (ext X), (ext Y) → icmp X, Y` | **both extends must be the same kind**, unless one is a `zext nneg` (then it counts as a `sext`), or both sources are `i1` and the predicate is an equality (then `(X \| Y) ==/!= 0`). Different source widths need `1u` on both and an extra cast. A signed compare keeps its predicate only if the extension was signed; otherwise the predicate becomes **unsigned** | 6279 |
| CT5 | `icmp (ext X), C → icmp X, C'` | `C` must round-trip through the source type (`getLosslessTrunc`). Same signedness rule as CT4 | 6348 |
| CT6 | `(sext X) <u C → X >s -1` | unsigned predicate on a *signed* extension where the constant does not round-trip: only the sign matters | 6371 |
| CT7 | `foldICmpBitCast` (line 3407) | bitcast operands: compare the sources when both are bitcasts of the same type; recognise FP sign tests through `bitcast` | 7717 |
| CT8 | `simplifyIntToPtrRoundTripCast` | strips `inttoptr(ptrtoint P)` | 6383 |

## 13b.7 Overflow-intrinsic recognition

`OptimizeOverflowCheck` (line 6487) and `computeOverflow` (line 6463) turn an
open-coded overflow check into the matching `*_with_overflow` intrinsic. Used
from `visitICmpInst` (line 7758) via `m_UAddWithOverflow`.

| Helper | What it recognises |
|---|---|
| `processUGT_ADDCST_ADD` (line 1093) | `(A + B + C2) >u C1` where the constants describe a narrow signed-add overflow test → `sadd.with.overflow` in the narrow type. Requires `C2` a power of two with `log2 ∈ {7,15,31}`, `C1` the matching low-bit mask, and every other user of the add to be a narrow `trunc` |
| `processUMulZExtIdiom` (line 6550) | `(zext X *nuw zext Y) pred C` → `umul.with.overflow` |
| `foldICmpOfUAddOv` (line 7376) | `extractvalue(uadd.with.overflow(A,B),0) <u A → extractvalue(…,1)` and three related shapes |
| `foldMultiplicationOverflowCheck` (line 4882) | `(X * Y) /u Y != X` style checks |
| `isNeutralValue` (line 6448) | whether the RHS is the binop's identity, used to skip trivial checks |

## 13b.8 Tail folds in `visitICmpInst`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| TL1 | `(X & ~Y) ==/!= 0 → (X & Y) !=/== 0` | `isKnownToBeAPowerOfTwo(X, OrZero=false)`; equality | 7735 |
| TL2 | `icmp (X >> (N-1)), (zext/sext i1 Y) → icmp (X <s 0), Y` | unsigned or equality predicate; the shift kind must match the extension kind (`lshr`+`zext` or `ashr`+`sext`); `1u` on one | 7783 |
| TL3 | `extractvalue(cmpxchg, 0) == Cmp → extractvalue(cmpxchg, 1)` | the `cmpxchg` must not be `weak` | 7815 |
| TL4 | `foldICmpPow2Test` (line 5797) | recognises `(X & (X-1)) == 0` and friends as power-of-two tests, emitting `ctpop` comparisons | 7805 |
| TL5 | `foldICmpWithHighBitMask` (line 7263): `(1 << Y) <=u X → (X >>u Y) != 0` | `1u` on the shift; also the `~(-1 << Y)` / `(1 << Y) - 1` spellings | 7821 |
| TL6 | `foldVectorCmp` (line 7306): push the compare through `vector.reverse` and through matching shuffles | `1u` on one operand; masks must match | 7825 |
| TL7 | `foldICmpInvariantGroup` (line 7404): strip `launder`/`strip.invariant.group` when comparing against null | null must not be a valid pointer in that address space | 7829 |
| TL8 | `foldReductionIdiom` (line 7425): `icmp (vector_reduce_op V), C` | | 7832 |
| TL9 | `((sext A) & C1) ==/!= C2 → (A & trunc C1') ==/!= trunc C2` | equality; `C2`'s active bits fit the narrow type; the truncated mask gets its sign bit set if `C1` reaches above the narrow width | 7840 |
| TL10 | `(A - B) pred (A + B) → B pred' 0` | matching no-wrap flags: unsigned needs both `nuw`, signed both `nsw`, equality needs one of each on each | 7688 |
| TL11 | `icmp (select C, A, B), (select C, D, E)` → sink into the select | `1u` on one; one side must simplify | 7670 |

