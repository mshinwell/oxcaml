# `InstCombineCasts.cpp` — Part 12: casts

Back to [index](README.md).

The organising idea of this file is **expression-tree retyping**: rather than
matching individual patterns, the pass asks "can I recompute this whole
expression in the destination type?" and, if so, rebuilds it, deleting the
cast. Three predicates implement this — `canEvaluateTruncated`,
`canEvaluateZExtd`, `canEvaluateSExtd` — and `EvaluateInDifferentType`
(line 30) performs the rebuild.

---

## 12.1 `commonCastTransforms` (line 156) — every cast opcode

| # | Rule | Side conditions | Line |
|---|---|---|---|
| CC1 | constant-fold the cast | | 160 |
| CC2 | `cast2(cast1(X)) → cast3(X)` | `isEliminableCastPair` (line 128), which delegates to `CastInst::isEliminableCastPair` and then **rejects** results that would create an `inttoptr`/`ptrtoint` to an integer type of the wrong width for the pointer | 165 |
| CC3 | `cast(select C, A, B) → select C, cast(A), cast(B)` | the select's condition must **not** be a compare whose operand type equals the select type (creating a select whose operands differ in size from its condition inhibits later folds) — unless this is a `trunc` that `shouldChangeType` likes. For a `bitcast`, the element count must be preserved | 175 |
| CC4 | `cast(phi ...) → phi(cast ...)` | only if both types are non-integer, or `shouldChangeType` (avoid creating an illegal-typed PHI from a legal one) | 196 |
| CC5 | `cast (shuffle X, undef, M) → shuffle (cast X), M` | `1u` on the shuffle; fixed vectors; **same element count and same total bit width** on both sides — **[canon]** | 208 |

## 12.2 `canEvaluateTruncated` (line 269)

`canAlwaysEvaluateInType` (line 233) accepts `m_ImmConstant`, and any
`zext`/`sext`/`trunc` whose source is already the target type.

| Node | Truncatable when |
|---|---|
| `add`, `sub`, `mul`, `and`, `or`, `xor` | both operands are |
| `udiv`, `urem` | **the truncated-off high bits of both operands are known zero.** Note the context instruction is *not* preserved into the recursion — simplifying div/rem using later context could introduce a trap |
| `shl` | `maxShiftAmount <u NarrowWidth` |
| `lshr` | `maxShiftAmount <u NarrowWidth`, **and** either (the sole user is a `trunc` and `maxShiftAmt + demandedBits <= NarrowWidth`) or the bits shifted in are known zero |
| `ashr` | `maxShiftAmount <u NarrowWidth` and `OrigWidth - NarrowWidth < numSignBits(operand)` |
| `trunc` | always |
| `zext`, `sext` | always |
| `select` | both arms are |
| `phi` | all incoming are |
| `fptoui`, `fptosi` | the narrow integer type is wide enough to hold the FP type's max value (`semanticsIntSizeInBits`) — **otherwise the narrowed cast would be poison where the original was not** |
| `shufflevector` | both operands are |

Everything else (`canNotEvaluateInType`, line 247) is rejected — in particular
any value with **more than one use**, and any non-instruction.

## 12.3 `visitTrunc` (line 753)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| T1 | retype the whole expression to the narrow type | `canEvaluateTruncated`; vector, or `shouldChangeType`. *Always a win — the cast disappears* | 765 |
| T2 | retype to `DestWidth * 2` instead | when T1 fails, `DestWidth*2 < SrcWidth`, and `canEvaluateTruncated` to the double-width type. Keeps a `trunc` but narrows the tree, which may enable vectorisation | 781 |
| T3 | `SimplifyDemandedInstructionBits` | Part 20 | 797 |

### Truncation to `i1`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| T4 | `trunc ((C1 << X) >> C2) to i1 → X == (C2 - log2 C1)` | `C1` a power of two; `1u` | 806 |
| T5 | `trunc (X >> (N-1)) to i1 → X <s 0` | either shift kind | 813 |
| T6 | `trunc (X >>u C) to i1 → (X & (1<<C)) != 0` | `1u` | 820 |
| T7 | `trunc ((X >>u C) \| X) to i1 → (X & ((1<<C)\|1)) != 0` | `1u` | 827 |
| T8 | `trunc (C << X) to i1 → X == 0` | `C` **odd** | 836 |
| T9 | `trunc (X ^ Y) to i1 → X != Y` | the **`trunc` must be `nuw` or `nsw`** — the flag says the discarded high bits were all zero/sign, so the low bit determines the whole value | 841 |

### General

| # | Rule | Side conditions | Line |
|---|---|---|---|
| T10 | `trunc (lshr (sext A), C) → ashr A, C` | `C <= SrcWidth - max(DestWidth, AWidth)`; the new shift amount is clamped to `Width-1`; `exact` preserved. If types mismatch, needs `1u` and emits a cast | 848 |
| T11 | `narrowBinOp` | §12.4 | 878 |
| T12 | `shrinkSplatShuffle` (line 706): `trunc (shuf X, undef, splat) → shuf (trunc X), poison, splat` | `1u`; all-equal mask; same type | 881 |
| T13 | `shrinkInsertElt` (line 726): `trunc (inselt undef, X, I) → inselt undef, (trunc X), I` | `1u`; the vector operand must be `undef` | 884 |
| T14 | `trunc (X << C) → (trunc X) << C` | `1u` on the source; vector or `shouldChangeType`; `C <u DestWidth`; **and `X` must not itself be a shift-right by a constant** (that would undo `FoldShiftByConstant` and is the extend-in-register pattern) | 890 |
| T15 | `foldVecTruncToExtElt` (line 411): `trunc (lshr (bitcast <N x T> V), C) → extractelement V, I` | `1u`; endianness-aware index | 903 |
| T16 | `foldVecExtTruncToExtElt` (line 461) | the ext/trunc variant | 906 |
| T17 | `trunc (ctlz (zext A), B) → ctlz(A, B) + (SrcWidth - AWidth)` | `1u`; `AWidth == DestWidth`; `AWidth > log2(SrcWidth)` | 910 |
| T18 | `trunc (vscale) → vscale` | the function has a `vscale_range` attribute with `log2(max) < DestWidth` | 921 |
| T19 | `trunc X to i1 → true` | the `trunc` is `nuw` or `nsw` and `isKnownNonZero(X)` | 933 |
| T20 | infer `nsw` | `ComputeMaxSignificantBits(Src) <= DestWidth` | 939 |
| T21 | infer `nuw` | the high bits of `Src` are known zero | 945 |

## 12.4 `narrowBinOp` (line 620)

Requires `1u` on the binop, and vector or `shouldChangeType`.

| # | Rule | Applies to | Line |
|---|---|---|---|
| NB1 | `trunc (binop C, X) → binop (trunc C), (trunc X)` | `and or xor add sub mul` | 637 |
| NB2 | `trunc (binop (ext X), Y) → binop X, (trunc Y)` | same set; `X`'s type must equal the destination | 650 |
| NB3 | `trunc (shr (trunc A), C) → trunc (shr A, C)` | `lshr`/`ashr`; `C <= SrcWidth - DestWidth`, so all the bits the shift creates are truncated away; `exact` preserved; undef lanes merged | 668 |
| NB4 | `narrowFunnelShift` | §12.5 | 695 |

## 12.5 `narrowFunnelShift` (line 516)

```
trunc (or (shl ShVal0, ShAmt0), (lshr ShVal1, ShAmt1))
     →  fshl/fshr(trunc ShVal0, trunc ShVal1, ShAmt)
```

* `NarrowWidth` must be a power of two; `1u` on the `or` and both shifts;
  the two shifts must be in opposite directions.
* The shift amounts must match one of:
  - `R == NarrowWidth - L` — allowed for a **funnel** shift only if
    `ShVal0 == ShVal1` (a rotate) **or** the high bits of `L` above
    `log2(NarrowWidth)` are known zero, because a narrowed funnel shift must
    not over-shift into poison;
  - `L == X & (W-1)`, `R == (-X) & (W-1)` — **rotates only**;
  - the same with a `zext` around each masked amount.
* **`ShVal1` (the right-shifted value) must have zero high bits in the wide
  type.** The left-shifted value's high bits are discarded by the truncation,
  so they are unconstrained.

## 12.6 `visitZExt` (line 1192)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| Z0 | bail out entirely | the `zext`'s sole user is a `trunc` and the operand isn't constant — let the `trunc` fold first | 1195 |
| Z1 | `zext nneg (i1 X) → 0` | `nneg` on an `i1` zext means the value is non-negative *as a signed i1*, i.e. it is 0 | 1206 |
| Z2 | retype the expression to the wide type | `canEvaluateZExtd` (line 1079) with `shouldChangeType`. The predicate also returns `BitsToClear`, the count of extra high bits of the *narrow* result that need masking; the rebuild emits an `and` unless those bits are already known zero | 1214 |
| Z3 | `zext (trunc A) → (zext?) (A & lowmask)` | three sub-cases by relative width: `zext(A & mask)`, `A & mask`, or `(trunc A) & mask` | 1250 |
| Z4 | `transformZExtICmp` | §12.7 | 1281 |
| Z5 | `zext ((trunc X) & C) → X & (zext C)` | `1u`; `X`'s type must be the destination | 1287 |
| Z6 | `zext (((trunc X) & C) ^ C) → (X & zext C) ^ zext C` | `1u` on both | 1294 |
| Z7 | `zext ((trunc X) & C) → X & (zext C)` | the multi-use variant of Z5 (no `1u`) | 1306 |
| Z8 | `zext (vscale) → vscale` | `vscale_range` max fits | 1313 |
| Z9 | infer `nneg` | the sole user is a shift and the source type is wide enough to hold any in-range shift amount; **or** `isKnownNonNegative(Src)` | 1327 |

## 12.7 `transformZExtICmp` (line 971)

> Source FIXME: these transforms do not check for extra uses and may create an
> extra instruction; the comment suggests the inverse direction (preferring
> `icmp`) may actually be better. Worth taking as advisory, not gospel.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| ZC1 | `zext (X <s 0) → X >>u (N-1)` | — | 984 |
| ZC2 | `zext (X == 0) → X ^ 1` | `X` has exactly one possible set bit, at position 0 | 996 |
| ZC3 | `zext (X == 0) → (X >>u k) ^ 1` | the single possible bit is at position `k`, and `k+1 != DestWidth` (the high-bit case is canonicalised elsewhere); for `eq` also requires matching types or `k == 0` | 996 |
| ZC4 | `zext (X != 0) → X` / `X >>u k` | same analysis without the `xor` | 996 |
| ZC5 | `zext ((X & (1 << S)) == 0) → ((~X) >>u S) & 1` | `1u` on the compare and the `and`; matching types, or the predicate is `ne`, or the shift has `1u` | 1035 |
| ZC6 | `zext ((X & (1 << S)) != 0) → (X >>u S) & 1` | same | 1035 |

## 12.8 `visitSExt` (line 1479)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S0 | bail out | sole user is a `trunc` | 1482 |
| S1 | `sext X → zext nneg X` | `isKnownNonNegative(X)` — **[canon]** | 1493 |
| S2 | retype the expression to the wide type | `canEvaluateSExtd` (line 1431) + `shouldChangeType`. If the rebuilt value doesn't already have enough sign bits, emits `shl`+`ashr` | 1500 |
| S3 | `sext (trunc X) → X` (or a cast) | `numSignBits(X) > XBitSize - SrcBitSize` | 1521 |
| S4 | `sext (trunc X) → (X << C) >>s C` | `1u`; `X`'s type is the destination | 1526 |
| S5 | `sext (trunc (lshr Y, C)) → sext/trunc (ashr Y, C)` | `1u`; `C == XBitSize - SrcBitSize` exactly | 1537 |
| S6 | `transformSExtICmp` | §12.9 | 1546 |
| S7 | `sext (ashr (shl (trunc A), C), C) → (A << C') >>s C'` | both shift constants equal; `A`'s type is the destination; `C' = DestWidth - (SrcWidth - C)`. Undef lanes merged | 1562 |
| S8 | `sext (ashr (trunc X), M-1) → (X << (N-M)) >>s (N-1)` | `1u`; splats the sign bit of the narrow value | 1585 |
| S9 | `sext (vscale) → vscale` | `log2(maxVScale) < SrcBitSize - 1` | 1601 |

### `canEvaluateSExtd` (line 1431)

`sext`/`zext`/`trunc` always; `and or xor add sub mul` if both operands are;
`select` if both arms are; `phi` if all incoming are. Notably **shifts are
not handled** (TODO in the source).

## 12.9 `transformSExtICmp` (line 1346)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| SC1 | `sext (X <s 0) → X >>s (N-1)` | — | 1353 |
| SC2 | `sext ((X & 2^n) == 0) → (X >>u n) - 1` | `1u` on the compare; the compare is against `0` or a power of two; `X` has exactly one possible set bit | 1385 |
| SC3 | `sext ((X & 2^n) != 2^n) → (X >>u n) - 1` | same | 1385 |
| SC4 | `sext ((X & 2^n) != 0) → (X << (N-1-n)) >>s (N-1)` | same | 1395 |
| SC5 | `sext ((X & 2^n) == 2^n) → (X << (N-1-n)) >>s (N-1)` | same | 1395 |
| SC6 | constant-fold to all-ones / zero | the compared constant is a *different* power of two from the only possible set bit — the test is statically decidable | 1375 |

## 12.10 FP casts

### `visitFPTrunc` (line 1758)

The interesting group is *double-rounding avoidance*. `getMinimumFPType`
(line 1683) looks through `fpext` and shrinks FP constants to the narrowest
type that represents them exactly.

| # | Rule | Precision condition | Line |
|---|---|---|---|
| FT1 | `fptrunc (fadd X, Y) → fadd (fptrunc X), (fptrunc Y)` | `OpWidth >= 2*DstWidth + 1` **and** `DstWidth >= SrcWidth`. *Cited to Figueroa's 2000 thesis, p50: this bound makes double rounding provably innocuous.* Same for `fsub` | 1791 |
| FT2 | `fptrunc (fmul X, Y) → fmul (fptrunc X), (fptrunc Y)` | `OpWidth >= LHSWidth + RHSWidth` and `DstWidth >= SrcWidth` — the infinitely-precise product has at most `LHSWidth+RHSWidth` significant bits | 1808 |
| FT3 | `fptrunc (fdiv X, Y) → fdiv (fptrunc X), (fptrunc Y)` | `OpWidth >= 2*DstWidth` and `DstWidth >= SrcWidth` (conservative; the source notes the unbalanced case could be tightened) | 1820 |
| FT4 | `fptrunc (frem X, Y) → fpcast (frem (trunc X), (trunc Y))` | evaluated in the larger of the two *minimum* source types; `SrcWidth != OpWidth`. **Remainder is always exact, so no precision condition is needed** | 1831 |

All four require `1u` on the binop. FMF are copied from the binop.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FT5 | `fptrunc (fneg X) → fneg (fptrunc X)` | `1u`; FMF **intersected** between the `fptrunc` and the operand | 1861 |
| FT6 | `fptrunc (select C, (fpext X), Y) → select C, X, (fptrunc Y)` | `1u`; `X`'s type must equal the destination. Mirror case too | 1872 |
| FT7 | `fptrunc (unary-FP-op X) → unary-FP-op (fptrunc X)` | for `ceil fabs floor nearbyint rint round roundeven trunc`; `1u` on the argument. **Except for `fabs`, the argument must itself be an `fpext` from the destination type.** FMF are taken from the `fptrunc`, **not** the intrinsic — "a normal value may be converted to an infinity, so we cannot propagate `ninf`" | 1893 |
| FT8 | `shrinkInsertElt` | as T13 | 1932 |
| FT9 | `fptrunc (sitofp/uitofp X) → sitofp/uitofp X` | `isKnownExactCastIntToFP` | 1937 |

### `visitFPExt` (line 1947)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FE1 | `fpext (sitofp/uitofp X) → sitofp/uitofp X` | `isKnownExactCastIntToFP` | 1952 |

### `isKnownExactCastIntToFP` (line 1711)

An int→FP cast is exact when any of:
* the source integer width (minus 1 for signed) `<=` the FP mantissa width;
* the source is itself an `fptosi`/`fptoui` whose FP type has no more
  significant bits than the destination FP type (**+1 if this is
  `uitofp (fptosi F)`, to allow for rounding of negative inputs**); neither
  type may be `ppc_fp128`;
* known bits show the source has few enough significant bits
  (`width - leadingZeros - trailingZeros <= mantissaWidth`).

### `foldItoFPtoI` (line 1965) and `foldFPtoI` (line 2005)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FI1 | `fptosi (sitofp X) → sext/trunc X` | `isKnownExactCastIntToFP`, **or** the destination integer is narrow enough that overflow UB covers the inexactness (`OutputSize <= mantissaWidth`) | 1965 |
| FI2 | `fptoui (uitofp X) → zext/trunc X` | same; an unsigned output from a signed input is also safe, because a negative input would be UB | 1990 |
| FI3 | `fptoui X → 0` | `computeKnownFPClass` proves `X` is never a positive normal | 2005 |
| FI4 | `fptosi X → 0` | proves `X` is never normal | 2005 |
| FI5 | infer `nneg` on `uitofp` | `isKnownNonNegative` | 2040 |
| FI6 | `sitofp X → uitofp nneg X` | `isKnownNonNegative` — **[canon]** | 2050 |

## 12.11 Pointer casts

| # | Rule | Side conditions | Line |
|---|---|---|---|
| P1 | `inttoptr X → inttoptr (zext/trunc X to intptr)` | the source width differs from the target pointer width — **[canon]**, exposes the cast to other folds | 2062 |
| P2 | `ptrtoint P → zext/trunc (ptrtoint P to intptr)` | destination width differs from pointer width — **[canon]** | 2124 |
| P3 | `ptrtoint (ptrmask P, M) → (ptrtoint P) & M` | `1u`; `M`'s type must equal the result type. *`and` is better supported than `ptrmask`* | 2134 |
| P4 | `foldPtrToIntOfGEP` (line 2078): `ptrtoint (gep ... (inttoptr X)) → X + offsets` | the GEP chain must be all `1u`; the base must be a `1u` `inttoptr` of the right type, or `null`. Each `add` gets `nuw` iff the GEP had it | 2141 |
| P5 | `ptrtoint (insertelement (inttoptr V), S, I) → insertelement V, (ptrtoint S), I` | `1u`; `V`'s type must equal the result | 2146 |
| P6 | `addrspacecast` | only `commonCastTransforms` | 2904 |

## 12.12 `visitBitCast` (line 2757)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| B1 | `bitcast X to (same type) → X` | | 2766 |
| B2 | `bitcast (trunc/zext (bitcast <vec>)) → shufflevector` | `optimizeVectorResizeWithIntegerBitCasts` (line 2159). **Endianness-dependent**: the trunc/zext affects the high bits of the integer, which is the *front* of the vector on big-endian and the *back* on little-endian | 2772 |
| B3 | `bitcast (or of shifted zexts) → insertelement chain` | `optimizeIntegerToVectorInsertions` (line 2376) / `collectInsertionElements` (line 2262) | 2786 |
| B4 | `bitcast <1 x T> → scalar` | via `extractelement` | 2794 |
| B5 | `bitcast (inselt <1 x T> V, X, 0) → bitcast X` | | 2806 |
| B6 | `bitcast (inselt (bitcast X), Y, 0) → (X & highmask) \| zext Y` | `1u` on both; destination is an integer of a "desirable" width; index 0 **after endian normalisation** (any other index would need a shift) | 2813 |
| B7 | `bitcast (shuffle A, B, M) → shuffle (bitcast A), (bitcast B), M` | `1u`; same element count throughout; at least one shuffle operand is already a bitcast *from* the destination type | 2838 |
| B8 | `bitcast (shuffle X, undef, reverse) → bswap/bitreverse (bitcast X)` | `1u`; the mask is a full reverse; even element count. `bswap` when the element type is `i8` and the destination integer width is legal; `bitreverse` when the element type is `i1` | 2860 |
| B9 | `optimizeBitCastFromPhi` (line 2568) | the A→B→A cast through a PHI; guarded by `hasStoreUsersOnly` heuristics | 2880 |
| B10 | `canonicalizeBitCastExtElt` (line 2410): `bitcast (extractelement V, I) → extractelement (bitcast V), I` | `1u`; the destination must be a valid vector element type | 2884 |
| B11 | `foldBitCastBitwiseLogic` (line 2437) | §below | 2887 |
| B12 | `foldBitCastSelect` (line 2509): `bitcast (select C, bitcast(X), Y) → select C, X, bitcast(Y)` | `1u` on the select and the inner bitcast; `X` must have the destination type and not be a constant; the select's element count must be preserved; scalar↔vector changes are refused | 2890 |
| B13 | `foldCopySignIdioms` (line 2738): `bitcast ((bitcast X & signmask) \| Y) → copysign(bitcast Y, X)` | element-wise bitcast; `X` has the FP result type; **`isKnownNonNegative(Y)`** | 2893 |

### `foldBitCastBitwiseLogic` (line 2437)

`1u` on the logic op, which must be `and`/`or`/`xor`. **Restricted to vector
types** (the source notes this is to avoid creating illegal scalar ops).

* FP destination: `bitcast(logic(bitcast X, bitcast Y))` where one of `X`,`Y`
  is FP and the other integer → do the logic in the integer type.
* Integer destination: `bitcast(logic(bitcast X, Y)) → logic(X, bitcast Y)`
  when `X` already has the destination type and is not a constant.
* `bitcast (logic X, C) → logic (bitcast X), (bitcast C)` — **[canon]**, so
  that e.g. `icmp u (a ^ signmask), (b ^ signmask)` can later become
  `icmp s a, b`.

