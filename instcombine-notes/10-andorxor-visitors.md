# `InstCombineAndOrXor.cpp` — Part 11b: `visitAnd`, `visitOr`, `visitXor`

Back to [index](README.md). Helpers: [11a](09-andorxor-shared.md).
Comparison folds: [11c](11-andorxor-cmps.md).

---

# 11b.1 `visitAnd` (line 2386)

Preamble: `simplifyAndInst`; `SimplifyAssociativeOrCommutative`;
`foldVectorBinop`; `foldBinopWithPhiOperands`;
`SimplifyDemandedInstructionBits`; `foldAndToXor`; `foldComplexAndOrPatterns`;
`foldUsingDistributiveLaws` (`(A|B)&(A|C) → A|(B&C)`);
`foldBinOpShiftWithShift`.

## Single-bit / power-of-two patterns

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A1 | `(1 >> X) & 1 → zext(X == 0)` | `1u` on the shift (either direction) | 2423 |
| A2 | `(C << X) & 1 → zext(X == 0)` | `1u`; `C` **odd** | 2423 |
| A3 | `(-(X & 1)) & Y → (X & 1) == 0 ? 0 : Y` **[comm]** | `1u` on the neg | 2434 |
| A4 | `(X ± Y) & Y → ~X & Y` **[comm]** | `1u` on the add/sub; `isKnownToBeAPowerOfTwo(Y, OrZero=true)` — **[canon]** | 2446 |

## With a constant mask `C` (`Op1` is `m_APInt`)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A5 | `(X ^ C1) & C → (X & C) ^ (C1 & C)` | `1u` on the xor | 2453 |
| A6 | `(X \| C1) & C → (X & (C ^ (C1&C))) \| (C1&C)` | `1u` on the or. Reduces set bits in the mask, which helps store narrowing | 2461 |
| A7 | `(sext (X a>> S)) & C → (sext X) >>u S` | `1u`; `S < Width`; `C` must be exactly `lowbits(Width - S)` | 2476 |
| A8 | `(X a>> S) & C → X >>u S` | `S < Width`; `C` is a mask of `Width - S` bits | 2487 |
| A9 | `(X + AddC) & C → (X & C) ^ C` | `1u`; `C` a power of two; `AddC` has no bits below `C`'s bit. *The add flips exactly one bit* | 2497 |
| A10 | `(bo (zext X), C1) & C → zext((bo X, C1') & C')` | `bo` ∈ {`xor`,`or`,`mul`,`add`,`sub`}; `1u` on the binop and the zext; `C` fits in the narrow width | 2523 |
| A11 | `(bo (zext X), Y) & C → zext(bo X, trunc Y)` | as A10; `C` is exactly a mask of the narrow width (so the `and` disappears) | 2539 |
| A12 | `(bo Y, (zext X)) & C → zext(bo (trunc Y), X)` | mirror | 2550 |
| A13 | `((X {x}or Y) & C) → X {x}or (Y & C)` | `1u` on the or/xor; the bits `~C` are known zero in `X` (so `X` needs no masking) | 2568 |
| A14 | mirror of A13 with the roles of `X`/`Y` swapped | plus `Y` not a constant | 2575 |
| A15 | `(ShiftC << X) & C → X == (log2 C - log2 ShiftC) ? C : 0` | `C` and `ShiftC` powers of two; `1u` on the shift | 2586 |
| A16 | `(ShiftC >> X) & C → X == (log2 ShiftC - log2 C) ? C : 0` | same | 2586 |
| A17 | `((C1 << X) >>u C2) & C3 → X == (cttz C3 + C2 - cttz C1) ? C3 : 0` | `C1`, `C3` powers of two; `C2 + cttz(C3) < Width`; `1u` | 2607 |
| A18 | `((C1 >>u X) << C2) & C3 → X == (cttz C1 + C2 - cttz C3) ? C3 : 0` | `C1`, `C3` powers of two; `log2(C3) >= C2`; `1u` | 2624 |
| A19 | `(X & C1) \| C2 → X & (C1\|C2)` — *listed under `or`, see O33* | | |

## FP sign-bit tricks

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A20 | `bitcast(F) & 0x7FFF... → bitcast(fabs F)` | element-wise bitcast; the element type is FP with the **sign bit in the MSB** (`APFloat::hasSignBitInMSB`); the function must **not** have `noimplicitfloat` | 2647 |

## Extends and bools

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A21 | `((zext X) << Y) & signmask → (sext X) & signmask` | `1u` on the shl; `Y` must be exactly `N - SrcWidth` | 2664 |
| A22 | `narrowMaskedBinOp` | 11a.4 | 2678 |
| A23 | `foldAndOrOfSelectUsingImpliedCond` | only for `i1` type; see Part 14 | 2681 |
| A24 | `foldBinOpIntoSelectOrPhi` | Part 21 | 2694 |
| A25 | `matchDeMorgansLaws` | DM1/DM3 | 2697 |

## Xor/or/and identities

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A26 | `A & ~(A ^ B) → A & B` **[comm]** | — | 2703 |
| A27 | `(A ^ B) & ((B ^ C) ^ A) → (A ^ B) & ~C` | `~C` must be free (`1u` on the operand, or `getFreelyInverted` succeeds) | 2710 |
| A28 | `((A ^ C) ^ B) & (B ^ A) → (B ^ A) & ~C` | same | 2721 |
| A29 | `(A \| B) & (~A ^ B) → A & B` **[comm ×4]** | — | 2734 |
| A30 | `(~A ^ B) & (A \| B) → A & B` **[comm ×4]** | — | 2743 |
| A31 | `(~A \| B) & (A ^ B) → ~A & B` **[comm ×4]** | — | 2752 |
| A32 | `(A ^ B) & (~A \| B) → ~A & B` **[comm ×4]** | — | 2759 |

## Boolean / select conversions

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A33 | `foldBooleanAndOr` | 11c | 2764 |
| A34 | `reassociateBooleanAndOr` | `1u` on the inner logical-and | 2768 |
| A35 | `reassociateFCmps` | 11a.13 | 2783 |
| A36 | `foldCastedBitwiseLogic` | 11a.3 | 2786 |
| A37 | `foldBinopOfSextBoolToSelect` | Part 21 | 2789 |
| A38 | `(sext i1 A) & B → A ? B : 0` **[comm]** | `A` is `i1` | 2798 |
| A39 | `~(sext i1 A) & B → A ? 0 : B` **[comm]** | `A` is `i1` | 2804 |
| A40 | `(zext i1 A) & B → A ? (B & 1) : 0` **[comm]** | `1u` on the zext; `A` is `i1` | 2810 |
| A41 | `(A - 1) & B → A ? 0 : B` **[comm]** | `A` is `i1`, or (`zext` of something with) at most 1 active bit — then the condition becomes `A == 0` and the arms swap | 2816 |
| A42 | `(X a>> (N-1)) & Y → (X <s 0) ? Y : 0` **[comm]** | `1u`; optional surrounding `sext` | 2827 |
| A43 | `~(X a>> (N-1)) & Y → (X <s 0) ? 0 : Y` **[comm]** | same | 2836 |

## Tail

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A44 | `(~x) & y → ~(x \| ~y)` | `sinkNotIntoOtherHandOfLogicalOp`, only if inversions are removed | 2845 |
| A45 | an `and` recurrence with a loop-invariant step → `and start, step` | `matchSimpleRecurrence`; `Step` must **dominate** the PHI | 2849 |
| A46 | `reassociateForUses` | 11a.6 | 2854 |
| A47 | `canonicalizeLogicFirst` | 11a.7 | 2857 |
| A48 | `foldLogicOfIsFPClass` | 11c | 2860 |
| A49 | `foldBinOpOfDisplacedShifts` | 11a.8 | 2863 |
| A50 | `foldBitwiseLogicWithIntrinsics` | 11a.9 | 2866 |
| A51 | `X & Y → X[Y := -1] & Y` **[comm]** | `simplifyAndOrWithOpReplaced` | 2869 |

---

# 11b.2 `visitOr` (line 3747)

Preamble: `simplifyOrInst`; `SimplifyAssociativeOrCommutative`;
`foldVectorBinop`; `foldBinopWithPhiOperands`;
`SimplifyDemandedInstructionBits`; `foldOrToXor`; `foldComplexAndOrPatterns`;
`foldOrOfInversions`; `foldUsingDistributiveLaws`.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| O1 | `(A & B) \| (C & D) → A ^ D` | `foldOrOfInversions`: `A == ~C && B == ~D` (or `A == ~D && B == ~C`) | 3775 |
| O2 | `foldAndOrOfSelectUsingImpliedCond` | `i1` only | 3784 |
| O3 | `foldBinOpIntoSelectOrPhi` | | 3797 |
| O4 | `matchBSwapOrBitReverse` | recognises `bswap`/`bitreverse` built from shifts and masks — a multi-instruction matcher, line 2878 | 3800 |
| O5 | `matchFunnelShift` | recognises `fshl`/`fshr` from an `or` of two shifts; see `convertOrOfShiftsToFunnelShift` (line 2896) | 3805 |
| O6 | `matchOrConcat` (line 3087) | `(zext X << N/2) \| zext Y → bswap/concat` shapes | 3808 |
| O7 | `foldBinOpShiftWithShift` | Part 21 | 3811 |
| O8 | `tryFoldInstWithCtpopWithNot` | Part 21 | 3814 |

## When the `or` is `disjoint` (it *is* an `add`)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| O9 | `foldAddLikeCommutative(…, NSW=true, NUW=true)` | see [V29/V30](01-addsub-integer.md) | 3818 |
| O10 | `foldBitmaskMul` | `matchBitmaskMul` (line 3612) decomposes `(X & mask) * C` terms and recombines them | 3827 |
| O11 | `reassociateDisjointOr` (line 3700) | reassociates chains of disjoint ors | 3830 |
| O12 | `SimplifyAddWithRemainder` | at the very end; see [V14/V15](01-addsub-integer.md) | 4290 |

## General

| # | Rule | Side conditions | Line |
|---|---|---|---|
| O13 | `(X ^ C) \| Y → (X \| Y) ^ C` **[comm]** | `1u` on the xor; `C` not all-ones; `MaskedValueIsZero(Y, C)` | 3835 |
| O14 | `(X * Y) \|disjoint X → X * (Y + 1)` **[comm]** | `1u` on the mul; the `or` must be `disjoint` | 3845 |

### `(A & C0) | (B & C1)` with constant masks

| # | Rule | Side conditions | Line |
|---|---|---|---|
| O15 | `((X\|B) & C0) \| (B & ~C0) → (X & C0) \| B` | `C0 == ~C1` | 3860 |
| O16 | `(A & C0) \| ((X\|A) & ~C0) → (X & ~C0) \| A` | `C0 == ~C1` | 3863 |
| O17 | `((X^B) & C0) \| (B & ~C0) → (X & C0) ^ B` | `C0 == ~C1` | 3867 |
| O18 | `(A & C0) \| ((X^A) & ~C0) → (X & ~C0) ^ A` | `C0 == ~C1` | 3870 |
| O19 | `((X\|B) & C0) \| (B & C1) → (X\|B) & (C0\|C1)` | `C0 & C1 == 0`; `MaskedValueIsZero(X, ~C0)` | 3876 |
| O20 | `(A & C0) \| ((X\|A) & C1) → (X\|A) & (C0\|C1)` | `C0 & C1 == 0`; `MaskedValueIsZero(X, ~C1)` | 3883 |
| O21 | `((X\|C2) & C0) \| ((X\|C3) & C1) → (X\|C2\|C3) & (C0\|C1)` | `C0&C1 == 0`, `C2 & ~C0 == 0`, `C3 & ~C1 == 0` — *bitfield insertion* | 3892 |

### Select recovery

| # | Rule | Side conditions | Line |
|---|---|---|---|
| O22 | `(Cond & C) \| (~Cond & D) → Cond ? C : D` | `matchSelectFromAndOr` (line 3254), tried in all 8 operand pairings; `1u` on one operand. `getSelectCondition` (line 3170) also handles inverted *vector* bitmasks via `areInverseVectorBitmasks` | 3907 |
| O23 | `(Cond & C) \| ~(Cond \| D) → Cond ? C : ~D` | 4 pairings; `1u` on one operand | 3932 |

### Xor absorption

| # | Rule | Side conditions | Line |
|---|---|---|---|
| O24 | `(A ^ B) \| ((B ^ C) ^ A) → (A ^ B) \| C` **[comm]** | — | 3946 |
| O25 | `(A \| ?) \| (A ^ B) → (A \| ?) \| B` | operands canonicalised so the `xor` is on the RHS | 3971 |
| O26 | `(A & B) \| (A ^ B) → A \| B` | — | 3979 |
| O27 | `~A \| (A ^ B) → ~(A & B)` | `1u` on one operand | 3985 |
| O28 | `~(A & ?) \| (A ^ B) → ~((A & ?) & B)` | `1u` on one operand | 3993 |
| O29 | `(~A \| C) \| (A ^ B) → ~(A & B) \| C` | `1u` on **both** | 4005 |
| O30 | `((A&B) ^ A) \| ((A&B) ^ B) → A ^ B` **[comm ×4]** | — | 4098 |

### Booleans, casts, reassociation

| # | Rule | Side conditions | Line |
|---|---|---|---|
| O31 | `foldBooleanAndOr` / `reassociateBooleanAndOr` / `reassociateFCmps` / `foldCastedBitwiseLogic` / `foldBinopOfSextBoolToSelect` | | 4018–4038 |
| O32 | `(sext i1 A) \| B → A ? -1 : B` **[comm]** | `1u` on the sext; `A` is `i1` | 4045 |
| O33 | `(X \| C) \| V → (X \| V) \| C` | `1u` on the inner or; `V` not a `ConstantInt`. `disjoint` is propagated: the inner new `or` takes the **outer** disjointness, and the result is disjoint only if both were — **[canon]** | 4058 |
| O34 | `(bool?A:B) \| (bool?C:D) → bool ? (A\|C) : (B\|D)` | same condition value; `1u` on both selects | 4072 |
| O35 | `((Y -nsw X) a>> (N-1)) \| X → X >s Y ? -1 : X` **[comm]** | `1u` on the ashr | 4084 |
| O36 | `canonicalizeCondSignextOfHighBitExtractToSignextHighBitExtract` | [V45](01-addsub-integer.md) | 4116 |

### Overflow-intrinsic patterns

| # | Rule | Side conditions | Line |
|---|---|---|---|
| O37 | `extractvalue(umul.with.overflow(A,B),1) \| (extractvalue(…,0) != 0) → (A != 0) & (B != 0)` | `1u` on the overflow bit, or on both the compare and the product. *The `or` weakens the condition to "any nonzero result counts as overflow", which for `umul` means both operands nonzero* | 4121 |
| O38 | `Ov \| (icmp pred Res, C2) → Ov \| (icmp pred X, C2∓C1)` | `WO` is an `add`/`sub` with-overflow whose RHS is `C1`; `1u` on the icmp; predicate signedness must match the intrinsic's, or be an equality. The new constant must not overflow, **unless** the predicate is an equality | 4147 |
| O39 | `foldOrUnsignedUMulOverflowICmp` (line 3724) | folds the whole `Ov \| icmp` into one comparison for `umul.with.overflow` | 4175 |

### Tail

| # | Rule | Side conditions | Line |
|---|---|---|---|
| O40 | `(~x) \| y → ~(x & ~y)` | `sinkNotIntoOtherHandOfLogicalOp` | 4179 |
| O41 | `(1 << X) \| ((1 << X) - 1) → -1 >>u ((N-1) - X)` **[comm]** | `1u` on one operand — *"low bit mask up to and including bit X"* | 4184 |
| O42 | `or` recurrence with invariant step → `or start, step` | `Step` dominates the PHI | 4194 |
| O43 | `(A & B) \| (C \| D) → C \| (D \| (A & B))` | `1u` throughout; fires when `C` or `D` is itself `A & ?` or `B & ?`, to bring the two `and`s together | 4201 |
| O44 | `reassociateForUses`, `canonicalizeLogicFirst`, `foldLogicOfIsFPClass`, `foldBinOpOfDisplacedShifts` | | 4229–4241 |
| O45 | `bitcast(F) \| signmask → bitcast(fneg(fabs F))` | sign bit in MSB; not `noimplicitfloat`. Note this **increases** instruction count unless the result is cast back — accepted for value-tracking | 4252 |
| O46 | `(X & C1) \| C2 → X & (C1 \| C2)` | `1u` on the and; the bits of `C2` are **known one** in `X` | 4271 |
| O47 | `foldBitwiseLogicWithIntrinsics` | 11a.9 | 4278 |
| O48 | `X \| Y → X[Y := 0] \| Y` **[comm]** | `simplifyAndOrWithOpReplaced` | 4281 |

---

# 11b.3 `visitXor` (line 4899)

Preamble: `simplifyXorInst`; `SimplifyAssociativeOrCommutative`;
`foldVectorBinop`; `foldBinopWithPhiOperands`; `foldXorToXor`;
`foldUsingDistributiveLaws`; `SimplifyDemandedInstructionBits`; **`foldNot`**;
`foldBinOpShiftWithShift`.

## `foldXorToXor` (line 4298)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| XX1 | `(A & B) ^ (A \| B) → A ^ B` **[comm ×4]** | — | 4312 |
| XX2 | `(A \| ~B) ^ (~A \| B) → A ^ B` **[comm ×4]** | — | 4320 |
| XX3 | `(A & ~B) ^ (~A & B) → A ^ B` **[comm ×4]** | — | 4328 |
| XX4 | `(A \| B) ^ ~(A & B) → ~(A ^ B)` | `1u` on one operand | 4340 |
| XX5 | `(A & B) ^ ~(A \| B) → ~(A ^ B)` | `1u` on one operand | 4340 |

## `foldNot` (line 4713) — `X ^ -1`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| N1 | `~(~X & Y) → X \| ~Y` **[comm]** | `1u` on the and | 4729 |
| N2 | `~(~X && Y) → X ? true : ~Y` | logical (select) form; `1u` | 4733 |
| N3 | `~(~X \| Y) → X & ~Y` **[comm]** | `1u` | 4740 |
| N4 | `~(~X \|\| Y) → X ? ~Y : false` | logical form; `1u` | 4744 |
| N5 | `~((-X) \| Y) → (X - 1) & ~Y` **[comm]** | `1u` on the or and the neg | 4752 |
| N6 | `~(~X a>> Y) → X a>> Y` | — | 4760 |
| N7 | `~(~X >>u Y) → X a>> Y` | **`isKnownNegative(X)`** — an `lshr` of a known-negative value behaves like an `ashr` | 4765 |
| N8 | `~(X a>> (N-1)) → sext(X >s -1)` | `1u` | 4772 |
| N9 | `~(C a>> Y) → ~C >>u Y` | `C` negative | 4784 |
| N10 | `~(C >>u Y) → ~C a>> Y` | `C` non-negative | 4789 |
| N11 | `~(X + C) → ~C - X` | `C` an `m_ImmConstant` | 4793 |
| N12 | `~(X - Y) → ~X + Y` | `X` a constant, or `1u` on the sub | 4798 |
| N13 | `~(~X + Y) → X - Y` **[comm]** | flags copied from the add | 4803 |
| N14 | `~(cmp A, B) → inverse-cmp A, B` | `1u` on the cmp, **or** all users can be freely inverted. Mutates the compare in place and inverts all its users | 4810 |
| N15 | `~bitcast(sext i1 X) → bitcast(sext(~X))` | `1u` on both; `X` is `i1` | 4821 |
| N16 | `sinkNotIntoLogicalOp` | `~(x op y) → ~x op' ~y` when **both** `x` and `y` are freely invertible and all users of the result can be updated | 4829 |
| N17 | `~min(~X, Y) → max(X, ~Y)` **[comm]** | `1u` on the intrinsic | 4835 |
| N18 | `~is_fpclass(X, M) → is_fpclass(X, ~M & fcAllFlags)` | `1u`; mutates in place | 4843 |
| N19 | `~select(C, cmpT, cmpF) → select(C, ~cmpT, ~cmpF)` | `1u` on the select; each arm must be a `1u` compare **or** a constant; predicates inverted in place | 4862 |
| N20 | `foldNotXor` (line 4531): `~((A&B) ^ (A\|?)) → (A&B) \| ~(A\|?)` | `1u` on the xor; the `and` and `or` must share an operand. 8 commuted variants | 4884 |
| N21 | `~V → getFreelyInverted(V)` | whenever the inversion costs nothing | 4890 |

## `visitXor` body

| # | Rule | Side conditions | Line |
|---|---|---|---|
| X1 | `(X \|disjoint Y) ^ M → (X ^ M) ^ Y` **[comm]** | `1u` on the disjoint or; the inner `xor` must itself simplify | 4935 |
| X2 | `(X & M) ^ (Y & ~M) → (X & M) \|disjoint (Y & ~M)` **[comm]** | `disjoint` set only if `isGuaranteedNotToBeUndef(M)` | 4948 |
| X3 | `visitMaskedMerge` (line 4498): `B ^ ((B ^ X) & ~M) → (D & M) ^ X` | `1u` on the and; `M` must literally be a `not` | 4959 |
| X4 | `visitMaskedMerge` with a constant mask: unfold to `(X & C) \| (B & ~C)` | `1u` on the inner xor; **undef lanes of `C` are clamped to -1** (propagating undef would be unsafe) | 4959 |

### With a constant `C1` on the RHS

| # | Rule | Side conditions | Line |
|---|---|---|---|
| X5 | `(X \| C2) ^ C1 → (X & ~C2) ^ (C1 ^ C2)` | `1u`; both `m_ImmConstant`. Undef lanes of `C2` replaced with all-ones, then merged back | 4966 |
| X6 | `(~X \| C2) ^ C1 → (X & ~C2) ^ ~C1` | `1u` | 4978 |
| X7 | `(~X & C2) ^ C1 → (X \| ~C2) ^ ~C1` | `1u` | 4983 |
| X8 | `(X a>> (N-1)) ^ C → (X >s -1) ? C : ~C` | `1u`; optional surrounding `trunc`; `C` must not be all-ones | 4994 |
| X9 | `(C - X) ^ signmask → (C + signmask) - X` | — | 5011 |
| X10 | `(X + C) ^ signmask → X + (C + signmask)` | — | 5015 |
| X11 | `(X \| C) ^ RHSC → X ^ (C ^ RHSC)` | `MaskedValueIsZero(X, C)` | 5019 |
| X12 | `ctlz(X) ^ (N-1) → cttz(X)` | `1u`; `is_zero_poison` true (`m_One()` second arg); `isKnownToBeAPowerOfTwo(X, OrZero=true)` | 5027 |
| X13 | `cttz(X) ^ (N-1) → ctlz(X)` | same | 5027 |
| X14 | `(X << C) ^ RHSC → (~X) << C` | `1u`; `RHSC == -1 << C` exactly — **[canon]** | 5044 |
| X15 | `(X >>u C) ^ RHSC → (~X) >>u C` | `1u`; `RHSC == -1 >>u C` | 5050 |
| X16 | `bitcast(F) ^ signmask → bitcast(fneg F)` | sign bit in MSB; not `noimplicitfloat` | 5066 |
| X17 | `((X ^ C1) >>u C2) ^ C3 → (X >>u C2) ^ ((C1>>C2) ^ C3)` | `1u`; **scalar only** (uses `m_ConstantInt`) | 5085 |

### Non-constant

| # | Rule | Side conditions | Line |
|---|---|---|---|
| X18 | `foldBinOpIntoSelectOrPhi` | | 5100 |
| X19 | `Y ^ (X \| Y) → X & ~Y` **[comm]** | `1u` on the or | 5105 |
| X20 | `Y ^ (X & Y) → ~X & Y` **[comm]** | `1u` on the and; **skipped when the other operand is a constant** (`(X & C) ^ C` is the canonical form; touching it loops) | 5113 |
| X21 | `(A ^ B) ^ (A \| C) → (~A & C) ^ B` **[comm ×4]** | `1u` on both | 5127 |
| X22 | `(A ^ B) ^ (B \| C) → (~B & C) ^ A` **[comm ×4]** | `1u` on both | 5133 |
| X23 | `(A & B) ^ (A ^ B) → A \| B` **[comm]** | — | 5139 |
| X24 | `(A & ~B) ^ ~A → ~(A & B)` **[comm]** | — | 5150 |
| X25 | `(~A & B) ^ A → A \| B` **[comm ×4]** | — | 5156 |
| X26 | `(~A \| B) ^ A → ~(A & B)` **[comm]** | `1u` on the or | 5160 |
| X27 | `(A \| B) ^ (A \| C) → (B ^ C) & ~A` **[comm ×4]** | `1u` on both ors | 5170 |
| X28 | `(A && B) ^ (A \|\| C) → A ? ~B : C` **[comm ×4]** | `i1` only; `1u` on both. **`A` is frozen** when both are real `select`s and `B == D` | 5183 |
| X29 | `foldXorOfICmps` | 11c | 5199 |
| X30 | `foldCastedBitwiseLogic` | 11a.3 | 5204 |
| X31 | `canonicalizeAbs` (line 4565): `(A + (A a>> (N-1))) ^ (A a>> (N-1)) → (A <s 0) ? -A : A` | the `ashr` must have **exactly 2** uses and the `add` `1u`. If the add was `nuw`, the negative arm becomes `0`; else the `neg` inherits the add's `nsw` — **[canon]** | 5207 |
| X32 | `(X ^ C1) ^ Y → (X ^ Y) ^ C1` **[comm]** | `1u` on the inner xor; `X` must not be a `ConstantExpr` (loop avoidance) — **[canon]** | 5215 |
| X33 | `reassociateForUses`, `canonicalizeLogicFirst`, `foldLogicOfIsFPClass`, `canonicalizeConditionalNegationViaMathToSelect`, `foldBinOpOfDisplacedShifts`, `foldBitwiseLogicWithIntrinsics` | | 5221–5236 |

