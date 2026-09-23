# `InstCombineShifts.cpp` — Part 10: `shl`, `lshr`, `ashr`

Back to [index](README.md).

**Semantic reminder.** In LLVM, a shift by an amount `>= bitwidth` yields
**`poison`**, not zero and not UB. Every rule that combines two shift amounts
must therefore prove the combined amount stays in range — and, symmetrically,
may *assume* each original amount was in range. This is the single most common
source of side conditions in this file.

`exact` on `lshr`/`ashr` = no nonzero bit is shifted out. `nuw`/`nsw` on `shl`
= no bit differing from the result's sign/zero extension is shifted out.

---

## 10.1 `commonShiftTransforms` (line 405) — all three opcodes

| # | Rule | Side conditions | Line |
|---|---|---|---|
| SH1 | `X shift (sext Y) → X shift (zext Y)` | `1u` on the sext. Sound because a negative shift amount would be out of range anyway — **[canon]** | 414 |
| SH2 | `SimplifyDemandedInstructionBits` | Part 20 | 420 |
| SH3 | `C shift select(...)` → sink into the select | `FoldOpIntoSelect` | 424 |
| SH4 | `FoldShiftByConstant` | §10.4 | 430 |
| SH5 | `reassociateShiftAmtsOfTwoSameDirectionShifts` | §10.2 | 434 |
| SH6 | `C shift (A +nuw C1) → (C shift C1) shift A` | the add must be `nuw` (or an `or disjoint`, via `m_NUWAddLike`). `nsw`/`nuw`/`exact` of the outer shift are carried | 440 |
| SH7 | `C << (X + AddC) → (C >>u -AddC) << X` | `AddC < 0`, `-AddC < N`; the shl needs `nsw` or `nuw`; **and `C` must be unchanged by a round trip** `(C >> p) << p`, i.e. the bits that would be lost are already zero. Output keeps `nuw` only | 456 |
| SH8 | `C >>u (X + AddC) → (C << -AddC) >>u X` | same shape; the `lshr` must be `exact`; `C == (C << p) >>u p`. Output is `exact` | 456 |
| SH9 | `C >>s (X + AddC) → (C << -AddC) >>s X` | same with `ashr`/`exact` | 456 |
| SH10 | `X shift (A %s C) → X shift (A & (C-1))` | `1u` on the `srem`; `C` a power of two. Sound because a *negative* shift amount is poison anyway, so the sign handling of `srem` is unobservable | 501 |
| SH11 | `foldShiftOfShiftedBinOp` | §10.3 | 511 |
| SH12 | `X shift (Y \| (N-1)) → X shift (N-1)` | any larger amount is poison, so the `or` forces exactly `N-1` | 514 |
| SH13 | `ucmp/scmp(A,B) >>u (N-1) → zext(A <u/<s B)` | only for `lshr`/`ashr`; `1u` on the cmp intrinsic. `lshr` → `zext`, `ashr` → `sext` | 517 |

## 10.2 `reassociateShiftAmtsOfTwoSameDirectionShifts` (line 58)

```
(X shiftop Q) shiftop K   →   X shiftop (Q + K)
```

Conditions:

* **Same opcode** for both shifts (unless only asking the sign-bit-extraction
  question).
* `zext` around either shift amount is looked through; a `trunc` between the
  two shifts is allowed but then **one operand of the outer shift must have
  one use** (an extra instruction is produced).
* `canTryToConstantAddTwoShiftAmounts` (line 23): after looking through
  extends, the shift-amount type may be *narrower* than the shifted type, so
  the sum could overflow there. The check requires
  `2^(shamtwidth) - 1 >= (N0-1) + (N1-1)`.
* `Q + K` must fold to a **constant** (`simplifyAddInst`) and be `u< bitwidth(X)`.
* With a `trunc` and **two right shifts**, the sum must be **exactly `N-1`** —
  i.e. it must be a sign-bit extraction; otherwise the truncation would drop
  bits the fold assumes are dead.
* Flags propagate **only if there was no trunc**: `nuw`/`nsw` if both shls had
  them; `exact` if both shrs had it.

The `AnalyzeForSignBitExtraction` mode answers "do these two right-shifts sum
to `N-1`?" without building anything; it returns `X` itself.

## 10.3 `foldShiftOfShiftedBinOp` (line 348)

```
shift (binop (shift X, C0), Y), C1  →  binop (shift X, C0+C1), (shift Y, C1)
```

* `binop` ∈ {`and`, `or`, `xor`, `add`, `sub`}; **`add`/`sub` only when the
  outer shift is `shl`**.
* `1u` on the binop; the inner shift must be `1u` **or** the other binop
  operand must be an `m_ImmConstant`.
* `C0 + C1 <u bitwidth`.
* `sub` is not commutative, so when the inner shift is operand 1 the operand
  order is preserved (`FirstShiftIsOp1`).

Purpose is dependency-chain shortening: the two new shifts are independent.

## 10.4 `FoldShiftByConstant` (line 783)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FS1 | `(C2 shift X) shift C1 → (C2 shift C1) shift X` | same opcode. `nuw`/`nsw` (shl) or `exact` (shr) iff both had them | 789 |
| FS2 | `(X /s DivC) >> (N-1) → ext(X <=s -DivC)` | right shifts only; `DivC != 0`, `DivC != INT_MIN`. Predicate is `sge` if `DivC < 0` else `sle`; extension is `sext` for `ashr`, `zext` for `lshr` | 812 |
| FS3 | propagate the shift into the operand tree | `canEvaluateShifted` (§10.5); **not for `ashr`** | 833 |
| FS4 | `foldBinOpIntoSelectOrPhi` | Part 21 | 842 |

Below here `Op0` must have one use.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| FS5 | `(X binop C) shift C1 → (X shift C1) binop (C shift C1)` | `canShiftBinOpWithConstantRHS` (line 766): `and`/`or` always; `add` only for `shl`; `xor` unless it is a `not` under a logical shift (a `not` is better for analysis than the resulting `xor`) | 851 |
| FS6 | `shift (select Cond, (X binop C), X), C1 → select Cond, ((X shift C1) binop (C shift C1)), (X shift C1)` | `1u` on the binop; the binop's operand 0 must literally be the other select arm, which must not be a constant; same `canShiftBinOpWithConstantRHS` check | 875 |
| FS7 | mirror of FS6 with the binop in the false arm | same | 893 |

## 10.5 `canEvaluateShifted` / `getShiftedValue` (lines 587, 704)

A speculative "can I rebuild this expression already shifted, at the same
cost?" traversal. Requires `1u` on every visited instruction. Used only for
`shl` and `lshr` outer shifts.

| Node | Can be shifted when | Result |
|---|---|---|
| `m_ImmConstant` | always | the shifted constant |
| `and`/`or`/`xor` | both operands can | operands rewritten in place |
| `select` | both arms can | arms rewritten in place |
| `phi` | all incoming can | incoming rewritten in place |
| `shl`/`lshr` | `canEvaluateShiftedShift` | `foldShiftedShift` |
| `mul X, C` | **right shift only**, `C` a negated power of two with `countr_zero(C) == NumBits` | `(-X) & lowbits(N - NumBits)` |

### `canEvaluateShiftedShift` (line 535) and `foldShiftedShift` (line 641)

For `Outer (Inner X, C1), C2` with both logical:

| Case | Condition | Result |
|---|---|---|
| same direction | always | `X shift (C1+C2)`, or `0` if `C1+C2 >= N`. **Inner flags cleared** (`nuw`/`nsw`/`exact` dropped) |
| opposite, `C1 == C2` | always | `X & mask` — low mask for inner-shl, high mask for inner-shr |
| opposite, `C1 > C2` | `C1 < N` **and** the bits the `and` would clear are already known zero (`MaskedValueIsZero`) | `X shift (C1 - C2)`, inner flags cleared, **no mask needed** |

> The "already known zero" precondition is what makes the third case
> profitable *and* correct without materialising the mask. Note the deliberate
> dropping of `nuw`/`nsw`/`exact` in `NewInnerShift` — the new shift amount
> invalidates the old premise.

## 10.6 `dropRedundantMaskingOfLeftShiftInput` (line 194) — `shl` only

Six spellings of "mask off the low `MaskShAmt` bits, then shift left":

```
a)  (x & ((1 << M) - 1))        << S
b)  (x & ~(-1 << M))            << S
c)  (x & (-1 l>> M))            << S
d)  (x & ((-1 << M) l>> M))     << S
e)  ((x << M) l>> M)            << S
f)  ((x << M) a>> M)            << S
       ⟹   x << S
```

Conditions:
* **a, b:** `M + S >=u bitwidth(x)`.
* **c–f:** `S >=u M`.
* The sum/difference must fold to a constant. It is computed in a type **twice
  as wide** (`getExtendedType`) so the sum cannot itself overflow.
* `undef` lanes in the folded shift amount are replaced (with the extended
  bitwidth, resp. `-bitwidth`) so the lane stays `undef` rather than becoming
  a wrong value.
* If the residual mask is not all-ones, the masking instruction must have
  `1u` **and must not have been an `ashr`** (an `ashr` does not merely mask).
* An intervening `trunc` is allowed only if it has one use.
* **`nuw`/`nsw` are deliberately not set** on the new shift: the guarantee that
  no nonzero bits are shifted out no longer holds.

## 10.7 `visitShl` (line 1041)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| L1 | `(zext X) << C → zext(X << C)` | `1u` on the zext; `C < SrcWidth`; the top `C` bits of `X` known zero | 1066 |
| L2 | `(X >> C) << C → X & (-1 << C)` | either shift kind | 1076 |
| L3 | `(X >>exact C1) << C → X << (C - C1)` | `C1 < C`. New `nuw` if the shl had `nuw`, **or** (`C1 != 0` and the shr was an `lshr` and the shl had `nsw`); `nsw` copied | 1082 |
| L4 | `(X >>exact C1) << C → X >>exact (C1 - C)` | `C1 > C`; same shr opcode | 1095 |
| L5 | `(X >> C1) << C → (X << (C - C1)) & (-1 << C)` | `1u` on the shr; `C1 < C`; flags as L3 | 1105 |
| L6 | `(X >> C1) << C → (X >> (C1 - C)) & (-1 << C)` | `1u`; `C1 > C`; `exact` copied to the new shr | 1117 |
| L7 | `(trunc (X >> C1)) << C → (trunc (X shift |C1-C|)) & (-1 << C)` | `1u` on both trunc and shr. The *larger* shift direction survives | 1131 |
| L8 | `((X >> C) binop Y) << C → (X binop (Y << C)) & (-1 << C)` | `1u` on the binop and the shr; binop ∈ {`add`,`sub`,`and`,`or`,`xor`}; commuted if the binop is commutative and `Y` has `1u`. **`sub` is not reordered** | 1163 |
| L9 | `(((X >> C) & CC) binop Y) << C → (X & (CC << C)) binop (Y << C)` | as L8; `disjoint` on an `or` is preserved | 1177 |
| L10 | `(C1 - X) << C → (C1 << C) - (X << C)` | `1u` on the sub | 1195 |
| L11 | infer `nuw`/`nsw` | `setShiftFlags`, §10.10 | 1202 |
| L12 | `(X >> Y) << Y → X & (-1 << Y)` | **variable** shift amount; `1u` on the shr; either shr kind | 1207 |
| L13 | `(-1 >>u Y) << Y → -1 << Y` | variable | 1215 |
| L14 | `(X * C2) << C1 → X * (C2 << C1)` | `C1`, `C2` `m_ImmConstant` | 1224 |
| L15 | `(zext i1 X) << C1 → X ? (1 << C1) : 0` | — | 1228 |
| L16 | `1 << ((N-1) - X) → signmask >>u X` | — | 1236 |
| L17 | `1 << cttz(X) → (-X) & X` | `1u` on the cttz — **[canon]** "extract lowest set bit" | 1241 |

## 10.8 `visitLShr` (line 1278)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| R1 | `(~X) >>u (N-1) → zext(X >s -1)` | `1u` on the not | 1295 |
| R2 | `((X <<nuw Z) -nuw Y) >>uexact Z → X -nuw (Y >>uexact Z)` | the outer `lshr` must be `exact`; `1u` on the sub; `nsw` carried | 1301 |
| R3 | `(X + Y) >>u 1 → X & Y` | both `X` and `Y` have at most 1 active bit (`countMaxActiveBits() <= 1`) | 1313 |
| R4 | `(X -nuw (Y <<nuw Z)) >>uexact Z → (X >>uexact Z) -nuw Y` | as R2 | 1319 |
| R5 | `((X <<nuw Z) binop nuw Y) >>u Z → X binop nuw (Y >>u Z)` **[comm]** | binop ∈ {`add`,`and`,`or`,`xor`}; `1u`; the binop must be `nuw` if it is an overflowing op. The inner `lshr` gets `exact` unless the binop is `and`. `disjoint` preserved for `or` | 1341 |

With a constant shift amount `C`:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| R6 | `ctlz(X) >>u log2(N) → zext(X == 0)` | `N` a power of two, shift amount exactly `log2(N)` | 1364 |
| R7 | `cttz(X) >>u log2(N) → zext(X == 0)` | same | 1364 |
| R8 | `ctpop(X) >>u log2(N) → zext(X == -1)` | same | 1364 |
| R9 | `(X <<nuw C1) >>u C → X >>u (C - C1)` | `C1 < C`; `exact` copied | 1379 |
| R10 | `(X << C1) >>u C → (X >>u (C-C1)) & (-1 >>u C)` | `1u`; `C1 < C` | 1386 |
| R11 | `(X <<nuw C1) >>u C → X <<nuw,nsw (C1 - C)` | `C1 > C`; the new `nsw` only when `C > 0` | 1395 |
| R12 | `(X << C1) >>u C → (X << (C1-C)) & (-1 >>u C)` | `1u`; `C1 > C` | 1402 |
| R13 | `(X << C) >>u C → X & (-1 >>u C)` | `C1 == C` | 1410 |
| R14 | `((X << C) + Y) >>u C → (X + (Y >>u C)) & (-1 >>u C)` **[comm]** | `1u` on the add and the shl | 1419 |
| R15 | `(zext X) >>u C → zext(X >>u C)` | `1u`; `shouldChangeType` | 1430 |
| R16 | `(sext i1 X) >>u C → X ? (-1 >>u C) : 0` | — | 1440 |
| R17 | `(sext X) >>u (N-1) → zext(X >>u (M-1))` | `1u`; `shouldChangeType`; `M` = source width | 1450 |
| R18 | `(sext iM X to iN) >>u (N-M) → zext(X >>s min(N-M, M-1))` | `1u`; `shouldChangeType` | 1456 |

With `C == N-1`:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| R19 | `(X \| -X) >>u (N-1) → zext(X != 0)` **[comm]** | `1u` | 1466 |
| R20 | `(X -nsw Y) >>u (N-1) → zext(X <s Y)` | `1u`; the sub must be `nsw` | 1470 |
| R21 | `(X %s 2) >>u (N-1) → (X >>u (N-1)) & X` | `1u`. *"negative and odd"* | 1475 |
| R22 | `((X-1) & ~X) >>u (N-1) → zext(X == 0)` **[comm]** | `1u` | 1481 |

Remaining constant cases:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| R23 | `(trunc (X >>u C1)) >>u C → (trunc (X >>u (C1+C))) & MaskC` | `1u` on the trunc; `C1 + C < SrcWidth`; and either `1u` on the inner shr or `C1 >= SrcWidth - N` (in which case the mask disappears) | 1487 |
| R24 | `(X *nuw (2^k+1)) >>u k → X` | `N > 2`; `2k == N`. *"splat" multiply* | 1508 |
| R25 | `(X *nuw (2^k+1)) >>u k → X +nuw (X >>u k)` | `1u`; `nsw` carried | 1513 |
| R26 | `(X *nuw MulC) >>u C → X *nuw,nsw (MulC >>u C)` | `1u`; `MulC` divisible by `2^C` | 1527 |
| R27 | `(X *nsw (2^k+1)) >>u k → X +nsw (X >>u k)` | `1u`; `N > 2` | 1540 |
| R28 | `bswap(zext X) >>u C → zext(bswap(X) >>u (C - WidthDiff))` | `1u` on both; `SrcWidth % 16 == 0`; `C >= WidthDiff` | 1552 |
| R29 | `bswap(zext X) >>u C → zext(bswap X) << (WidthDiff - C)` | same, `C < WidthDiff` | 1552 |
| R30 | `(zext(i1 X) + zext(i1 Y)) >>u 1 → zext(X & Y)` | `1u` on one of the three | 1573 |

Non-constant:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| R31 | infer `exact` | `setShiftFlags` | 1586 |
| R32 | `(X << Y) >>u Y → X & (-1 >>u Y)` | `1u` on the shl | 1590 |
| R33 | `(-1 << Y) >>u Y → -1 >>u Y` | — | 1597 |
| R34 | `foldLShrOverflowBit` | §10.9 | 1602 |
| R35 | `(P << x) >>u cttz(P << y) → (1 << x) >>u y` | `isKnownToBeAPowerOfTwo(P, OrZero=true)`; both shls need matching `nuw` or `nsw` | 1607 |

## 10.9 `foldLShrOverflowBit` (line 922)

```
(zext X + zext Y) >>u K   →   zext (icmp ult (X + Y), X)
```

* `X`, `Y` are `zext`s from exactly `K`-bit types, each `1u`.
* Result type has **more than 2 bits**, and `K > 1`.
* The `add` may only be used by this `lshr` and by truncations to `K` bits or
  narrower; those truncations are rewritten to use the narrowed add.
* **The new narrow `add` must not carry `nuw`/`nsw`** — the whole point is to
  observe the carry-out, which would be poison under those flags.

## 10.10 `setShiftFlags` (line 982) — flag inference, all three opcodes

| Inference | Condition |
|---|---|
| `exact` on a shr | the operand is `shl X, Y` with the *same* `Y` |
| `exact` on a shr | the shift amount is `cttz(operand)` |
| `nuw` on a `shl` | `maxShiftCount <= countMinLeadingZeros(Op0)` |
| `nsw` on a `shl` | `maxShiftCount < countMinSignBits(Op0)` |
| `exact` on a shr | `maxShiftCount <= countMinTrailingZeros(Op0)` |

`maxShiftCount` is `KnownBits(Op1).getMaxValue()` clamped to `N-1`, justified
by "a larger amount is poison anyway".

## 10.11 `visitAShr` (line 1710)

With a constant shift amount `ShAmt < N`:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A1 | `((zext X) << C) >>s C → sext X` | `C == N - SrcWidth` | 1727 |
| A2 | `(X <<nsw C1) >>s C2 → X >>s (C2 - C1)` | `C1 < C2`; the shl **must be `nsw`** (an ordinary `shl` shifts in arbitrary bits); `exact` copied | 1736 |
| A3 | `(X <<nsw C1) >>s C2 → X <<nsw (C1 - C2)` | `C1 > C2` | 1743 |
| A4 | `(X >>s C1) >>s C2 → X >>s min(C1+C2, N-1)` | oversized arithmetic shifts saturate at `N-1` | 1751 |
| A5 | `(sext X) >>s C → sext(X >>s min(C, M-1))` | `1u`; vector, or `shouldChangeType` | 1759 |
| A6 | `(X \| -X) >>s (N-1) → sext(X != 0)` **[comm]** | `1u` | 1770 |
| A7 | `(X -nsw Y) >>s (N-1) → sext(X <s Y)` | `1u` | 1774 |
| A8 | `((X-1) & ~X) >>s (N-1) → sext(X == 0)` **[comm]** | `1u` | 1779 |
| A9 | `(X *nsw (2^k+1)) >>s k → X +nsw (X >>s k)` | `1u`; `N > 2`; **`k < N-1`** (the sign bit); `nuw` carried | 1785 |

Non-constant:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A10 | infer flags | `setShiftFlags` | 1800 |
| A11 | `(X << (N-1)) >>s (N-1) → -(X & 1)` | `1u` on the shl. Undef lanes of both original constants are merged into the `1` mask — **[canon]** "splat the low bit" | 1806 |
| A12 | `foldVariableSignZeroExtensionOfVariableHighBitExtract` | §10.12 | 1819 |
| A13 | `X >>s Y → X >>u Y` | the sign bit of `X` is known zero; `exact` copied | 1823 |
| A14 | `(~X) >>s Y → ~(X >>s Y)` | `1u` on the not. **`exact` must be dropped**; the `-1` constant must not contain undef lanes | 1830 |

## 10.12 `foldVariableSignZeroExtensionOfVariableHighBitExtract` (line 1642)

```
((X >>? (N - NBits)) << (N - NBits)) >>s (N - NBits)
       ⟹  X >>s (N - NBits)      [and a trunc if one was present]
```

All three `N` constants must be splats of the relevant bitwidth
(`BitWidthSplat`), and the same `NBits` must appear in all three shift
amounts, modulo `zext`. If the innermost shift has the same opcode as the
outer `ashr`, the outer pair is simply redundant and the result is the inner
value. With a `trunc` present, one operand of the `ashr` must be `1u`.
`exact`-ness is preserved from the inner extraction.

