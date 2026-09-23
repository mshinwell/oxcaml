# `InstCombineAddSub.cpp` — Part 1: integer `add`

Back to [index](README.md). Conventions: see [Part 0](README.md#part-0--preliminaries).
`X`, `Y`, `Z`, `A`, `B` are arbitrary values; `C`, `C1`, `C2` are constants;
**[comm]** = the code uses a commutative matcher, so all operand orders match;
**[canon]** = canonicalisation (does not reduce instruction count).
`1u` on a pattern = that subterm is required to have exactly one use.

---

## 1.1 `foldAddWithConstant` — `add X, C` (line 856)

Guarded by `Op1` being an `m_ImmConstant`. Runs `foldBinOpIntoSelectOrPhi`
first (see Part 12).

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A1 | `(C1 - X) + C2 → (C1 + C2) - X` | — | 869 |
| A2 | `(X - Y) + (-1) → (~Y) + X` | `1u` on the `sub` | 876 |
| A3 | `zext(i1 B) + C → B ? C+1 : C` | `B` is `i1` | 881 |
| A4 | `sext(i1 B) + C → B ? C-1 : C` | `B` is `i1` | 885 |
| A5 | `(~X) + C → (C-1) - X` | output gets `nsw` iff input had `nsw` **and** `C-1` does not signed-overflow | 890 |
| A6 | `(X s>> (N-1)) + 1 → zext(X s> -1)` | `N` = bitwidth; `1u` on the `ashr` | 902 |

Below here `C` is additionally required to be an `m_APInt` (splat).

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A7 | `(X \|disjoint C1) + C2 → X + (C1 + C2)` | the `or` is `disjoint` (so it *is* an add). Output `nsw` iff input `nsw` and `C1+C2` no signed overflow; output `nuw` iff input `nuw` | 913 |
| A8 | `(X \| C1) + C2 → (X \| C1) ^ C1` | `C1 == -C2` | 925 |
| A9 | `X + signmask → X \| signmask` | `add` has `nsw` or `nuw`. *(If the add cannot wrap and the sign bit is added, the sign bit of `X` must have been clear.)* | 931 |
| A10 | `X + signmask → X ^ signmask` | otherwise (wrapping allowed) — **[canon]** | 936 |
| A11 | `zext(X ^ C1) + C2 → sext X` | `C1` is `INT_MIN` of the narrow type and `sext(C1) == C2`. *This is the tail of an open-coded sign extension.* | 942 |

Patterns below match `Op0 = X ^ C1`:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A12 | `(X ^ signmask) + C → X + (signmask ^ C)` | — | 948 |
| A13 | `(X ^ C1) + C → (C1 + C) - X` | `C1` is a low-bit mask **and** `X` has no bits set above it (`(C1 \| knownzero(X)).isAllOnes()`) | 954 |
| A14 | `(X ^ C1) + C → (X << k) s>> k` | `1u` on the xor; `C1 == -C`; one of `C`/`C1` is a power of two, `k = N - log2(pow2) - 1`; **and** the top `k` bits of `X` are known zero. *Open-coded sign-extend-in-register.* | 964 |

With `C == 1` and `1u` on `Op0`:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A15 | `sext(i1 X) + 1 → zext(~X)` | `X` is `i1` | 986 |
| A16 | `((X << (N-1)) s>> (N-1)) + 1 → (~X) & 1` | both shift amounts equal `N-1` | 994 |

| # | Rule | Side conditions | Line |
|---|---|---|---|
| A17 | `umax(X, C) + (-C) → usub.sat(X, C)` | `1u` on the `umax` | 1002 |
| A18 | `zext(X + (-1)) + 1 → zext X` | `C == 1`; `isKnownNonZero(X)` | 1009 |

> **Proof note for A18:** needs `X != 0` so that `X-1` does not wrap in the
> narrow type; with wrapping, `zext(0-1) + 1 = 2^n`, not `0`.

---

## 1.2 `foldNoWrapAdd` — constants across an extend (line 809)

The theme: a no-wrap flag on the *inner* narrow add lets a constant move
through the extension.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| N1 | `zext(X +nuw C2) + C1 → zext(X + (C2 + trunc C1))` | `C1 < 0` and `C1 >= -sext(C2)`; either the new narrow constant is 0 (then just `zext X`), or `1u` on the `zext` | 819 |
| N2 | `sext(X +nsw C2) + C → sext(X) + (sext(C2) + C)` | `1u` on the `sext`. Also matches `zext nneg` (`m_SExtLike`) | 838 |
| N3 | `zext(X +nuw C2) + C → zext(X) + (zext(C2) + C)` | `1u` on the `zext` | 846 |

> N2/N3 are **[canon]**-ish: instruction count is unchanged (the constant
> add folds away), but the extend is pushed toward the leaves.

---

## 1.3 `visitAdd` main body (line 1521)

Preamble, in order: `simplifyAddInst`; `SimplifyAssociativeOrCommutative`;
`foldVectorBinop`; `foldBinopWithPhiOperands`; `foldUsingDistributiveLaws`
(`(A*B)+(A*C) → A*(B+C)`, see Part 12); `foldBoxMultiply`;
`factorizeMathWithShlOps`; `foldAddWithConstant`; `foldNoWrapAdd`;
`foldBinOpShiftWithShift`; `combineAddSubWithShlAddSub`;
`foldAddLikeCommutative` (both operand orders).

### Type-driven

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V1 | `add i1 X, Y → X ^ Y` | type is `i1`/`<n x i1>` | 1553 |
| V2 | `X + X → X << 1` | flags `nsw`/`nuw` copied from the add | 1556 |

### Negation

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V3 | `(-A) + (-B) → -(A + B)` | — | 1566 |
| V4 | `(-A) + B → B - A` | output `nsw` iff add `nsw` **and** the `neg` was `nsw` | 1569 |
| V5 | `A + (-B) → A - B` | same flag rule | 1577 |

### `checkForNegativeOperand` (line 752)

Requires `1u` on at least one of the two `add` operands (the rewrite emits two
instructions).

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V6 | `((Z \| ~C1) ^ C1) + 1 + RHS → RHS - (Z & C1)` | — | 776 |
| V7 | `((Z & C1) ^ C1) + 1 + RHS → RHS - (Z \| ~C1)` | — | 781 |
| V8 | `((Z & C2) ^ C1) + RHS → RHS - (Z \| ~C2)` | `C1 == C2 + 1` and `C1` is **odd** | 800 |

> All three are instances of `~V + 1 == -V` after recognising a De-Morgan'd
> inner term. V8 folds the `+1` into the xor constant, which is why `C1` must
> be odd (no carry out of bit 0).

### Reassociation with `not` / `1`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V9 | `(A + 1) + (~B) → A - B` **[comm]** | also matches `(~B + A) + 1` | 1591 |
| V10 | `(A + RHS) + RHS → A + (RHS << 1)` | `1u` on inner add **[comm]** | 1597 |
| V11 | `LHS + (A + LHS) → A + (LHS << 1)` | `1u` on inner add **[comm]** | 1601 |
| V12 | `(A + C1) + (C2 - B) → (A - B) + (C1 + C2)` **[comm]** | `1u` on one of the two operands | 1607 |
| V13 | `(C1 - A) + B → (B - A) + C1` **[comm]** | `1u` on the sub — **[canon]**, moves the constant to the add | 1616 |

### `SimplifyAddWithRemainder` (line 1156)

`MatchRem` also accepts `X & (2^k - 1)` as `X urem 2^k`; `MatchMul` accepts
`X << k` as `X * 2^k`; `MatchDiv` accepts `X lshr k` as `X udiv 2^k`.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V14 | `(X % C0) + ((X / C0) % C1) * C0 → X % (C0 * C1)` **[comm]** | same signedness throughout; `C0 * C1` must not overflow (`smul_ov`/`umul_ov`) | 1170 |
| V15 | `(X / C0) * C1 + (X % C0) * C2 → (X / C0) * (C1 - C2*C0) + X * C2` | same signedness; if `C1 - C2*C0 != 0` then `1u` on the rem; **`isGuaranteedNotToBeUndef(X)`** (X is duplicated); skipped when `C1==1 && unsigned && C0` is a power of two ≠ 2 (would turn an `and` into a `mul`) | 1196 |

### Bit-level identities

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V16 | `(A & 2^k) + A → A & (2^k - 1)` **[comm]** | `ComputeNumSignBits(A) > countl_zero(2^k)`, i.e. bit `k` of `A` is a copy of the sign bit | 1625 |
| V17 | `zext(B -nuw A) + zext(A) → zext(B)` **[comm]** | inner sub must be `nuw` | 1632 |
| V18 | `zext(i1 A) + sext(i1 A) → 0` **[comm]** | `A` is `i1` (`zext` gives 0/1, `sext` gives 0/-1) | 1640 |
| V19 | `sext(A <pred B) + zext(A >pred B) → scmp/ucmp(A, B)` **[comm]** | one predicate is a `<`, the other a `>`, with **matching signedness**; integer operands | 1646 |
| V20 | `A + B → A \|disjoint B` | `haveNoCommonBitsSet(A, B)` — **[canon]** | 1666 |
| V21 | `(A ^ B) + (A & B) → A \| B` **[comm]** | — | 1673 |
| V22 | `(A \| B) + (A & B) → A + B` **[comm]** | rewritten in place to keep `nuw`/`nsw` | 1680 |
| V23 | `A + (A \| -A) → (A - 1) & A` **[comm]** | `1u` on the `or`; the new `add` inherits `nuw`/`nsw` | 1690 |
| V24 | `(A & -A) - 1 → (A - 1) & ~A` | `1u` on the `and` and on the `neg` — **[canon]**, helps `ctpop → cttz` | 1700 |

### Multiply-flavoured reassociation

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V25 | `~(A * C1) + A → (A * (1 - C1)) - 1` **[comm]** | `1u` on both the `not` and the `mul` | 1715 |
| V26 | `(A * -2^k) + B → B - (A << k)` **[comm]** | `1u` on the `mul` | 1727 |
| V27 | `foldBoxMultiply`: `((XLo*YHi + YLo*XHi) << H) + XLo*YLo → X * Y` | even bitwidth; `H = N/2`; `XLo = X & (2^H-1)`, `YLo = Y & (2^H-1)`; the high halves are `lshr` by `H`; `1u` on the low multiply. Cross terms may use `X` or `XLo` interchangeably | 1482 |
| V28 | `foldSquareSumInt`: `a*a + 2ab + b*b → (a+b)^2` | several shapes, all with `1u` on the sub-products; `2x` matched as `x << 1` | 1058 |

### `foldAddLikeCommutative` (line 1316), tried both orders

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V29 | `(A - B) + (C - A) → C - B` | output `nsw` iff add `nsw` and both subs `nsw`; output `nuw` iff both subs `nuw` (note: **not** gated on the add's `nuw`) | 1318 |
| V30 | `((X s/ C1) << C2) + X → X s% (-C1)` | `-C1 == 1 << C2` | 1334 |

### Comparison / signum shapes

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V31 | `(A s>> (N-1)) + zext(A s> 0) → (A s>> (N-1)) \| zext(A != 0)` | `1u` on the `zext` and the `icmp` — **[canon]** signum | 1738 |
| V32 | `X + zext/sext(X == C) → (X == C) ? C ± 1 : X` | `1u` on the extend; `+1` for `zext`, `-1` for `sext` | 1752 |
| V33 | `(A + 1) + sext(A != 0) → umax(A, 1)` | `1u` on the `sext` and the `icmp` | 1771 |
| V34 | `foldAddToAshr`: `(X s/ 2^k) + sext(...rounding test...) → X s>> k` | `2^k` positive power of two; the second operand must be exactly the canonical round-toward-zero correction, either `sext((X & (SMIN\|(2^k-1))) u> SMIN)` or, for `k==1`, `sext((X & (SMIN+1)) == SMIN+1)` | 1278 |

### Saturating / ceiling idioms

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V35 | `canonicalizeLowbitMask`: `(1 << NBits) - 1 → ~(-1 << NBits)` | `1u` on the `shl`. New `shl` is always `nsw`; `nuw` copied from the `add` — **[canon]** | 1221 |
| V36 | `umin(X, ~Y) + Y → uadd.sat(X, Y)` **[comm]** | — | 1247 |
| V37 | `umin(X, ~C) + C → uadd.sat(X, C)` | — | 1253 |
| V38 | `usub.sat(A, B) + B → umax(A, B)` **[comm]** | `1u` on the intrinsic | 1863 |
| V39 | `(X >> k) + zext((X & (2^k - 1)) != 0) → (X + (2^k-1)) >> k` **[comm]** | `1u` on the `lshr`; `popcount(Mask) == k`; **`willNotOverflowUnsignedAdd(X, Mask)`** | 1787 |

### Inversion, ctpop, log2

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V40 | `(~X) + (~Y) → -2 - (X + Y)` | **both** operands must be freely invertible *and consuming* (`isFreeToInvert` with `ConsumesLHS/RHS` true), so no extra instruction is created | 1810 |
| V41 | `ctpop(A) + ctpop(B) → ctpop(A \| B)` | `1u` on both; `haveNoCommonBitsSet(A, B)` | 1870 |
| V42 | `zext(ctpop(A) >u 1) + (ctlz(A, true) ^ (N-1)) → N - ctlz(A-1, false)` | predicate `ugt` or `ne`; `1u` on nearly every subterm; `XorC == N-1`. *log2_ceil idiom* | 1884 |

### Flag inference (not a rewrite)

At line 1836 the pass *adds* `nsw`/`nuw` to the existing `add` when
`willNotOverflowSignedAdd` / `willNotOverflowUnsignedAdd` prove it. If a flag
was added and the add is the step of a simple recurrence, users of the PHI are
re-queued (line 1916).

### `combineAddSubWithShlAddSub` (line 1265)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V43 | `A + ((-B) << Cnt) → A - (B << Cnt)` **[comm]** | `1u` on both the `shl` and the `neg` | 1268 |

### `factorizeMathWithShlOps` (line 1446), shared with `sub`

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V44 | `(X << S) ± (Y << S) → (X ± Y) << S` | `1u` on at least one operand. Output gets `nsw` only if *all three* of the add/sub and both shls had `nsw`; likewise `nuw` | 1466 |

### `canonicalizeCondSignextOfHighBitExtractToSignextHighBitExtract` (line 1347)

Shared by `add`, `or`, `sub`.

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V45 | `(X >>u (N - NBits)) + (X <s 0 ? (-1 << NBits) : 0) → X >>s (N - NBits)` | the shift amount must literally be `N - NBits`; the select condition must be a sign-bit test of the *same* `X` (`isSignBitCheck`); the select's other arm must be zero. For `sub` the magic constant is `1` instead of `-1` and the select must be on the RHS. A surrounding `trunc` is allowed if something else becomes dead. `exact` is preserved onto the new `ashr` | 1347 |


---

# `InstCombineAddSub.cpp` — Part 2: integer `sub`

`visitSub` (line 2238). Preamble: `simplifySubInst`; `foldVectorBinop`;
`foldBinopWithPhiOperands`.

Two structural facts dominate this function:

* **`sub` is aggressively rewritten into `add` of a negation.** The `Negator`
  (see Part 3) is invoked early and tries to sink `0 - X` into `X`'s own
  definition. Almost everything reachable *after* the Negator call therefore
  assumes `Op0` is not zero.
* The final `return` is `TryToNarrowDeduceFlags()`, which runs
  `narrowMathIfNoOverflow` and then *infers* `nsw`/`nuw` on the existing `sub`.

## 2.1 Early, before the Negator

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S1 | `X - (-A) → X + A` | `dyn_castNegVal`. Output `nsw` iff the `sub` had `nsw` **and** either the inner sub had `nsw` or (for a constant) the constant is not `INT_MIN` | 2250 |
| S2 | `(X << S) - (Y << S) → (X - Y) << S` | `factorizeMathWithShlOps`, see V44 | 2269 |
| S3 | `C - (X + C2) → (C - C2) - X` | output `nsw` iff sub `nsw` **and** inner add `nsw` **and** `C - C2` does not signed-overflow; output `nuw` iff sub `nuw` and inner add `nuw` | 2277 |

### The Negator escape hatch (line 2315)

`sub Op0, Op1` is treated as `add Op0, (0 - Op1)`, and `Negator::Negate` tries
to produce `-Op1` for free. **Exception:** if this is a pure negation
(`Op0 == 0`) and some user is a `select` of the form `select(_, Op1, thisNeg)`
— i.e. an `abs`/`nabs` idiom — the negation is left alone so the abs pattern
still matches later.

If `Op0 == 0` and the Negator failed, `visitSub` stops here.

## 2.2 Distributive / type folds

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S4 | `(A*B) - (A*C) → A*(B-C)` etc. | `foldUsingDistributiveLaws` | 2334 |
| S5 | `sub i1 X, Y → X ^ Y` | type is `i1` | 2337 |
| S6 | `-1 - A → ~A` | — **[canon]** | 2341 |
| S7 | `(X + -1) - Y → (~Y) + X` | `1u` on the add | 2346 |
| S8 | `(X & C1) - (X & C2) → X & (C1 ^ C2)` | `(C1 & C2) == C2`, i.e. `C2 ⊆ C1` | 2352 |

## 2.3 Reassociation of add/sub chains

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S9 | `((X - Y) + Z) - W → (X + Z) - (Y + W)` | `1u` on both the outer add and the inner sub. *Shortens the dependency chain* | 2364 |
| S10 | `(X - Y) - W → X - (Y + W)` | `1u` on the inner sub. `nuw` iff both had `nuw`; `nsw` only if **also** `nuw` holds and both had `nsw` (note the unusual conjunction) | 2372 |
| S11 | `(X + Z) - (Y + Z) → X - Y` | — | 2386 |
| S12 | `(X + C0) - (Y + C1) → (X - Y) + (C0 - C1)` | `1u` on both adds | 2392 |
| S13 | `(W + X) - (Y + Z) → X - Z` etc. | uses `m_AddLike` (matches `or disjoint` too); fires for any of `W==Y`, `W==Z`, `X==Y`, `X==Z`. `nsw` iff sub and both add-likes `nsw`; **`nuw` iff sub `nuw` and only the *RHS* add-like `nuw`** | 2403 |
| S14 | `(~X) - (~Y) → Y - X` | both operands freely invertible **and** at least one *consuming* (else infinite loop) | 2431 |

> **S13's asymmetric `nuw`:** `(W+X) - (Y+Z)` with `W == Y` becomes `X - Z`.
> Unsigned non-wrap of the result needs `X >= Z`; the sub's own `nuw` gives
> `W+X >= Y+Z` and the RHS `nuw` gives `Y+Z` exact, which together yield it.
> The LHS's `nuw` is not needed. Worth double-checking when porting.

## 2.4 Constant on the left (`Op0` is a `Constant`)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S15 | `C - zext(i1 X) → X ? C-1 : C` | `X` is `i1` | 2464 |
| S16 | `C - sext(i1 X) → X ? C+1 : C` | `X` is `i1` | 2467 |
| S17 | `C - (~X) → X + (C+1)` | — | 2472 |
| S18 | `C - select(...)` → sink into the select arms | `FoldOpIntoSelect` | 2476 |
| S19 | `C - phi(...)` → sink into the phi | `foldOpIntoPhi` | 2481 |
| S20 | `C - (C2 - X) → X + (C - C2)` | — | 2488 |

With `Op0` an `m_APInt`:

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S21 | `C - Y → Y ^ C` | `C` is a low-bit mask **and** all bits outside it are known zero in `Y`. Deliberately uses `getWithoutDomCondCache()` so the transform stays easy to reverse | 2494 |
| S22 | `C - ((C3 -nuw X) & C2) → (C - (C2&C3)) + (X & C2)` | `(C3 - ((C2&C3)-1))` is a power of two; `((C2&C3)-1) ⊆ (C2+C3)`; and either the inner sub is `nuw` or `C2` is a negated power of two | 2509 |

## 2.5 Logic-op identities

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S23 | `X - (X + Y) → -Y` **[comm]** | — | 2530 |
| S24 | `(X - Y) - X → -Y` | — | 2534 |
| S25 | `(A \| B) - (A & B) → A ^ B` | — | 2541 |
| S26 | `(A + B) - (A \| B) → A & B` | — | 2549 |
| S27 | `(A + B) - (A & B) → A \| B` | — | 2557 |
| S28 | `(A & B) - (A \| B) → -(A ^ B)` | `1u` on one operand | 2565 |
| S29 | `(A \| B) - (A ^ B) → A & B` | — | 2574 |
| S30 | `(A ^ B) - (A \| B) → -(A & B)` | `1u` on one operand | 2582 |
| S31 | `(X \| Y) - X → ~X & Y` **[comm]** | `1u` on the or | 2592 |
| S32 | `(Y & -X) - Y → -(Y & (X - 1))` **[comm]** | `1u` on the and and on the neg | 2600 |
| S33 | `(Y & C) - Y → -(Y & ~C)` | `1u` on the and | 2610 |
| S34 | `X - (X & Y) → X & ~Y` **[comm]** | `1u` on the and **or** `Y` is a constant | 2676 |

## 2.6 Select / min-max

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S35 | `(X ^ sext(C)) - sext(C) → C ? -X : X` | `C` is `i1`; `1u` on the xor | 2617 |
| S36 | `sext(C) - (X ^ sext(C)) → C ? X : -X` | same | 2618 |
| S37 | `(A+B) - umin/smin(A,B) → umax/smax(A,B)` | `1u` on one side | 2200 |
| S38 | `(A+B) - umax/smax(A,B) → umin/smin(A,B)` | same | 2200 |
| S39 | `(X + Y) - umin(Y, Z) → X + usub.sat(Y, Z)` | `1u` on the umin and the add | 2213 |
| S40 | `Op0 - smin(Op0 -nsw Z, 0) → smax(Op0, Z)` | inner sub must be `nsw` | 2228 |
| S41 | `Op0 - smax(Op0 -nsw Z, 0) → smin(Op0, Z)` | same | 2228 |
| S42 | sink `sub` into a `select` whose arm equals the other `sub` operand | `1u` on the select; result is `select Cond, 0, (sub ...)` or the mirror. Preserves `prof` metadata | 2629 |
| S43 | `~X - max/min(~X, Y) → ~max/min(X, ~Y) - X` **[comm]** | `~X` has < 3 uses; `Y` freely invertible | 2683 |
| S44 | `max/min(~X, Y) - ~X → X - ~max/min(X, ~Y)` **[comm]** | same | 2690 |
| S45 | `smax(X,Y) - smin(X,Y) → abs(X -nsw Y)` | the `sub` must have `nsw` or `nuw`; `1u` on both min/max. The `abs` is created with `is_int_min_poison = true` | 2823 |

## 2.7 Saturating arithmetic

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S46 | `X - usub.sat(X, Y) → umin(X, Y)` | `1u` | 2762 |
| S47 | `umax(X, Op1) - Op1 → usub.sat(X, Op1)` **[comm]** | `1u` | 2770 |
| S48 | `Op0 - umin(X, Op0) → usub.sat(Op0, X)` **[comm]** | `1u` | 2776 |
| S49 | `Op0 - umax(X, Op0) → -usub.sat(X, Op0)` **[comm]** | `1u` | 2781 |
| S50 | `umin(X, Op1) - Op1 → -usub.sat(Op1, X)` **[comm]** | `1u` | 2787 |

## 2.8 Pointer differences (`OptimizePointerDifference`, line 2152)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S51 | `ptrtoint(P) - ptrtoint(Q) → offsetof(P) - offsetof(Q)` | `P` and `Q` must share a common base pointer, found by walking GEP chains (`CommonPointerBase::compute`). Result `nsw` iff both chains `inbounds`; `nuw` iff the sub was `nuw` and both chains `nuw` | 2747 |
| S52 | `trunc(ptrtoint P) - trunc(ptrtoint Q) → trunc(P - Q)` | as above, but `IsNUW` forced false | 2754 |
| S53 | `zext(ptrtoint(gep Q, off)) - zext(ptrtoint Q) → zext/sext(off)` | the GEP must have `nuw` or `nusw`; `zext` (with `nneg` if `nusw`) for `nuw`, `sext` otherwise | 2760 |

> The whole `CommonPointerBase` machinery is really *one* rule with a
> substantial matching procedure. For porting, note the flag derivation: a
> single `inbounds` GEP with a `nuw` outer sub also makes the offset's final
> `mul`/`shl` `nuw` (line 2166).

## 2.9 Remaining `sub` idioms

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S54 | `(A ^ (A s>> (N-1))) - (A s>> (N-1)) → (A <s 0) ? -A : A` | the `ashr` must have **exactly 2** uses, `1u` on the xor. If the `sub` was `nuw`, the negative arm becomes `0`; otherwise the `neg` inherits `nsw` — **[canon]** abs | 2729 |
| S55 | `(X + AddC) - (X & AndC) → (X + AddC) & ~AndC` | `AndC` must have no bits at or above `cttz(AddC)` — i.e. the add cannot carry into any masked bit | 2746 |
| S56 | `sub_rdx(V0) - add_rdx(V1) → add_rdx(V0 - V1)` | both are `vector_reduce_add` with `1u`, same vector type | 2448 |
| S57 | `N - ctpop(X) → ctpop(~X)` | `Op0` is exactly the bitwidth; `1u` on the ctpop | 2795 |
| S58 | `(X*X) - (Y*Y) → (X+Y) * (X-Y)` | `1u` on both muls. `nsw` propagates only if sub and both muls `nsw` **and bitwidth > 2**; `nuw` similarly with **bitwidth > 1** | 2803 |
| S59 | `sext(X +nsw Y) - sext(X) → sext(Y)` **[comm on the add]** | uses `m_SExtLike` (so `zext nneg` counts) | 2835 |
| S60 | `sext(X +nsw Y) - sext(X +nsw Z) → sext(Y) - sext(Z)` | a cost check: number of newly dead instructions ≥ number of new `sext`s. Output `nsw` copied from the sub | 2843 |
| S61 | `tryFoldInstWithCtpopWithNot` | see Part 12 | 2621 |

