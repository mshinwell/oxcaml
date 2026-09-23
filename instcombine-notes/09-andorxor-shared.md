# `InstCombineAndOrXor.cpp` — Part 11a: helpers shared by `and`/`or`/`xor`

Back to [index](README.md). This file is split into three parts:

* **11a (this file)** — helpers shared by two or three of the bitwise ops.
* **[11b](10-andorxor-visitors.md)** — `visitAnd`, `visitOr`, `visitXor`.
* **[11c](11-andorxor-cmps.md)** — `and`/`or`/`xor` **of comparisons**, the
  largest and most intricate group.

---

## 11a.1 De Morgan (`matchDeMorgansLaws`, line 1696)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| DM1 | `(~A) & (~B) → ~(A \| B)` | `1u` on both `not`s, **and** neither `A` nor `B` is itself freely invertible (otherwise the inverse fold would loop) | 1690 |
| DM2 | `(~A) \| (~B) → ~(A & B)` | same | 1690 |
| DM3 | `(A & ~B) & ~C → A & ~(B \| C)` **[comm on the inner op]** | `1u` on the inner binop | 1704 |
| DM4 | `(A \| ~B) \| ~C → A \| ~(B & C)` **[comm]** | same | 1704 |

> The `!isFreeToInvert(A) && !isFreeToInvert(B)` guard in DM1/DM2 is a
> **termination condition**, not a soundness one: if `A` were freely
> invertible, other folds would push the `not` back down and the pass would
> oscillate. Any port with a similar inverse rule needs the same guard.

## 11a.2 And/or ↔ xor (`foldAndToXor` line 1896, `foldOrToXor` line 1922)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| X1 | `(A \| B) & ~(A & B) → A ^ B` | operand order fixed by complexity canonicalisation | 1904 |
| X2 | `(A \| ~B) & (~A \| B) → ~(A ^ B)` **[comm ×4]** | `1u` on one operand | 1913 |
| X3 | `(A & B) \| ~(A \| B) → ~(A ^ B)` | `1u` on one operand | 1930 |
| X4 | `(A ^ B) \| ~(A \| B) → ~(A & B)` | `1u` on one operand | 1937 |
| X5 | `(A & ~B) \| (~A & B) → A ^ B` **[comm ×4]** | — | 1948 |

## 11a.3 Casts (`foldCastedBitwiseLogic` line 1784, `foldLogicCastConstant` line 1749)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| C1 | `(A >>u (N-1)) op zext(icmp) → zext((A <s 0) op icmp)` **[comm]** | `1u` on both the `lshr` and the `zext`; shift amount exactly `N-1` | 1793 |
| C2 | `op (zext X), C → zext(op X, C')` | `1u` on the cast; `C` must survive `getLosslessUnsignedTrunc` to the source type | 1758 |
| C3 | `op (sext X), C → sext(op X, C')` | `1u`; `getLosslessSignedTrunc`. `m_SExtLike` also matches `zext nneg` | 1767 |
| C4 | `op (zext/sext X), (zext/sext Y) → zext/sext(op X, Y)` | **same** cast opcode on both; at least one `1u`. If the source widths differ, **both** must be `1u` and the narrower is first extended to the wider source type. `disjoint` is preserved onto the narrow `or` | 1830 |
| C5 | `op (cast A), (cast B) → cast(op A, B)` | same cast opcode, **same source type**; both pass `shouldOptimizeCast` (neither is a no-op cast, a cast of a constant, or part of an eliminable cast pair) | 1866 |

## 11a.4 `narrowMaskedBinOp` (line 1965) — `and` only

```
and (binop (zext X), C), (zext X)   →   zext (and (binop X, C'), X)
and (sub C, (zext X)),   (zext X)   →   zext (and (sub C', X), X)
```

* `binop` ∈ {`add`, `mul`, `lshr`, `shl`}, plus the `sub`-with-constant-LHS
  form. (`ashr` is excluded: it should already have become `lshr` here.)
* `1u` on the binop; the `zext` must have **fewer than 3 uses**.
* `shouldChangeType(Ty, X->getType())` unless vector.
* **For `shl`/`lshr`, `canNarrowShiftAmt`** (line 1958): the constant shift
  amount must be provably `<u` the *narrow* bitwidth, else the narrowed shift
  would be poison where the wide one was not.

## 11a.5 `foldComplexAndOrPatterns` (line 2006)

Eight rules, each stated once for `and` and once for `or` (the code is written
generically over `Opcode`/`FlippedOpcode`). All are heavily `1u`-guarded.

| # | `or` form | `and` form | Line |
|---|---|---|---|
| CX1 | `(~(A\|B) & C) \| (~(A\|C) & B) → (B ^ C) & ~A` | `(~(A&B) \| C) & (~(A&C) \| B) → ~((B ^ C) & A)` | 2091 |
| CX2 | `(~(A\|B) & C) \| (~(B\|C) & A) → (A ^ C) & ~B` | `(~(A&B) \| C) & (~(B&C) \| A) → ~((A ^ C) & B)` | 2101 |
| CX3 | `(~(A\|B) & C) \| ~(A\|C) → ~((B & C) \| A)` | `(~(A&B) \| C) & ~(A&C) → ~((B \| C) & A)` | 2111 |
| CX4 | `(~(A\|B) & C) \| ~(B\|C) → ~((A & C) \| B)` | `(~(A&B) \| C) & ~(B&C) → ~((A \| C) & B)` | 2118 |
| CX5 | `(~(A\|B) & C) \| ~(C \| (A^B)) → ~((A\|B) & (C \| (A^B)))` | **not valid** — see note | 2128 |
| CX6 | `(~A & B & C) \| ~(A\|B\|C) → ~(A \| (B ^ C))` | `(~A \| B \| C) & ~(A&B&C) → ~A \| (B ^ C)` | 2156 |
| CX7 | `(~A & B & C) \| ~(A\|B) → (C \| ~B) & ~A` | `(~A \| B \| C) & ~(A&B) → (C & ~B) \| ~A` | 2172 |
| CX8 | `(~A & B & C) \| ~(A\|C) → (B \| ~C) & ~A` | `(~A \| B \| C) & ~(A&C) → (B & ~C) \| ~A` | 2180 |

> **CX5's missing dual is a documented soundness gap, not an oversight.** The
> source comment (line 2124) records that
> `(~(A&B) | C) & ~(C & (A^B)) → (A^B^C) | ~(A|C)` is **invalid** because "the
> result is more undefined than a source". A good regression test for anyone
> mechanising these.

## 11a.6 `reassociateForUses` (line 2149) — **[canon]**

```
(X op Y) op Z  →  (Y op Z) op X      if X has >1 use
(X op Y) op Z  →  (X op Z) op Y      if Y has >1 use
```

Requires `1u` on the inner binop and on `Z`, and none of `X`, `Y`, `Z` a
constant. Purpose: gather the one-use values into a single instruction so that
one-use-restricted folds become applicable. Pure profitability.

## 11a.7 `canonicalizeLogicFirst` (line 2182) — **[canon]**

```
(X + C2) op C   →   (X op C) + C2      for op ∈ {and, or, xor}
```

* `1u` on the add.
* Let `LastOneMath = N - countr_zero(C2)` — the highest bit position the add
  can affect (counting from the top).
* **`and`:** require `countl_one(C) >= LastOneMath`.
* **`or`/`xor`:** require `countl_zero(C) >= LastOneMath`.

That is, the logic op must only touch bits *below* everything the add can
carry into, so the two commute. Flags are copied from the original add.

## 11a.8 `foldBinOpOfDisplacedShifts` (line 2220) — also used by `add`

```
binop (shift C1, ShAmt), (shift C2, (ShAmt + AddC))
      →  shift (binop C1, (shift C2, AddC)), ShAmt
```

* Both shifts must be the **same opcode**; for `add` only `shl` is allowed.
* `AddC` must be a valid shift amount (`<u bitwidth`).
* Both operands must be real `Instruction`s (no constant expressions).
* The inner `add` may be an `or disjoint` (`m_AddLike`).

## 11a.9 `foldBitwiseLogicWithIntrinsics` (line 2274)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| I1 | `op fshl(A,B,S), fshl(C,D,S) → fshl(op(A,C), op(B,D), S)` | same intrinsic, same shift amount operand; `1u` on both | 2296 |
| I2 | `op fshr(A,B,S), fshr(C,D,S) → fshr(op(A,C), op(B,D), S)` | same | 2296 |
| I3 | `op bswap(A), bswap(B) → bswap(op(A,B))` | `1u` on both | 2308 |
| I4 | `op bswap(A), C → bswap(op(A, byteswap(C)))` | `1u` on the intrinsic | 2308 |
| I5 | `op bitreverse(A), bitreverse(B) → bitreverse(op(A,B))` | `1u` on both | 2308 |
| I6 | `op bitreverse(A), C → bitreverse(op(A, reversebits(C)))` | `1u` | 2308 |

## 11a.10 `simplifyAndOrWithOpReplaced` (line 2325)

Not a rule but a substitution engine used by `visitAnd`/`visitOr`:

> In `X | Y`, try replacing `Y` with `0` inside `X`; in `X & Y`, try replacing
> `Y` with `-1` inside `X`.

It recurses only through bitwise operations, and in `SimplifyOnly` mode builds
nothing. This is the "short-circuit" reasoning: if the result of `X | Y`
depends on `X` only when `Y` is `0`, substituting `0` for `Y` in `X` is sound.

## 11a.11 `reassociateBooleanAndOr` (line 2366)

Reassociates `i1` and/or chains so that a pair of comparisons that
`foldBooleanAndOr` can combine ends up adjacent. Purely enabling; see 11c.

## 11a.12 `canonicalizeConditionalNegationViaMathToSelect` (line 1637) — `xor` only

```
(X + sext(Cond)) ^ sext(Cond)   →   Cond ? -X : X
```

Requires `Cond` to be `i1`, and `1u` on one operand (`xor` is not treated as
commutative here because complexity ordering has already fixed the order).

## 11a.13 `reassociateFCmps` (line 1655)

```
and (fcmp ord X, 0), (and (fcmp ord Y, 0), Z)  →  and (fcmp ord X, Y), Z
or  (fcmp uno X, 0), (or  (fcmp uno Y, 0), Z)  →  or  (fcmp uno X, Y), Z
```

4 commuted variants. `X` and `Y` must have the same type. **FMF on the new
`fcmp` is the intersection** of the two source `fcmp`s (`FMFSource::intersect`).

`fcmp ord X, 0.0` means "X is not NaN"; two such checks combine into one
two-operand `ord`. The dual holds for `uno`.

