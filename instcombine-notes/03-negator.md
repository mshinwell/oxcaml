# `InstCombineNegator.cpp` — sinking negation

Back to [index](README.md).

Not a peephole list but a **recursive, speculative, all-or-nothing rewriter**.
Called from `visitSub` (line 2315) and from `Negator::Negate`. It answers:

> given `-V`, can I produce an equivalent expression **without increasing the
> instruction count**?

If yes, the caller replaces `sub Op0, Op1` with `add Op0, negate(Op1)`.

## 4.1 The framework

```
Negator::Negate(LHSIsZero, IsNSW, Root, IC)
  → Negator::run(Root, IsNSW)
      → negate(V, IsNSW, Depth)          [memoised in NegationsCache]
          → visitImpl(V, IsNSW, Depth)   [the rule table]
```

Four properties matter for porting:

* **Speculative construction.** New instructions are built into a side list
  (`NewInstructions`) via a callback inserter. On failure they are *erased*
  (`run`, line 553) and nothing is inserted. Only on success are they spliced
  into the function, in def-use order.
* **Memoisation with cycle detection.** `NegationsCache` maps value → negated
  value. In debug builds a placeholder detects cycles.
* **Depth limit.** `NegatorMaxDepth` (default `NegatorDefaultMaxDepth`),
  overridable by `-instcombine-negator-max-depth`. Exceeding it aborts.
* **`IsTrulyNegation`.** True when the caller really had `0 - X` (as opposed to
  `A - X`). This is a *profitability* distinction: with a true negation the old
  `sub` disappears anyway, so rules may fire even on multi-use values and may
  afford to leave one operand un-negated.

**Key invariant:** `visitImpl` bails out immediately if
`!V->hasOneUse() && !IsTrulyNegation` (line 148). Every rule below is therefore
implicitly one-use-guarded in the non-true-negation case.

## 4.2 Rules requiring no recursion

| # | `-V` where `V` = | Result | Side conditions | Line |
|---|---|---|---|---|
| G1 | `undef` | `undef` | — | 124 |
| G2 | any `i1` value | the value itself | negation is identity in `i1` | 128 |
| G3 | `-X` | `X` | — | 134 |
| G4 | integral constant | folded negation | built with `HasNSW=false` | 138 |
| G5 | `X + 1` **[sorted]** | `~X` | `inc` is always negatible | 164 |
| G6 | `~X` | `X + 1` | `not` is always negatible | 172 |
| G7 | `X a>> (N-1)` | `X l>> (N-1)` | sign-bit smear; IR flags copied | 179 |
| G8 | `X l>> (N-1)` | `X a>> (N-1)` | as above | 179 |
| G9 | `sext(i1 X)` | `zext(i1 X)` | operand must be `i1` | 198 |
| G10 | `zext(i1 X)` | `sext(i1 X)` | operand must be `i1` | 198 |
| G11 | `Cond ? C1 : C2` | `Cond ? -C1 : -C2` | **both** arms `m_ImmConstant`; not use-limited, since no recursion | 207 |
| G12 | `ucmp/scmp(A, B)` | `ucmp/scmp(B, A)` | `1u` on the intrinsic | 220 |
| G13 | `A - B` | `B - A` | `1u` on the sub **or** `A` is an `m_ImmConstant`; output `nsw` iff `IsNSW && sub.nsw` | 227 |

> **G7/G8 note.** `-(X >>s 31) == X >>u 31` for `i32`: the arithmetic shift
> gives `0` or `-1`; negating gives `0` or `1`, which is exactly the logical
> shift. Copying IR flags here is fine because both are `exact`-capable and
> the `exact` condition (no nonzero bit shifted out) is the same predicate.

> **G13's asymmetry.** `nuw` is explicitly **not** propagated
> (`HasNUW=false`): `A -nuw B` means `A >= B`, which says nothing about
> `B - A`.

## 4.3 Rules requiring `V->hasOneUse()` (line 241)

| # | `-V` where `V` = | Result | Side conditions | Line |
|---|---|---|---|---|
| G14 | `zext(X l>> (SrcW-1))` | `sext(X a>> (SrcW-1))` | **`IsTrulyNegation`** only | 245 |
| G15 | `(trunc?(X l>> C)) & 1` | `trunc?((X << (N-1-C)) a>> (N-1))` | `1u` on the inner shift; `C` an `m_ImmConstant` | 258 |
| G16 | `X /s C` | `X /s (-C)` | `C` has no undef/poison element, `C != INT_MIN`, `C != 1`; `exact` preserved | 272 |

> **G16's conditions are all necessary:** `-C` must exist (`C != INT_MIN`),
> and `C == 1` is excluded only as a profitability guard — `-(X/1)` is better
> handled as `-X` elsewhere. The `containsUndefOrPoisonElement` check is a
> vector-lane concern.

## 4.4 Recursive rules (depth-limited)

Structural cases — negation is pushed through and succeeds iff every recursive
call succeeds:

| # | `V` = | Requirement | Line |
|---|---|---|---|
| G17 | `freeze X` | `X` negatible | 297 |
| G18 | `phi [v1, b1], ...` | **all** incoming negatible, **and** the PHI must not dominate any incoming block (avoids negating induction variables → infinite loop) | 304 |
| G19 | `shufflevector A, B, M` | both `A` and `B` negatible | 358 |
| G20 | `extractelement V, I` | `V` negatible | 369 |
| G21 | `insertelement V, E, I` | both `V` and `E` negatible | 378 |
| G22 | `trunc X` | `X` negatible (recursed with `IsNSW = false`) | 391 |

Algebraic cases:

| # | `V` = | Result | Side conditions | Line |
|---|---|---|---|---|
| G23 | `Cond ? A : B` where `B == -A` | `Cond ? B : A` (swap arms) | `isKnownNegation(A, B, NeedNSW=false, AllowPoison=false)`. **Poison-generating flags are dropped** from the swapped arms. `prof` metadata deliberately *not* swapped | 330 |
| G24 | `Cond ? A : B` | `Cond ? -A : -B` | both arms negatible; metadata preserved | 349 |
| G25 | `X << C` | `(-X) << C` | `X` negatible; `IsNSW &= shl.nsw`; `HasNUW=false` on the result | 398 |
| G26 | `X << C` (fallback) | `X * (-1 << C)` | `C` an `m_ImmConstant` **and `IsTrulyNegation`** | 404 |
| G27 | `A \|disjoint 1` | `~A` | the `or` **must be `disjoint`** | 415 |
| G28 | `A \|disjoint B` | falls through to the `add` case | `disjoint` makes `or` ≡ `add` | 418 |
| G29 | `A + B` | `(-A) + (-B)` | both negatible | 435 |
| G30 | `A + B` | `(-A) - B` | only one negatible, **and `IsTrulyNegation`** | 443 |
| G31 | `A ^ C` | `(A ^ ~C) + 1` | `C` a constant **and `IsTrulyNegation`** | 451 |
| G32 | `A * B` | `(-B) * A` or `A * (-B)` | one operand negatible; tries the *second* operand first (likelier to be a constant). Output `nsw` iff `IsNSW && mul.nsw`; `HasNUW=false` | 462 |

> **G31 is `-(A ^ C) = (A ^ ~C) + 1`.** Proof: `-(x) = ~x + 1`, and
> `~(A ^ C) = A ^ ~C`. It needs `IsTrulyNegation` purely for profitability —
> it creates two instructions where one existed.

> **`exact ashr` is deliberately not negated** (line 190):
> `-(X a>>exact C) == X /s (-1 << C)` holds, but division is judged too
> expensive to be worth it.

## 4.5 The `abs` interaction

`visitSub` refuses to invoke the Negator on a pure negation whose user is
`select(_, Op1, thisNeg)` (line 2310). Without that guard, the Negator would
dissolve the negation and the `abs`/`nabs` recogniser in `visitSelect` would
never fire. This is a **phase-ordering hack**, not a correctness condition, but
a port that reorders these passes will need the equivalent.

