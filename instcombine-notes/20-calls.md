# `InstCombineCalls.cpp` — Part 18: intrinsics and calls

Back to [index](README.md). `visitCallInst`, line 1684; `visitCallBase`,
line 4101.

## 18.0 Structure

`visitCallInst` is a ~2200-line `switch` over `Intrinsic::ID` — 109 cases.
Its rules are *semantic identities of the intrinsics*, not IR algebra, so
each group needs its intrinsic's specification to verify.

Generic machinery applied before the switch (lines 1684–1780):
* `simplifyCall`/`simplifyIntrinsic`.
* Memory intrinsics (`memcpy`, `memmove`, `memset`) → loads/stores or
  removal: `SimplifyAnyMemTransfer` (line 116), `SimplifyAnyMemSet` (line 218).
* `canonicalizeConstantArg0ToArg1` (line 829) — **[canon]** for commutative
  intrinsics.
* `foldShuffledIntrinsicOperands` (line 1402) —
  `intrinsic (shuffle X, M), (shuffle Y, M) → shuffle (intrinsic X, Y), M`.
* `foldReversedIntrinsicOperands` (line 1461) — the same for `vector.reverse`.
* `foldIntrinsicWithOverflowCommon` (line 851) — shared logic for the
  `*_with_overflow` family.

---

## 18.1 `abs` (line 1828)

| Rule | Conditions |
|---|---|
| `abs(-X) → abs(X)` | |
| `abs(A * abs(B)) → abs(A * B)` | |
| `abs(X) → X` | `getKnownSignOrZero(X)` says non-negative |
| `abs(X) → -X` | known negative |
| `abs(sext X) → zext (abs X)` | |
| `abs(X %s 2) → X & 1` | |

## 18.2 `umin`/`umax`/`smin`/`smax` (lines 1881–2130)

| Rule | Conditions |
|---|---|
| `umin(cttz(X), C) → cttz(X \| (1 << C))` | |
| `umin(ctlz(X), C) → ctlz(X \| (SignedMin >>u C))` | |
| `smax(smin(X, MinC), MaxC) → smin(smax(X, MaxC), MinC)` | `MinC >=s MaxC` — **[canon]** clamp ordering |
| `umin(i1 X, i1 Y) → X & Y`; `smax(i1 X, Y) → X & Y` | `i1` type |
| `umax(i1 X, i1 Y) → X \| Y`; `smin(i1 X, Y) → X \| Y` | |
| `smin(smax(X, -1), 1) → scmp(X, 0)` | |
| `smax(-nsw X, -nsw Y) → -nsw smin(X, Y)` | both negations `nsw` |
| `max(~A, Y) → ~min(A, ~Y)` | `~Y` free; four variants incl. constants and nested min/max |
| `minmax(X & NegPow2C, Y & NegPow2C) → minmax(X, Y) & NegPow2C` | same mask on both |
| `smax(X, -X) → abs(X)`, `umin(X, -X) → abs(X)`, and the two negated duals | |
| `moveAddAfterMinMax` (line 1141) | `min(X+C, Y+C) → min(X,Y)+C` with matching no-wrap |
| `matchSAddSubSat` (line 1178) | a min/max pair implementing signed saturation → `sadd.sat`/`ssub.sat` |
| `foldClampRangeOfTwo` (line 1240) | nested clamps |
| `reassociateMinMaxWithConstants` (line 1280) | pull constants together |
| `factorizeMinMaxTree` (line 1342) | a tree of min/max with a shared operand |

## 18.3 Bit-counting and bit-order

### `cttz`/`ctlz` — `foldCttzCtlz` (line 479)

| Rule | Conditions |
|---|---|
| `cttz(bitreverse X) → ctlz(X)` and vice versa | |
| `cttz(i1 X, false) → ~X`; `cttz(i1 X, true) → 0` | `i1` result |
| set `is_zero_poison = true` | `1u` and the only user is a shift by this value (a shift by ≥ bitwidth is poison anyway). **`dropUBImplyingAttrsAndMetadata` first** |
| `cttz(-X) → cttz(X)`; `cttz(X & -X) → cttz(X)`; `cttz(abs X) → cttz(X)` | |
| `cttz(sext X) → cttz(zext X)` | `1u` |
| `cttz(zext X, true) → zext(cttz(X, true))` | `1u` |
| `cttz(C << X, true) → cttz(C) + X` | |
| `cttz((C >>uexact X), true) → cttz(C) - X` | |
| `cttz((-1 >>u X) + 1) → N - X` | |
| `ctlz(C >>u X, true) → ctlz(C) + X` | |
| `ctlz(C <<nuw X, true) → ctlz(C) - X` | |
| `cttz(V) → log2(V)`; `ctlz(V) → (N-1) - log2(V)` | `tryGetLog2` succeeds (see [§7.6](06-idiv.md)); the `sub` is `nsw`+`nuw` |
| fold to a constant | known bits give `PossibleZeros == DefiniteZeros` |
| set `is_zero_poison` | `isKnownNonZero(X)` |
| add a **range return attribute** | derived from known bits, when none is present |

### `ctpop` — `foldCtpop` (line 643)

Similar: known-bits resolution, `ctpop(bitreverse/bswap X) → ctpop(X)`,
`ctpop(~X)` shapes, and a range attribute.

### `bswap` / `bitreverse` (lines 2180–2234)

| Rule | Conditions |
|---|---|
| `bitreverse(zext i1 X) → X ? SignBit : 0` | |
| `bswap(X << Y) → bswap(X) >>u Y` and the dual | `Y` a multiple of 8 |
| `bswap(X) → shift X` | `X` has exactly one "active byte" |
| `bswap(trunc(bswap X)) → trunc(X >>u C)` | |
| `foldBitOrderCrossLogicOp` (line 1500) | `bswap(A) op bswap(B) → bswap(A op B)`, shared with [11a.9](09-andorxor-shared.md) |

## 18.4 Funnel shifts (line 2306)

| Rule | Conditions |
|---|---|
| `fshr X, Y, C → fshl X, Y, (N - C)` | `C != 0` — **[canon]** |
| `fshl(X, 0, C) → X << C`; `fshl(X, undef, C) → X << C` | |
| `fshl(0, X, C) → X >>u (N - C)` | |
| `fshl i16 X, X, 8 → bswap i16 X` | the specific rotate that is a byte swap |
| `fshl(X, X, -Y) → fshr(X, X, Y)` | rotates only |
| `fshl(X, 0, Y) → X << (Y & (N-1))` | **bitwidth must be a power of two**, so the mask is exact |

## 18.5 Overflow and saturating intrinsics (lines 2450–2600)

| Rule | Conditions |
|---|---|
| `uaddo(X +nuw C0, C1) → uaddo(X, C0+C1)` | the constant add must not overflow |
| `saddo(X +nsw C0, C1) → saddo(X, C0+C1)` | |
| `ssubo(X, C) → saddo(X, -C)` | `C != INT_MIN` — **[canon]** |
| `usub_sat(C -nuw A, C1) → usub_sat(C - C1, A)` | `C1 <u C`; otherwise `0` |
| `ssub_sat(X, C) → sadd_sat(X, -C)` | `C != INT_MIN` — **[canon]** |
| `sat(sat(X + V2) + V) → sat(X + (V + V2))` | the combined constant must not overflow |
| `createOverflowTuple` (line 842) | when only one half of the result tuple is used, rebuild the other from a plain op |

## 18.6 FP intrinsics

### `minnum`/`maxnum`/`minimum`/`maximum` (line 2599)

| Rule | Conditions |
|---|---|
| `min(-X, -Y) → -(max(X, Y))` | the intrinsic ID flips; both operands negated |
| `m(m(X, C2), C1) → m(X, C)` | constants folded per intrinsic |
| `m(fpext X, fpext Y) → fpext(m(X, Y))` | same source type |
| `max(X, -X) → fabs(X)`; `min(X, -X) → -fabs(X)` | |

### `fma`/`fmuladd` (line 2757)

| Rule | Conditions |
|---|---|
| `fma(-x, -y, z) → fma(x, y, z)` | |
| `fma(fabs x, fabs x, z) → fma(x, x, z)` | **the same value twice** |
| `fma(x, y, 0.0) → x * y` | requires the right FMF for the zero |
| `fma(x, -1.0, y) → y - x` | |

### `copysign` (line 2806)

| Rule | Conditions |
|---|---|
| `copysign(Mag, -Sign) → -fabs(Mag)` | the sign argument is known negative |
| `copysign(Mag, +Sign) → fabs(Mag)` | known non-negative |
| `copysign(Mag, copysign(?, X)) → copysign(Mag, X)` | |
| `copysign(-MagC, X) → copysign(MagC, X)` | — **[canon]** |
| `copysign(fabs X, S) → copysign(X, S)`; same for `fneg` | |

### `fabs` (line 2850)

`fabs(-X) → fabs(X)`; `fabs(select C, TC, FC) → select C, |TC|, |FC|`;
`fabs(select C, -F, F) → fabs(F)`; `fabs(copysign x, y) → fabs(x)`.

### Rounding intrinsics (line 2892)

`ceil floor round roundeven nearbyint rint trunc`: narrow through an `fpext`
(`intrinsic (fpext x) → fpext (intrinsic x)`).

### `sin`/`cos` (line 2907)

`cos(-x) → cos(x)`, `cos(fabs x) → cos(x)`, `cos(copysign x, y) → cos(x)`;
`sin(-x) → -sin(x)`.

### `powi` (line 2267)

`powi(x, -1) → 1/x`; `powi(x, 2) → x*x`; `powi(-x, p) → powi(x, p)` **for even
`p`** (and the `fabs`/`copysign` variants).

### `ldexp` (line 2930)

| Rule | Conditions |
|---|---|
| `ldexp(ldexp(x, a), b) → ldexp(x, a + b)` | the exponent add must not overflow |
| `ldexp(x, zext i1 y) → x * (y ? 2.0 : 1.0)` | |
| `ldexp(x, sext i1 y) → x * (y ? 0.5 : 1.0)` | |
| `ldexp(x, c ? e : 0) → c ? ldexp(x, e) : x` | |

### `is_fpclass` — `foldIntrinsicIsFPClass` (line 961)

Converts a class test back to an `fcmp` when one exists
(`fpclassTestIsFCmp0`, line 903), and resolves it against
`computeKnownFPClass`. **Denormal mode aware** via `inputDenormalIsIEEE` /
`inputDenormalIsDAZ` (lines 890, 895).

## 18.7 Vector reductions (lines 3624–3840)

For each of `and or add xor mul umin umax smin smax fadd fmul fmin fmax`:

* `simplifyReductionOperand` (line 1535) — strip a shuffle that only permutes
  lanes (a reduction is order-insensitive for the integer ops;
  `CanReorderLanes` gates the FP ones).
* Reduce over a `<1 x T>` → the scalar.
* `reduce.op (sext/zext X) → sext/zext (reduce.op X)` where the widths allow.
* `reduce.add (X - Y)`-style rewrites into a narrower reduction.

## 18.8 Memory and object intrinsics

| Intrinsic | Rules |
|---|---|
| `memcpy`/`memmove`/`memset` | `SimplifyAnyMemTransfer`/`SimplifyAnyMemSet`: a small constant length becomes a load+store (or store) of the widest legal integer, with the alignments preserved; `memmove(x, x, n)` is removed; a source of `undef` makes the whole thing dead |
| `masked_load`/`store`/`gather`/`scatter` | all-ones mask → a plain access; all-zeros → removal/passthru; constant-mask narrowing (lines 291–410) |
| `objectsize` | resolved against `lowerObjectSizeCall` |
| `launder`/`strip.invariant.group` | `simplifyInvariantGroupIntrinsic` (line 449): collapse nested calls |
| `lifetime_end` | removed when the object is dead |
| `stackrestore` | removed when it restores the immediately preceding `stacksave` or when nothing allocated in between |
| `ptrmask` | folded into the pointer arithmetic; nested `ptrmask`s merged |
| `assume` | `assume(a && b) → assume(a); assume(b)`; `assume(!(a\|\|b)) → assume(!a); assume(!b)`; `assume((load p) != null)` → add `!nonnull` metadata to the load and drop the assume |
| `experimental_guard` | `guard(a); guard(b) → guard(a & b)`, within `GuardWideningWindow` (default 1) instructions |

## 18.9 `visitCallBase` (line 4101) — all calls

| # | Rule | Side conditions | Line |
|---|---|---|---|
| C1 | `annotateAnyAllocSite` (line 4053) | add `noalias`, `dereferenceable`, alignment attributes derived from a known allocation function | 4102 |
| C2 | strip known-non-null wrappers from pointer arguments | the parameter has `nonnull`, or `dereferenceable` and null is invalid | 4110 |
| C3 | add `nonnull` to arguments proven non-zero | `isKnownNonZero` | 4118 |
| C4 | `transformConstExprCastCall` (line 4374) | a call through a bitcast of a function: rewrite to a direct call when the signatures are ABI-compatible | 4135 |
| C5 | drop `convergent` | the callee is not convergent and not an intrinsic | 4140 |
| C6 | remove a call with a mismatched calling convention | only when the callee is a definition | 4147 |
| C7 | `transformCallThroughTrampoline` (line 4628) | a call through `adjust.trampoline` → a direct call with the nest argument | — |
| C8 | `tryOptimizeCall` (line 3952) | run `LibCallSimplifier` | — |

