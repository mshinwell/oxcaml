# `InstCombineSimplifyDemanded.cpp` — Part 20: demanded-bits / -elements / -FP-class

Back to [index](README.md).

This file is not a rule list at all — it is a **backward dataflow analysis
fused with rewriting**. It is the single most important thing to understand
before porting the rest of the pass, because dozens of rules elsewhere exist
only because this machinery has already normalised their inputs.

## 20.0 The idea

> Given an instruction `I` and a mask saying which bits (or vector elements,
> or FP classes) of `I`'s *result* are actually used downstream, rewrite `I`'s
> operands to anything that agrees on those bits, and return a simpler
> replacement for `I` if one exists.

Three parallel instantiations:

| Entry point | Lattice | Line |
|---|---|---|
| `SimplifyDemandedBits` | `APInt DemandedMask` + `KnownBits` | 95 |
| `SimplifyDemandedVectorElts` | `APInt DemandedElts` + `APInt PoisonElts` | 1397 |
| `SimplifyDemandedFPClass` | `FPClassTest DemandedMask` + `KnownFPClass` | 2076 |

All three are driven from the visitors: `SimplifyDemandedInstructionBits`
(line 74) demands *all* bits of an instruction and is called from `visitAnd`,
`visitOr`, `visitXor`, `commonShiftTransforms`, `visitTrunc`,
`commonIDivTransforms`, `commonIRemTransforms`; the vector version from the
three vector visitors.

## 20.1 The bit version

### Three exits from `SimplifyDemandedBits` (line 95)

1. **Nothing demanded** → replace the *use* with `undef` (line 108). Note it
   is the use, not the value; other uses keep their meaning.
2. **One use** → `SimplifyDemandedUseBits` (line 164), which may *mutate*
   the instruction.
3. **Multiple uses** → `SimplifyMultipleUseDemandedBits` (line 1146), which
   may only *return a replacement*, never mutate — the other users may demand
   different bits.

Depth-limited by `MaxAnalysisRecursionDepth`.

### Two recurring rewrites

* **`ShrinkDemandedConstant`** (line 42) — clear bits of a constant operand
  that are not demanded. This is why so many later folds can assume their
  constants are "tight".
* **`disableWrapFlagsBasedOnUnusedHighBits`** (line 181) — **critical for
  soundness**: if any high bit of an `add`/`sub`/`mul` is not demanded and the
  operands were simplified, `nsw` and `nuw` must be **dropped**, because the
  simplification may have introduced a wrap that the original could not have.

### Per-opcode summary (`SimplifyDemandedUseBits`, line 164)

| Opcode | What it does |
|---|---|
| `and` | LHS only needs the bits the RHS does not force to zero; if all demanded bits are known on one side, return the other operand |
| `or` | dual; **`disjoint` is dropped** if an operand changed |
| `xor` | if the demanded bits of one side are all known zero, return the other; recognises `~(~X)` cancellation and rewrites `xor` into `and`/`or`/`not` when the known bits allow |
| `select` | recurse into both arms with the same mask; intersect the results |
| `trunc` | demand only the low bits; **drops `nuw`/`nsw`** if the source changed |
| `zext` | demand the low bits of the source |
| `sext` | demand the low bits plus the sign bit; converts to `zext` when the sign bit is not demanded |
| `add`, `sub` | demand only up to the highest demanded bit (`simplifyOperandsBasedOnUnusedHighBits`); drop wrap flags |
| `mul` | same, plus trailing-zero reasoning |
| `shl` | demand the bits that will survive the shift; can narrow to a smaller shift or turn into an `and` |
| `lshr`, `ashr` | dual; `ashr` becomes `lshr` when the sign bits are not demanded; `simplifyShrShlDemandedBits` (line 1322) handles `shr`+`shl` pairs |
| `udiv` | high-bit reasoning only |
| `srem` | converts to `and` for power-of-two divisors when only low bits are demanded |
| `abs`, `ctpop`, `bswap`, `ptrmask`, `fshl`/`fshr`, `umax`, `umin` | intrinsic-specific demanded-bit rules; `bswap` reverses the mask, `fsh*` rotates it, `ptrmask` intersects it with the mask argument |

## 20.2 The vector-elements version (line 1397)

`DemandedElts` says which lanes are used; `PoisonElts` is an **output** saying
which lanes the analysis has determined to be poison.

Key behaviours:

* Scalable vectors are **not analysable** (the element count is not a
  compile-time constant) — immediate bail-out.
* No lanes demanded → the whole value becomes `poison`.
* A constant vector has its undemanded lanes replaced with `poison`.
* `AllowMultipleUsers` lets a caller (e.g. `visitExtractElementInst`) run the
  analysis over a multi-use value, replacing it wholesale afterwards.

| Opcode | What it does |
|---|---|
| `getelementptr` | demand the same lanes of every vector operand |
| `insertelement` | if the inserted lane is not demanded, drop the insert; otherwise recurse into the base with that lane cleared |
| `shufflevector` | map the demanded lanes through the mask onto each source; undemanded mask elements become `-1` (poison) |
| `select` | demand the same lanes of both arms and of the condition; a constant condition lane lets one arm's lane be dropped |
| `bitcast` | rescale the demanded mask between differing element counts (only when one divides the other) |
| `fptrunc`, `fpext` | pass the mask through unchanged |
| `masked_load`, `masked_gather` | intersect with the mask operand |
| default | recurse into all operands of a `1u` elementwise instruction |

Depth is capped by `-instcombine-simplify-vector-elts-depth` (default 10).

## 20.3 The FP-class version (line 1968)

`DemandedMask` is an `FPClassTest` bitset (`fcNan`, `fcInf`, `fcNormal`,
`fcSubnormal`, `fcZero`, each split by sign). Used to remove operations whose
only effect is on classes nobody observes — for instance dropping an `fabs`
when the consumer only tests for NaN, or simplifying a `copysign` when the
sign is not demanded. `getFPClassConstant` (line 1945) materialises a constant
when the demanded set has a single inhabitant.

## 20.4 Porting notes

* This analysis is **why many peephole rules in the other files have no
  explicit "the high bits are unused" condition** — they can assume the
  constants are already minimal and the extraneous operations already gone.
  A port that omits it will need those conditions written out, or will simply
  miss the optimisations.
* The mutate-vs-replace split (one use vs. many) is the pattern to copy: it is
  what makes a backward analysis safe in a DAG.
* `-instcombine-verify-known-bits` cross-checks `computeKnownBits` against
  what this pass derives. If you port both, build the same check — the two
  are easy to let drift apart, and a disagreement is a miscompile waiting to
  happen.

