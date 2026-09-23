# Parts 15 & 19: `InstCombinePHI.cpp` and `InstCombineAtomicRMW.cpp`

Back to [index](README.md).

---

# 15. `phi` (`visitPHINode`, line 1439)

Almost nothing here is a peephole in the algebraic sense. The theme is
**hoisting an operation out of a PHI**: if every incoming value is the same
operation, create a PHI of the operands and apply the operation once.

## 15.1 The "sink the op into the PHI" family

`foldPHIArgOpIntoPHI` (line 886) is the entry point, dispatching on the opcode
of the first incoming value. Global preconditions:

* Every incoming value must be an instruction that `isSameOperationAs` the
  first and has **exactly one user**.
* The PHI's block terminator must not be an EH pad.
* Debug locations of all the merged instructions are unioned
  (`PHIArgMergedDebugLoc`, line 43).

| # | Incoming shape | Result | Extra conditions | Line |
|---|---|---|---|---|
| P1 | `cast` | `cast (phi …)` | all casts from the same source type; for integer→integer, `shouldChangeType` | 903 |
| P2 | `binop X, C` / `cmp X, C` | `binop (phi …), C` | the **same** constant `C` in every arm. The new binop's IR flags are the **intersection** (`copyIRFlags` then `andIRFlags`) | 911 |
| P3 | `binop X, Y` (no constant) | `foldPHIArgBinOpIntoPHI` (line 439): two new PHIs, one per operand | at most one operand may vary per arm | 913 |
| P4 | `getelementptr` | `foldPHIArgGEPIntoPHI` (line 534) | all GEPs must have the same source element type and index structure; only one index may vary | 891 |
| P5 | `load` | `foldPHIArgLoadIntoPHI` (line 697) | `isSafeAndProfitableToSinkLoad` (line 653): every load must be non-volatile, have the same alignment and address space, and no intervening may-write instruction in its block. **All loads must agree on `atomic`ness** | 893 |
| P6 | `insertvalue` | `foldPHIArgInsertValueInstructionIntoPHI` (line 363) | identical index lists | 895 |
| P7 | `extractvalue` | `foldPHIArgExtractValueInstructionIntoPHI` (line 403) | identical index lists | 897 |
| P8 | `zext` | `foldPHIArgZextsIntoPHI` (line 805) | widens the PHI itself; refuses when it would create an illegal type from legal ones | 1443 |
| P9 | `inttoptr` | `foldPHIArgIntToPtrToPHI` (line 339) | | 1446 |

> **P2's flag intersection is the interesting bit for a port.** Hoisting `add
> nsw` out of a PHI is only sound if *every* arm had `nsw`; otherwise the
> hoisted operation could be poison on a path where the original was defined.
> The same logic applies to every flag-carrying case.

## 15.2 Value-level folds

| # | Rule | Side conditions | Line |
|---|---|---|---|
| P10 | `phi (bitcast P), (bitcast Q) … → bitcast (phi …)` | pointer type; all incoming values strip to the same pointer | 1455 |
| P11 | `foldDeadPhiWeb` (line 59) | a set of PHIs that only feed each other (and nothing else) is dead → replaced with `poison` | 1472 |
| P12 | `foldIntegerTypedPHI` (line 134) | an integer PHI that is really a pointer PHI in disguise (`ptrtoint`/`inttoptr` round trips) | 1477 |
| P13 | a PHI whose only user is a `1u` binop/unop/GEP that feeds back into the PHI → `poison` | *a self-referential cycle with no external value* | 1479 |
| P14 | replace incoming values with a **shared nonzero constant** | the PHI has ≤ 2 uses, every use is an equality compare against zero (possibly through a `1u` `or`), and the incoming value is `isKnownNonZero` **in its own predecessor's context**. Any intervening `or` has its poison-generating flags dropped | 1488 |
| P15 | `PHIsEqualValue` (line 1002) | a web of PHIs all reaching the same non-PHI value → replace with that value | 1525 |
| P16 | canonicalise incoming-block order across PHIs in the same block | `PredOrder` cache — **[canon]**, makes P17 fire | 1547 |
| P17 | PHI CSE | an identical PHI in the same block (`isIdenticalToWhenDefined`) | 1565 |
| P18 | `SliceUpIllegalIntegerPHI` (line 1101) | an integer PHI of an illegal width, all of whose uses are `trunc`/`lshr`+`trunc` extractions, is split into several legal-width PHIs | 1574 |
| P19 | `simplifyUsingControlFlow` (line 1286) | a PHI of `true`/`false` whose predecessors are determined by a branch on a condition → that condition (or its negation) | 1578 |
| P20 | `foldDependentIVs` (line 1389) | two induction variables stepping in lockstep → express one in terms of the other | 1581 |

`MaxNumPhis` (default 512, `-instcombine-max-num-phis`) caps the work in
`SliceUpIllegalIntegerPHI`.

---

# 19. `atomicrmw` (`visitAtomicRMWInst`, line 95)

Only three rules, but they are cleanly stated.

**Precondition:** the `atomicrmw` must **not be `volatile`**. A volatile RMW
performs an observable load *and* store, so it cannot be reduced even when the
value is known — the source notes this is "general paranoia about user
expectations".

| # | Rule | Condition | Line |
|---|---|---|---|
| R1 | any op → `xchg` | `isSaturating(RMWI)`: the operation always writes a value equal to its value operand | 103 |
| R2 | any idempotent integer op → `or ptr, 0` | `isIdempotentRMW(RMWI)` — **[canon]** | 117 |
| R3 | any idempotent FP op → `fadd ptr, -0.0` | same — **[canon]** | 121 |

### `isSaturating` (line 59)

| Op | Value operand |
|---|---|
| `xchg` | any |
| `or` | `-1` |
| `and` | `0` |
| `min`/`max` | `INT_MIN`/`INT_MAX` |
| `umin`/`umax` | `0`/`UINT_MAX` |
| `fmax` | `+Inf` |
| `fmin` | `-Inf` |
| `fadd`, `fsub` | NaN |

### `isIdempotentRMW` (line 24)

| Op | Value operand |
|---|---|
| `add`, `sub`, `or`, `xor` | `0` |
| `and` | `-1` |
| `min`/`max` | `INT_MAX`/`INT_MIN` |
| `umin`/`umax` | `UINT_MAX`/`0` |
| `fadd` | **`-0.0`** |
| `fsub` | **`+0.0`** |

> The FP asymmetry is the whole point: `x + (+0.0)` is **not** idempotent
> because `(-0.0) + (+0.0) = +0.0`. Only `-0.0` is the additive identity that
> preserves the sign of zero. Symmetrically for `fsub`.
>
> The canonical forms (`or 0` and `fadd -0.0`) are described in the source as
> arbitrary; the value is having *one* form for later matching.

