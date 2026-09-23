# `InstCombineLoadStoreAlloca.cpp` — Part 17: `alloca`, `load`, `store`

Back to [index](README.md).

## 17.0 Memory-specific preconditions

Unlike the arithmetic files, nearly every rule here is gated on **memory
ordering and volatility**, not on value properties:

| Guard | Meaning |
|---|---|
| `isVolatile()` | the access is observable; almost nothing may change |
| `isUnordered()` | not `volatile` and ordering is `NotAtomic` or `Unordered` — the usual precondition for moving or eliminating an access |
| `isSimple()` | `isUnordered()` **and** not atomic at all |
| `isSupportedAtomicType(Ty)` (line 564) | `int`, pointer or FP — the only types an atomic access may be retyped to |
| `NullPointerIsDefined(F, AS)` | whether a null pointer access is UB in this address space |

A second recurring idea: **UB-implies-unreachable**. Several rules, on seeing
an access that must be UB, insert an `unreachable` and poison the result
rather than trying to fold (`CreateNonTerminatorUnreachable`).

---

## 17.1 `visitAllocaInst` (line 476)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| L1 | `simplifyAllocaArraySize` (line 185) | constant array size → a non-array alloca of an array type; also removes a zero-size allocation | 477 |
| L2 | `alloca [0 x T], N → alloca [0 x T], 1` | the allocated type has zero size | 481 |
| L3 | move a zero-sized `alloca` to the entry block, or CSE it with an existing zero-sized entry-block alloca | the alignment of the survivor becomes the **max** of the two | 486 |
| L4 | replace the `alloca` with the global it is memcpy'd from | `isOnlyCopiedFromConstantMemory`: the only writes to the alloca are a single `memcpy` from constant memory. Needs `SourceAlign >= AllocaAlign`, `isDereferenceableForAllocaSize`, and the source not to be an `Instruction`. Address-space mismatch is handled by `PointerReplacer` (line 269), which rewrites every user | 501 |
| L5 | `visitAllocSite` | shared with `malloc`-like calls: delete an allocation with no "real" users | 545 |

`MaxCopiedFromConstantUsers` (default 300) caps L4's user walk.

## 17.2 `visitLoadInst` (line 1061)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| D1 | `combineLoadToOperationType` (line 663): `bitcast (load T, P) → load U, P` | the load must be **unordered**, have uses, not be a swift-error pointer, and have `1u` whose user is a **no-op cast**. The pointer-ness of the two types must agree, and an atomic load may only be retyped to an `isSupportedAtomicType` | 1067 |
| D2 | `replaceGEPIdxWithZero` (line 973) | an index that must be zero for the access to be in bounds is replaced by zero (`canReplaceGEPIdxWithZero`, line 898, which uses `isObjectSizeLessThanOrEq`) | 1070 |
| D3 | `unpackLoadToAggregate` (line 708) | a `load` of a struct/array with one element, or of a struct all of whose fields are loaded separately, is split into scalar loads. Requires `isSimple()` | 1074 |
| D4 | load CSE | `FindAvailableLoadedValue` finds a dominating load or store of the same location; metadata is merged (`combineMetadataForCSE`) | 1079 |
| D5 | **bail out** if not `isUnordered()` | | 1088 |
| D6 | a load that must be UB → `unreachable` + `poison` | `canSimplifyNullLoadOrGEP` (line 1000): loading from a null pointer where null is not a valid address | 1092 |
| D7 | `load (select C, P, Q) → select C, (load P), (load Q)` | `1u` on the select; **both** pointers must satisfy `isSafeToLoadUnconditionally`. The new loads inherit alignment, atomic ordering and sync scope, and copy only `PoisonGeneratingIDs` metadata | 1098 |
| D8 | strip a known-non-null wrapper from the pointer | `simplifyNonNullOperand` (line 1014); requires null to be invalid in this address space | 1126 |

## 17.3 `visitStoreInst` (line 1392)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| T1 | `combineStoreToValueType` (line 1223): `store (bitcast V), P → store V, P'` | the stored value is a no-op cast; same atomic-type restriction as D1 | 1396 |
| T2 | `unpackStoreToAggregate` (line 1261) | the dual of D3 | 1400 |
| T3 | `replaceGEPIdxWithZero` | as D2 | 1404 |
| T4 | **bail out** if not `isUnordered()` | | 1408 |
| T5 | delete a store to a `1u` `alloca` | the alloca has no other user, so the value is never read | 1412 |
| T6 | delete a store through a `1u` GEP off a `1u` `alloca` | same reasoning | 1416 |
| T7 | delete a store to constant memory | `!isModSet(AA->getModRefInfoMask(Ptr))` | 1425 |
| T8 | **dead store elimination**: delete a preceding store to the same address | scans back up to **6 instructions**; both stores unordered, `equivalentAddressValues` (line 1371), same value type. Stops at any instruction that may read, write or throw | 1429 |
| T9 | `store (load P), P → nothing` | the loaded value is being stored straight back to the same address | 1449 |
| T10 | `store V, null → store poison, null` | `canSimplifyNullStoreOrGEP` (line 989) — the store is UB, so the value becomes poison and later DCE removes it | 1460 |
| T11 | `store V, undef` → mark the rest of the block unreachable | `removeInstructionsBeforeUnreachable` and `handleUnreachableFrom` | 1466 |
| T12 | `store undef, P → nothing` | | 1476 |
| T13 | strip a known-non-null wrapper from the pointer | as D8 | 1480 |

## 17.4 `mergeStoreIntoSuccessor` (line 1521)

Not called from `visitStoreInst` but from the driver
(`InstructionCombining.cpp`). If a block ends with a store and its successor
has exactly two predecessors and begins with a store to the *same* address,
the two stores are merged into one in the successor with a PHI of the values —
the classic "sink the store out of the if".

Preconditions: both stores unordered (the comment notes the volatile/ordered
case "has not been audited"), matching address, and the store must be the
last non-terminator instruction in its block.

