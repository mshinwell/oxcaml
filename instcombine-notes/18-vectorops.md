# `InstCombineVectorOps.cpp` — Part 16: `extractelement`, `insertelement`, `shufflevector`, `insertvalue`

Back to [index](README.md).

## 16.0 What is different about vector folds

Three things distinguish this file from the scalar ones:

* **Poison is per-lane.** An out-of-range shuffle mask element (`-1`,
  `PoisonMaskElem`) yields poison in that lane only. Many folds are about
  proving that a lane is *not demanded* and may therefore be anything —
  this is `SimplifyDemandedVectorElts` (Part 20), which is the vector analogue
  of `SimplifyDemandedBits` and is invoked from all three visitors.
* **Endianness** matters whenever an integer is reinterpreted as a vector or
  vice versa: `foldTruncShuffle`, `foldTruncInsEltPair` and
  `foldBitcastExtElt` all take `DL.isBigEndian()`.
* **Scalable vectors** must be handled or excluded explicitly.
  `visitShuffleVectorInst` bails out at line 2886 for scalable types; the
  extract/insert visitors use `ElementCount::getKnownMinValue()` and guard
  with `isScalable()`.

`getPreferredVectorIndex` (line 390) canonicalises every constant index to
`i64` — **[canon]**, so later matches only need one form.

---

## 16.1 `visitExtractElementInst` (line 398)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| E1 | `extractelement (select C, A, B), I → select C, (ee A, I), (ee B, I)` | scalar (integer) condition; constant index | 404 |
| E2 | canonicalise the index type to `i64` | **[canon]** | 412 |
| E3 | `extractelement (stepvector), I → I` | constant index in range; `poison` if the index doesn't fit the element type | 419 |
| E4 | bail out | non-scalable vector with an out-of-range constant index | 432 |
| E5 | `foldBitcastExtElt` (line 183) | `extractelement (bitcast X), I` → a scalar bitcast/trunc/shift; **endianness-dependent** | 436 |
| E6 | `scalarizePHI` (line 100) | `extractelement (phi …), I` → a scalar PHI of extracts; only when the PHI is a simple recurrence whose other uses are all extracts at the same index | 440 |
| E7 | `extractelement (unop X), I → unop (ee X, I)` | `cheapToScalarize` (line 58): the operand is a constant, a splat, or itself an extract at the same index | 445 |
| E8 | `extractelement (binop X, Y), I → binop (ee X, I), (ee Y, I)` | `cheapToScalarize`, **and** either a known-valid index or `isSafeToSpeculativelyExecuteWithVariableReplaced` (a div by a lane that might be zero must not be scalarised into an always-executed div) | 452 |
| E9 | `extractelement (cmp X, Y), I → cmp (ee X, I), (ee Y, I)` | `cheapToScalarize`; flags copied | 462 |
| E10 | `extractelement (insertelement V, S, J), I → extractelement V, I` | both indices constant and different | 473 |
| E11 | `extractelement (gep …), I → gep (ee …)` | constant in-range index; `1u` on the GEP; **exactly one vector operand** | 477 |
| E12 | `extractelement (shuffle X, Y, M), I → extractelement Src, M[I]` | constant index or a splat mask; resolves through the mask to the source operand, or to `poison` for a `-1` mask element | 501 |
| E13 | `extractelement (cast X), I → cast (ee X, I)` | `1u` on the cast; **not** a bitcast (E5 handles that) | 524 |
| E14 | `SimplifyDemandedVectorElts` on the source, demanding only lane `I` | `1u` on the source; fixed vector with more than one element | 536 |
| E15 | the multi-use variant, demanding `findDemandedEltsByAllUsers` (line 367) | all users must be extracts at constant indices | 547 |

## 16.2 `visitInsertElementInst` (line 1684)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| N1 | canonicalise the index to `i64` | **[canon]** | 1693 |
| N2 | `insertelement (insertelement V, S2, J), S1, I → insertelement (insertelement V, S1, I), S2, J` | `1u` on the inner insert; `J > I`; `S2` not a constant — **[canon]** sorts inserts by index | 1698 |
| N3 | `insertelement undef, (bitcast S), I → bitcast (insertelement undef', S, I)` | `1u` on the bitcast; `S` scalar integer or FP | 1710 |
| N4 | `insertelement (bitcast V), (bitcast S), I → bitcast (insertelement V, S, I)` | `1u` on one; element types must line up | 1723 |
| N5 | a chain of `insertelement (extractelement …)` → `shufflevector` | `collectShuffleElements` (line 793); only applied at the *root* of the chain (`isShuffleRootCandidate`); fixed vectors; constant indices in range. Iterates (`Rerun`) until stable | 1737 |
| N6 | `SimplifyDemandedVectorElts` | fixed vector | 1768 |
| N7 | `foldConstantInsEltIntoShuffle` (line 1484) | inserting a constant into a shuffle result → fold into the shuffle's constant operand | 1780 |
| N8 | `hoistInsEltConst` (line 1461) | reorder two inserts so the constant one is innermost — **[canon]** | 1783 |
| N9 | `foldInsSequenceIntoSplat` (line 1291) | a full sequence inserting the *same* scalar into every lane → a splat shuffle | 1786 |
| N10 | `foldInsEltIntoSplat` (line 1365) | inserting the splatted value into a splat → the splat | 1789 |
| N11 | `foldInsEltIntoIdentityShuffle` (line 1402) | inserting into a shuffle that is an identity on the other lanes → widen the shuffle | 1792 |
| N12 | `narrowInsElt` (line 1588) | `insertelement (ext V), (ext S), I → ext (insertelement V, S, I)` | 1795 |
| N13 | `foldTruncInsEltPair` (line 1621) | two `trunc`s of the halves of a wide integer inserted into adjacent lanes → a bitcast; **endianness-dependent** | 1798 |

## 16.3 `visitShuffleVectorInst` (line 2870)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| S1 | `simplifyBinOpSplats` (line 2843): `shuffle (binop (splat X), (splat Y)), poison, zeromask → splat (binop X, Y)` | | 2879 |
| S2 | `shuffle X, Y, zeromask → shuffle X, poison, zeromask` | the RHS is unused by a zero mask — **[canon]** | 2882 |
| S3 | bail out for scalable vectors | | 2886 |
| S4 | `shuffle (bitcast X), (bitcast Y), M → bitcast (shuffle X, Y, M)` | same source type; same scalar bit width; `1u` on one | 2893 |
| S5 | `shuffle (bitcast X), undef, M → bitcast (shuffle X, undef, M')` | the mask must rescale exactly (`scaleShuffleMaskElts`) and the rescaled shuffle must simplify | 2906 |
| S6 | `shuffle X, X, M → shuffle X, poison, M'` | `createUnaryMask` folds the RHS indices back onto the LHS | 2921 |
| S7 | `shuffle undef, Y, M → shuffle Y, undef, M'` | commute — **[canon]** | 2929 |
| S8 | `canonicalizeInsertSplat` (line 2293) | `shuffle (insertelement poison, X, K), poison, zeromask → shuffle (insertelement poison, X, 0), poison, zeromask` — **[canon]**, normalises splats to index 0 | 2934 |
| S9 | `foldSelectShuffle` (line 2325) | a shuffle that is really a lane-wise select between two binops → one binop with shuffled operands. Uses `getAlternateBinop` (line 2142) so that e.g. `add`/`sub` pairs can be unified via a constant | 2937 |
| S10 | `foldTruncShuffle` (line 2464) | a shuffle extracting every Nth byte of a bitcast → `trunc`; **endianness-dependent** | 2940 |
| S11 | `narrowVectorSelect` (line 2505) | `shuffle (select C, X, Y), poison, M → select (shuffle C), (shuffle X), (shuffle Y)` | 2943 |
| S12 | `foldShuffleOfUnaryOps` (line 2539) | `shuffle (unop X), (unop Y), M → unop (shuffle X, Y, M)`; also `fneg`/`fabs`. FMF intersected | 2946 |
| S13 | `foldCastShuffle` (line 2572) | `shuffle (cast X), (cast Y), M → cast (shuffle X, Y, M)` | 2949 |
| S14 | `SimplifyDemandedVectorElts` | | 2953 |
| S15 | `foldIdentityExtractShuffle` (line 2636) | a shuffle of a shuffle that is an identity extract → collapse | 2960 |
| S16 | `foldShuffleWithInsert` (line 2686) | a shuffle whose source is an `insertelement` at a lane the mask ignores → drop the insert | 2963 |
| S17 | `foldIdentityPaddedShuffles` (line 2774) | two shuffles that together form an identity | 2966 |
| S18 | `shuffle (select …), C, M → select …, shuffled` | the RHS is a constant; the select's condition is scalar and either the RHS is poison or the condition is guaranteed non-poison | 2970 |
| S19 | `shuffle (phi …), C, M` → sink into the phi | RHS constant; multiple uses allowed | 2981 |
| S20 | re-evaluate the operand tree in the shuffled element order | `canEvaluateShuffled` (line 1839) / `evaluateInDifferentElementOrder` (line 2003); RHS must be `poison` | 2988 |
| S21 | `bitcast (shuffle extracting a contiguous run) → extractelement (bitcast)` | `isShuffleExtractingFromLHS` (line 2111); for each `bitcast` user, the target element width must divide the vector width exactly; an unaligned start emits an extra shuffle | 2996 |
| S22 | shuffle-of-shuffle collapse | both inner shuffles must have a `poison` second operand (or the outer RHS is poison) | 3060 onwards |

## 16.4 `visitInsertValueInst` (line 1226)

| # | Rule | Side conditions | Line |
|---|---|---|---|
| V1 | `foldAggregateConstructionIntoAggregateReuse` (line 880) | a chain of `insertvalue`s that rebuilds an aggregate identical to an existing one (possibly through PHIs) → reuse the original. This is the most involved function in the file: it walks the insert chain, checks that every inserted value is the matching `extractvalue` of a common source, and handles the case where the sources differ per predecessor by building a PHI | 1230 |
| V2 | `insertvalue (load …), …` | handled via demanded-elements | — |

