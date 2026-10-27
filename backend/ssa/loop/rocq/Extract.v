(* The extraction of the loop models to OxCaml, one file per model, written
   next to this file (rocq/Makefile then moves SsaModel.ml, the model of
   the SSA graph, next to its source in backend/ssa/rocq/): SsaModel.ml,
   FourierMotzkin.ml, LoopComparisons.ml, AffineExpr.ml, NaturalLoop.ml,
   AffineSsa.ml, InductionVar.ml, LoopTermination.ml, DeadInductionVar.ml,
   DeleteEmptyLoops.ml, and OxCamlList.ml for the few list functions with
   no OxCaml counterpart. The pass itself, delete_empty_loops.ml in the
   parent directory, calls [DeleteEmptyLoops.find_deletions] and rewrites
   the graph at the loops it returns; that rewriting, and the table of
   [Ssa_view.compute_op_def] the analyses are given, are not modelled.

   The entry points extracted are [find_deletions] and, for the unit test
   oxcaml/tests/backend/ssa/loop_comparisons_facts.ml, the affine forms
   with [feasible], [entails] and [facts]; everything they use comes with
   them.

   Everything about the functions is proved in the model files. The
   mapping of the models' types and primitives onto OxCaml's is what has to
   be trusted by inspection; it is in OxCamlExtract.v (rocq/),
   IntegerComparisonExtract.v (backend/rocq/), SsaModelExtract.v
   (backend/ssa/rocq/) and the *Extract.v files here. *)

From Stdlib Require Import Extraction.
From OxCamlStdlib Require Import OxCamlExtract.
From OxCamlBackend Require Import IntegerComparisonExtract.
From OxCamlSsa Require Import SsaModelExtract.
From OxCamlLoop Require Import FourierMotzkin FourierMotzkinExtract
  LoopComparisons AffineExpr AffineExprExtract NaturalLoop AffineSsa
  AffineSsaExtract InductionVar InductionVarExtract LoopTermination
  DeadInductionVar DeleteEmptyLoops.

Separate Extraction
  Affine feasible entails facts
  DeleteEmptyLoops.find_deletions.
