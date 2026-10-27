(* The extraction of the loop models to OxCaml, one file per model, written
   next to this file (rocq/Makefile then moves SsaModel.ml, the model of
   the SSA graph, next to its source in backend/ssa/rocq/): SsaModel.ml,
   FourierMotzkin.ml, LoopComparisons.ml, AffineExpr.ml, NaturalLoop.ml,
   AffineSsa.ml, InductionVar.ml, LoopTermination.ml, DeadInductionVar.ml,
   DeleteEmptyLoops.ml, and OcamlList.ml for the few list functions with
   no OxCaml counterpart. The graph-level models have thin wrappers in the
   parent directory (natural_loop.ml, induction_var.ml, termination.ml,
   dead_induction_var.ml, delete_empty_loops.ml), which add the labelled
   arguments of the .mli files there, the hash table of
   [Induction_var.compute_op_def] and the rewriting of
   [Delete_empty_loops.run], which are not modelled; the arithmetic models
   (FourierMotzkin, LoopComparisons, AffineExpr, AffineSsa) are used as
   extracted.

   Everything about the functions is proved in the model files. The
   mapping of the models' types and primitives onto OxCaml's is what has to
   be trusted by inspection; it is in OcamlExtract.v (rocq/),
   IntegerComparisonExtract.v (backend/rocq/), SsaModelExtract.v
   (backend/ssa/rocq/) and the *Extract.v files here. *)

From Stdlib Require Import Extraction.
From OxCamlStdlib Require Import OcamlExtract.
From OxCamlBackend Require Import IntegerComparisonExtract.
From OxCamlSsa Require Import SsaModelExtract.
From OxCamlLoop Require Import FourierMotzkin FourierMotzkinExtract
  LoopComparisons AffineExpr AffineExprExtract NaturalLoop AffineSsa
  AffineSsaExtract InductionVar InductionVarExtract LoopTermination
  DeadInductionVar DeleteEmptyLoops.

Separate Extraction
  Affine feasible entails
  oriented_continue_comparison continue_terminates facts
  Range to_affine
  new_ctx linearize cond_facts guards_at
  NaturalLoop.find_loops NaturalLoop.edge_dominates
  InductionVar.analyze InductionVar.is_header_param
  InductionVar.is_loop_invariant InductionVar.signed_step
  InductionVar.back_edge_set
  LoopTermination.analyze LoopTermination.find_exit_branch
  DeadInductionVar.analyze
  DeleteEmptyLoops.find_deletions.
