(* The extraction of the loop models to OCaml, one file per model, written
   next to this file (rocq/Makefile then moves SsaModel.ml, the model of
   the SSA graph, next to its source in backend/ssa/rocq/): SsaModel.ml,
   FourierMotzkin.ml, LoopComparisons.ml, AffineExpr.ml, NaturalLoop.ml,
   AffineSsa.ml, InductionVar.ml, LoopTermination.ml, DeadInductionVar.ml,
   DeleteEmptyLoops.ml, and OcamlList.ml for the few list functions with
   no OCaml counterpart. The modules of the same names in the parent
   directory (fourier_motzkin.ml, ...) are thin wrappers turning them into
   implementations of the .mli files there, raising [Overflow] where the
   models return [None], or building the hash table of
   [Induction_var.compute_op_def] and running the rewriting of
   [Delete_empty_loops.run], which are not modelled.

   Everything about the functions is proved in the model files. The
   mapping of the models' types and primitives onto OCaml's is what has to
   be trusted by inspection; it is in OcamlExtract.v (rocq/),
   IntegerComparisonExtract.v (backend/rocq/), SsaModelExtract.v
   (backend/ssa/rocq/) and the *Extract.v files here. *)

From Stdlib Require Import Extraction.
From OxcamlStdlib Require Import OcamlExtract.
From OxcamlBackend Require Import IntegerComparisonExtract.
From OxcamlSsa Require Import SsaModelExtract.
From OxcamlLoop Require Import FourierMotzkin FourierMotzkinExtract
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
