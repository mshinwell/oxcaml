(* The extraction of the loop models to OCaml, one file per model, written
   next to this file: FourierMotzkin.ml, LoopComparisons.ml, AffineExpr.ml,
   AffineSsa.ml, and OcamlList.ml for the few list functions with no OCaml
   counterpart. The modules of the same names in the parent directory
   (fourier_motzkin.ml, ...) are thin wrappers turning them into
   implementations of the .mli files there, raising [Overflow] where the
   models return [None]. rocq/Makefile runs this and formats the output.

   Everything about the functions is proved in the model files. The
   mapping of the models' types and primitives onto OCaml's is what has to
   be trusted by inspection; it is in OcamlExtract.v (rocq/),
   IntegerComparisonExtract.v (backend/rocq/) and the *Extract.v files
   here. *)

From Stdlib Require Import Extraction.
From OxcamlStdlib Require Import OcamlExtract.
From OxcamlBackend Require Import IntegerComparisonExtract.
From OxcamlLoop Require Import FourierMotzkin FourierMotzkinExtract
  LoopComparisons AffineExpr AffineExprExtract AffineSsa AffineSsaExtract.

Separate Extraction
  Affine feasible entails
  oriented_continue_comparison continue_terminates facts
  Range to_affine
  new_ctx linearize cond_facts.
