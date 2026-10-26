(* The extraction of the loop models to OCaml, one file per model, written
   next to this file: FourierMotzkin.ml, LoopComparisons.ml, AffineExpr.ml,
   and OcamlList.ml for the few list functions with no OCaml counterpart.
   The wrappers in wrapper/ turn them into implementations of the
   corresponding .mli files, raising [Overflow] where the models return
   [None]. rocq/Makefile runs this and formats the output.

   Everything about the functions is proved in the model files. The
   mapping of the models' types and primitives onto OCaml's is what has to
   be trusted by inspection; it is in OcamlExtract.v (rocq/),
   IntegerComparisonExtract.v (backend/rocq/) and the *Extract.v files
   here. *)

From Stdlib Require Import Extraction.
From OxcamlStdlib Require Import OcamlExtract.
From OxcamlBackend Require Import IntegerComparisonExtract.
From OxcamlLoop Require Import FourierMotzkin FourierMotzkinExtract
  LoopComparisons AffineExpr AffineExprExtract.

Separate Extraction
  Affine feasible entails
  oriented_continue_comparison continue_terminates facts
  Range to_affine.
