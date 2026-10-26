(* Extraction directives for AffineExpr.v (the extraction itself is run by
   Extract.v). Everything about the functions is proved in AffineExpr.v,
   and the mappings of [int], [Int64] and the list functions onto OCaml's
   are in OcamlExtract.v; this file only prints the model's one literal. *)

From Stdlib Require Import Extraction.
From OxcamlLoop Require Import AffineExpr.

Extract Inlined Constant word_bits => "64".
