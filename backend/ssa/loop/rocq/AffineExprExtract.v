(* Extraction directives for AffineExpr.v (the extraction itself is run by
   Extract.v). Everything about the functions is proved in AffineExpr.v, and
   the mappings of [int], [Int64] and the list functions onto OxCaml's are in
   OxCamlExtract.v; this file only prints the model's one literal. *)

From Stdlib Require Import Extraction.
From OxCamlLoop Require Import AffineExpr.

Extract Inlined Constant word_bits => "64".
