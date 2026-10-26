(* Extraction directives for AffineSsa.v (the extraction itself is run by
   Extract.v). Everything about the functions is proved in AffineSsa.v;
   this file says which compiler type and function stand for the model's
   SSA values and their equality, and prints the model's one literal. As
   in OcamlExtract.v, the mapping is trusted by inspection. *)

From Stdlib Require Import Extraction.
From OxcamlLoop Require Import AffineSsa.

Extract Constant value => "Ssa.finished Ssa.Value.t".
Extract Inlined Constant value_eqb => "Ssa.Value.equal".
Extract Inlined Constant max_shift_bits => "16".
