(* Extraction directives for AffineSsa.v (the extraction itself is run by
   Extract.v). Everything about the functions is proved in AffineSsa.v; the SSA
   values it computes on are those of SsaModel.v, whose extraction is in
   SsaModelExtract.v. This file only prints the model's two literals. As in
   OxCamlExtract.v, the mapping is trusted by inspection. *)

From Stdlib Require Import Extraction.
From OxCamlLoop Require Import AffineSsa.

Extract Inlined Constant max_nodes => "256".
Extract Inlined Constant max_shift_bits => "16".
