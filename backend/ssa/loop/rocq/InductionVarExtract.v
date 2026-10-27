(* Extraction directives for InductionVar.v (the extraction itself is run
   by Extract.v): the sign of a step is a polymorphic variant. As in
   OxCamlExtract.v, the mapping is trusted by inspection. *)

From Stdlib Require Import Extraction.
From OxCamlLoop Require Import InductionVar.

Extract Inductive biv_sign => "[ `Add | `Sub ]" [ "`Add" "`Sub" ].
