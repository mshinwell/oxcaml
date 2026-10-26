(* Extraction directives for InductionVar.v (the extraction itself is run
   by Extract.v): the sign of a step is the polymorphic variant of the
   interface, backend/ssa/loop/induction_var.mli. As in OcamlExtract.v,
   the mapping is trusted by inspection. *)

From Stdlib Require Import Extraction.
From OxcamlLoop Require Import InductionVar.

Extract Inductive biv_sign => "[ `Add | `Sub ]" [ "`Add" "`Sub" ].
