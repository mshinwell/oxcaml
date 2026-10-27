(* Extraction directives for FourierMotzkin.v (the extraction itself is
   run by Extract.v). Everything about the functions is proved in
   FourierMotzkin.v, and the mappings of [int], [Int64], the list functions
   and the checked arithmetic onto OxCaml's are in OxCamlExtract.v and
   IntArithExtract.v (rocq/). This file only prints the two size limits as
   literals: a primitive-integer constant would otherwise be printed as
   [Uint63.of_int 500]. Keep them in step with FourierMotzkin.v. *)

From Stdlib Require Import Extraction.
From OxCamlLoop Require Import FourierMotzkin.

Extract Inlined Constant max_atoms => "64".
Extract Inlined Constant max_ineqs => "500".
