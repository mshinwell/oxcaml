(* Extraction directives for FourierMotzkin.v (the extraction itself is
   run by Extract.v). Everything about the functions is proved in
   FourierMotzkin.v, and the mappings of the basic types, [int], [Int64]
   and the list functions onto OCaml's are in OcamlExtract.v. What this
   file adds, and what has to be trusted by inspection, is the OCaml for
   the four overflow tests [add_fits], [mul_fits], [add_fits64] and
   [mul_fits64]. The model takes each as given, with an axiom saying that
   it answers whether the exact result fits the type; the OCaml below is
   the implementation of that test from fourier_motzkin.ml: the sign-bit
   trick for addition, a divide-back check for multiplication. *)

From Stdlib Require Import Extraction.
From OxcamlStdlib Require Import OcamlExtract.
From OxcamlLoop Require Import FourierMotzkin.

Extract Constant add_fits =>
  "fun a b ->
    let s = a + b in
    a lxor s land (b lxor s) >= 0".

Extract Constant mul_fits =>
  "fun a b ->
    if Int.equal a 0 || Int.equal b 0
    then true
    else if
      (Int.equal a (-1) && Int.equal b Int.min_int)
      || (Int.equal b (-1) && Int.equal a Int.min_int)
    then false
    else Int.equal (a * b / a) b".

Extract Constant add_fits64 =>
  "fun a b ->
    let s = Int64.add a b in
    Int64.compare (Int64.logand (Int64.logxor a s) (Int64.logxor b s)) 0L
    >= 0".

Extract Constant mul_fits64 =>
  "fun a b ->
    if Int64.equal a 0L || Int64.equal b 0L
    then true
    else if
      (Int64.equal a (-1L) && Int64.equal b Int64.min_int)
      || (Int64.equal b (-1L) && Int64.equal a Int64.min_int)
    then false
    else Int64.equal (Int64.div (Int64.mul a b) a) b".

(* The size limits, as literals: a primitive-integer constant would
   otherwise be printed as [Uint63.of_int 10000]. *)
Extract Inlined Constant max_atoms => "64".
Extract Inlined Constant max_ineqs => "10000".
