(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Branch_annotations], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Likelihood.

(* branch_annotations.mli:30  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Branch_annotations.t".
(* branch_annotations.mli:46  val with_likelihood : t -> Likelihood.t -> t *)
Parameter with_likelihood : t -> Likelihood.t -> M t.
Extract Inlined Constant with_likelihood => "Branch_annotations.with_likelihood".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Branch_annotations. End Branch_annotations.
