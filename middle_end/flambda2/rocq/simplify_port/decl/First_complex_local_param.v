(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [First_complex_local_param], after its interface
   middle_end/flambda2/terms/first_complex_local_param.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* first_complex_local_param.mli:35  type t = | Index of int | Never_partially_applied *)
Parameter t : Type.
Extract Inlined Constant t => "First_complex_local_param.t".
