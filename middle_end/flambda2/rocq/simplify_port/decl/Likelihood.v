(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Likelihood], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* likelihood.mli:44  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Likelihood.t".
(* likelihood.mli:46  val cold : t *)
Parameter cold : t.
Extract Inlined Constant cold => "Likelihood.cold".
