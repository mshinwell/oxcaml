(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Inlined_debuginfo], after its interface
   middle_end/flambda2/term_basics/inlined_debuginfo.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* inlined_debuginfo.mli:46  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Inlined_debuginfo.t".
