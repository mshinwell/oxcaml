(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Switch_arm], after its interface
   middle_end/flambda2/terms/switch_arm.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* switch_arm.mli:29  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Switch_arm.t".
