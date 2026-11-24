(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Debuginfo], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* debuginfo.mli:97  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Debuginfo.t".
(* debuginfo.mli:99  val none : t *)
Parameter none : t.
Extract Inlined Constant none => "Debuginfo.none".
