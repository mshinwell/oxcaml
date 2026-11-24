(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Oxcaml_flags], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* oxcaml_flags.mli:132  type opt_level = Oclassic | O2 | O3 | O4 *)
Parameter opt_level_ : Type.
Extract Inlined Constant opt_level_ => "Oxcaml_flags.opt_level".
