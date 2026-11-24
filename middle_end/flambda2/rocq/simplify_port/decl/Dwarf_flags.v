(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Dwarf_flags], after its interface
   backend/debug/dwarf/dwarf_flags/dwarf_flags.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* dwarf_flags.mli:76  val gdwarf_may_alter_codegen : bool ref *)
Parameter gdwarf_may_alter_codegen : ref bool.
Extract Inlined Constant gdwarf_may_alter_codegen => "Dwarf_flags.gdwarf_may_alter_codegen".
