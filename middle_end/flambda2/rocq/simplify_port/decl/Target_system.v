(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Target_system], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Machine_width.
  (* target_system.mli:49  type t = | Thirty_two ( * Traditional 32-bit OCaml with GC tag bit * ) | Thirty_two_no_gc_tag_bit ( * JavaScript mode with full 32-bit integers * ) | Sixty_four ( * Traditional 64-bit OCaml with GC tag bit * ) *)
  Parameter t : Type.
  Extract Inlined Constant t => "Target_system.Machine_width.t".
End Machine_width.
