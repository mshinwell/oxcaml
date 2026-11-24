(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Target_system], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* target_system.mli:17  val is_32_bit : unit -> bool *)
Parameter is_32_bit : unit -> M bool.
Extract Inlined Constant is_32_bit => "Target_system.is_32_bit".
Module Machine_width.
  (* target_system.mli:49  type t = | Thirty_two ( * Traditional 32-bit OCaml with GC tag bit * ) | Thirty_two_no_gc_tag_bit ( * JavaScript mode with full 32-bit integers * ) | Sixty_four ( * Traditional 64-bit OCaml with GC tag bit * ) *)
  Parameter t : Type.
  Extract Inlined Constant t => "Target_system.Machine_width.t".
  (* target_system.mli:54  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Target_system.Machine_width.print".
  (* target_system.mli:56  val equal : t -> t -> bool *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Target_system.Machine_width.equal".
End Machine_width.
