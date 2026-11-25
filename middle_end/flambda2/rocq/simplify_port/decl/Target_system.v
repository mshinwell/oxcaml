(* The interface that this file follows has no header: see the comment
   below. *)

(* CR mshinwell: The is_32_bit and Machine_width declarations follow
   utils/target_system.mli, which has no leading notice; the donor-header rule
   supplies none. What notice should this generated file carry? *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Target_system], after its interface
   utils/target_system.mli
   (Git blob b06bc4df780ddffc16ee29cdff65e79c3c1af4c4). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

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

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Target_system. End Target_system.
