(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Clflags], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* clflags.mli:223  val target_is_jsir : unit -> bool *)
Parameter target_is_jsir : unit -> M bool.
Extract Inlined Constant target_is_jsir => "Clflags.target_is_jsir".
Module Register_allocator.
  (* clflags.mli:403  type t = | Cfg | Irc | Ls | Gi *)
  Parameter t : Type.
  Extract Inlined Constant t => "Clflags.Register_allocator.t".
End Register_allocator.
