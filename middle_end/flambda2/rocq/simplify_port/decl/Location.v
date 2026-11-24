(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Location], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Warnings.

(* location.mli:42  type t = Warnings.loc = { loc_start: Lexing.position; loc_end: Lexing.position; loc_ghost: bool; } *)
Definition t : Type := Warnings.loc.
Extract Inlined Constant t => "Location.t".
(* location.mli:353  val prerr_warning: t -> Warnings.t -> unit *)
Parameter prerr_warning : t -> Warnings.t -> M unit.
Extract Inlined Constant prerr_warning => "Location.prerr_warning".
