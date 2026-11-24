(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Oxcaml_args], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Extra_options.
  (* oxcaml_args.mli:309  val symbol : string -> string -> 'a -> (string * 'a) list -> unit -> 'a *)
  Parameter symbol : forall {A : Type}, string -> string -> A -> list (string * A) -> unit -> M A.
  Extract Inlined Constant symbol => "Oxcaml_args.Extra_options.symbol".
End Extra_options.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Oxcaml_args. End Oxcaml_args.
