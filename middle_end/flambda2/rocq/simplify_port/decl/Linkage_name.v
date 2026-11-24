(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Linkage_name], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* identifiable.mli:108  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Linkage_name.t".
(* linkage_name.mli:22  val to_string : t -> string *)
Parameter to_string : t -> M string.
Extract Inlined Constant to_string => "Linkage_name.to_string".
