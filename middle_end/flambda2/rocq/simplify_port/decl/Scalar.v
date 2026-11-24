(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Scalar], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Signedness.
  (* scalar.mli:208  type t = | Signed | Unsigned *)
  Inductive t : Type :=
  | Signed : t
  | Unsigned : t.
  Extract Inductive t => "Scalar.Signedness.t" [ "Scalar.Signedness.Signed" "Scalar.Signedness.Unsigned" ].
End Signedness.
