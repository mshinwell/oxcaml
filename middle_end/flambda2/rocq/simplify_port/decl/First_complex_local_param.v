(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [First_complex_local_param], after its interface
   middle_end/flambda2/terms/first_complex_local_param.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* first_complex_local_param.mli:35  type t = | Index of int | Never_partially_applied *)
Inductive t : Type :=
| Index : int -> t
| Never_partially_applied : t.
Extract Inductive t => "First_complex_local_param.t" [ "First_complex_local_param.Index" "First_complex_local_param.Never_partially_applied" ].

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module First_complex_local_param. End First_complex_local_param.
