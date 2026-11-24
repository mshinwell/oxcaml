(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Or_null], after its interface
   middle_end/flambda2/algorithms/or_null.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* or_null.mli:29  type 'a t = | Null | This of 'a [@@or_null] *)
Inductive t (A : Type) : Type :=
| Null : t A
| This : A -> t A.
Arguments Null {A}.
Arguments This {A}.
(* or_null.mli:38  val null : 'a t *)
Parameter null : forall {A : Type}, t A.
Extract Inlined Constant null => "Or_null.null".
(* or_null.mli:40  val this : 'a -> 'a t *)
Parameter this : forall {A : Type}, A -> M (t A).
Extract Inlined Constant this => "Or_null.this".
(* or_null.mli:48  val of_option : 'a option -> 'a t *)
Parameter of_option : forall {A : Type}, option A -> M (t A).
Extract Inlined Constant of_option => "Or_null.of_option".
