(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2021 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Or_infinity], after its interface
   middle_end/flambda2/numbers/or_infinity.mli
   (Git blob c3de626ab65e2644862a86a9a8bc356f7eac7783). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* or_infinity.mli:15  type 'a t = | Finite of 'a | Infinity *)
Inductive t (A : Type) : Type :=
| Finite : A -> t A
| Infinity : t A.
Arguments Finite {A}.
Arguments Infinity {A}.
Extract Inductive t => "Or_infinity.t" [ "Or_infinity.Finite" "Or_infinity.Infinity" ].
(* or_infinity.mli:19  val compare : f:('a -> 'a -> int) -> 'a t -> 'a t -> int *)
Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
Extract Inlined Constant compare => "Or_infinity.compare".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Or_infinity. End Or_infinity.
