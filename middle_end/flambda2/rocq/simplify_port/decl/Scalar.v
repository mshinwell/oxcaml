(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                 Jacob Van Buren, Jane Street, New York                 *)
(*                                                                        *)
(*   Copyright 2025 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Scalar], after its interface
   typing/scalar.mli
   (Git blob 12e97d0cb241a3516c8210123741efeb93df00ed). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Signedness.
  (* scalar.mli:208  type t = | Signed | Unsigned *)
  Inductive t : Type :=
  | Signed : t
  | Unsigned : t.
  Extract Inductive t => "Scalar.Signedness.t" [ "Scalar.Signedness.Signed" "Scalar.Signedness.Unsigned" ].
End Signedness.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Scalar. End Scalar.
