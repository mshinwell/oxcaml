(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2022 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Poll_attribute], after its interface
   middle_end/flambda2/terms/poll_attribute.mli
   (Git blob c6a9aef3d5ec3e6270bba76a825b1f35e7ea5834). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* poll_attribute.mli:15  type t = | Default | Error *)
Inductive t : Type :=
| Default : t
| Error : t.
Extract Inductive t => "Poll_attribute.t" [ "Poll_attribute.Default" "Poll_attribute.Error" ].

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Poll_attribute. End Poll_attribute.
