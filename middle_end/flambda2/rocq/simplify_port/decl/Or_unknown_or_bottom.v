(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018 OCamlPro SAS                                          *)
(*   Copyright 2018 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Or_unknown_or_bottom], after its interface
   middle_end/flambda2/lattices/or_unknown_or_bottom.mli
   (Git blob 46ea135c7f02b476ee41d78e06766d4b3806062d). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* or_unknown_or_bottom.mli:17  type 'a t = | Unknown | Ok of 'a | Bottom *)
Inductive t (A : Type) : Type :=
| Unknown : t A
| Ok : A -> t A
| Bottom : t A.
Arguments Unknown {A}.
Arguments Ok {A}.
Arguments Bottom {A}.
Extract Inductive t => "Or_unknown_or_bottom.t" [ "Or_unknown_or_bottom.Unknown" "Or_unknown_or_bottom.Ok" "Or_unknown_or_bottom.Bottom" ].

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Or_unknown_or_bottom. End Or_unknown_or_bottom.
