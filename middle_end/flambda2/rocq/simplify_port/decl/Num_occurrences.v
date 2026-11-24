(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2019--2020 OCamlPro SAS                                    *)
(*   Copyright 2019--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Num_occurrences], after its interface
   middle_end/flambda2/nominal/num_occurrences.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* num_occurrences.mli:17  type t = | Zero | One | More_than_one *)
Inductive t : Type :=
| Zero : t
| One : t
| More_than_one : t.
Extract Inductive t => "Num_occurrences.t" [ "Num_occurrences.Zero" "Num_occurrences.One" "Num_occurrences.More_than_one" ].

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Num_occurrences. End Num_occurrences.
