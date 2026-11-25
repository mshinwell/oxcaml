(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018--2021 OCamlPro SAS                                    *)
(*   Copyright 2018--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Renaming], after its interface
   middle_end/flambda2/nominal/renaming.mli
   (Git blob f23b1b5561f68006110a15b3dd814fc0634252a6). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Variable_.

(* renaming.mli:28  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Renaming.t".
(* renaming.mli:30  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Renaming.empty".
(* renaming.mli:54  val compose : second:t -> first:t -> t *)
Parameter compose : t -> t -> M t.
Extract Inlined Constant compose => "Renaming.compose".
(* renaming.mli:56  val add_variable : t -> Variable.t -> Variable.t -> t *)
Parameter add_variable : t -> Variable_.t -> Variable_.t -> M t.
Extract Inlined Constant add_variable => "Renaming.add_variable".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Renaming. End Renaming.
