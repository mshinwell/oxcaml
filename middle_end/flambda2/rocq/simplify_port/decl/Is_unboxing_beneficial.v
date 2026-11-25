(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Is_unboxing_beneficial], after its interface
   middle_end/flambda2/simplify/unboxing/is_unboxing_beneficial.mli
   (Git blob 2bad159abfc256a6bd556259aa7d68593643cd89). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Unboxing_types.

(* is_unboxing_beneficial.mli:20  val filter_non_beneficial_decisions : Unboxing_types.decision -> Unboxing_types.decision *)
Parameter filter_non_beneficial_decisions : Unboxing_types.decision_ -> M Unboxing_types.decision_.
Extract Inlined Constant filter_non_beneficial_decisions => "Is_unboxing_beneficial.filter_non_beneficial_decisions".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Is_unboxing_beneficial. End Is_unboxing_beneficial.
