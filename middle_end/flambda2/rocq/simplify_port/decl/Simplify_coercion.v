(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplify_coercion], after its interface
   middle_end/flambda2/simplify/simplify_coercion.mli
   (Git blob be39b7b101d40f675866df473e6670f85284eec0). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Coercion Downwards_acc.

(* simplify_coercion.mli:17  val simplify_coercion : Downwards_acc.t -> Coercion.t -> Coercion.t *)
Parameter simplify_coercion : Downwards_acc.t -> Coercion.t -> M Coercion.t.
Extract Inlined Constant simplify_coercion => "Simplify_coercion.simplify_coercion".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_coercion. End Simplify_coercion.
