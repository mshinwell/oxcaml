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
   Simplify uses of the compiler's module [Simplify_primitive], after its interface
   middle_end/flambda2/simplify/simplify_primitive.mli
   (Git blob 278edd7a532fff7870341043832a60379d5939b8). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_var Debuginfo Downwards_acc Flambda_primitive Simplify_primitive_result.

(* simplify_primitive.mli:19  val simplify_primitive : Downwards_acc.t -> Flambda_primitive.t -> Debuginfo.t -> result_var:Bound_var.t -> Simplify_primitive_result.t *)
Parameter simplify_primitive : Downwards_acc.t -> Flambda_primitive.t -> Debuginfo.t -> Bound_var.t -> M Simplify_primitive_result.t.
Extract Inlined Constant simplify_primitive => "Simplify_primitive.simplify_primitive".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_primitive. End Simplify_primitive.
