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
   Simplify uses of the compiler's module [Simplify_variadic_primitive], after its interface
   middle_end/flambda2/simplify/simplify_variadic_primitive.mli
   (Git blob 9ee4d3178134ddb31abd9cd8bd5b94928abc9d9b). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_var Debuginfo Downwards_acc Flambda2_types Flambda_primitive Simple Simplify_primitive_result.

(* simplify_variadic_primitive.mli:19  val simplify_variadic_primitive : Downwards_acc.t -> Flambda_primitive.t -> Flambda_primitive.variadic_primitive -> args_with_tys:(Simple.t * Flambda2_types.t) list -> Debuginfo.t -> result_var:Bound_var.t -> Simplify_primitive_result.t *)
Parameter simplify_variadic_primitive : Downwards_acc.t -> Flambda_primitive.t -> Flambda_primitive.variadic_primitive -> list (Simple.t * Flambda2_types.t) -> Debuginfo.t -> Bound_var.t -> M Simplify_primitive_result.t.
Extract Inlined Constant simplify_variadic_primitive => "Simplify_variadic_primitive.simplify_variadic_primitive".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_variadic_primitive. End Simplify_variadic_primitive.
