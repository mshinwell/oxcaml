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
   Simplify uses of the compiler's module [Simplify_static_const], after its interface
   middle_end/flambda2/simplify/simplify_static_const.mli
   (Git blob 035a6d8c9c83506029bf142be3116e405ab58f4b). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_static Downwards_acc Flambda Rebuilt_static_const Simplify_common.

(* simplify_static_const.mli:21  val simplify_static_consts : Downwards_acc.t -> Bound_static.t -> Static_const_group.t -> simplify_function_body:Simplify_common.simplify_function_body -> Bound_static.t * Rebuilt_static_const.Group.t * Downwards_acc.t *)
Parameter simplify_static_consts : Downwards_acc.t -> Bound_static.t -> Flambda.Static_const_group.t -> Simplify_common.simplify_function_body -> M (tuple3 Bound_static.t Rebuilt_static_const.Group.t Downwards_acc.t).
Extract Inlined Constant simplify_static_consts => "Simplify_static_const.simplify_static_consts".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_static_const. End Simplify_static_const.
