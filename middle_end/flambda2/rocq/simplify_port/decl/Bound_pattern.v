(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2019--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Bound_pattern], after its interface
   middle_end/flambda2/bound_identifiers/bound_pattern.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_var.

(* bound_pattern.mli:18  type t = private | Singleton of Bound_var.t ( ** The binding of a single variable, which is statically scoped. This case is not used for sets of closures. * ) | Set_of_closures of Bound_var.t list ( ** The binding of one or more variables to the individual closures in a set of closures. The variables are statically scoped. * ) | Static of Bound_static.t *)
Parameter t : Type.
Extract Inlined Constant t => "Bound_pattern.t".
(* bound_pattern.mli:30  val singleton : Bound_var.t -> t *)
Parameter singleton : Bound_var.t -> M t.
Extract Inlined Constant singleton => "Bound_pattern.singleton".
