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
   Simplify uses of the compiler's module [Reification], after its interface
   middle_end/flambda2/simplify/lifting/reification.mli
   (Git blob 04d02e433b07b0110f7400c10965b504718b58a1). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_var Debuginfo Downwards_acc Flambda_kind Or_invalid Simplified_named.

(* reification.mli:19  val try_to_reify : Downwards_acc.t -> Debuginfo.t -> Simplified_named.t -> bound_to:Bound_var.t -> kind_of_bound_to:Flambda_kind.t -> allow_lifting:bool -> Simplified_named.t Or_invalid.t * Downwards_acc.t *)
Parameter try_to_reify : Downwards_acc.t -> Debuginfo.t -> Simplified_named.t -> Bound_var.t -> Flambda_kind.t -> bool -> M (Or_invalid.t Simplified_named.t * Downwards_acc.t).
Extract Inlined Constant try_to_reify => "Reification.try_to_reify".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Reification. End Reification.
