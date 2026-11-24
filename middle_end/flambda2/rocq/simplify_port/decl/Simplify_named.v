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
   Simplify uses of the compiler's module [Simplify_named], after its interface
   middle_end/flambda2/simplify/simplify_named.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_pattern Downwards_acc Flambda Or_invalid Removed_operations Simplified_named Simplify_common Simplify_named_result.

(* simplify_named.mli:19  val simplify_named : Downwards_acc.t -> Bound_pattern.t -> Flambda.Named.t -> simplify_function_body:Simplify_common.simplify_function_body -> (Simplify_named_result.t Or_invalid.t * Removed_operations.t) Simplified_named.or_rewritten *)
Parameter simplify_named : Downwards_acc.t -> Bound_pattern.t -> Flambda.Named.t -> Simplify_common.simplify_function_body -> M (Simplified_named.or_rewritten (Or_invalid.t Simplify_named_result.t * Removed_operations.t)).
Extract Inlined Constant simplify_named => "Simplify_named.simplify_named".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_named. End Simplify_named.
