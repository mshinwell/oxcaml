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
   Simplify uses of the compiler's module [Simplify_set_of_closures], after its interface
   middle_end/flambda2/simplify/simplify_set_of_closures.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Bound_name Bound_pattern Bound_static Code Code_id Downwards_acc Flambda Function_slot Rebuilt_static_const Simplify_common Simplify_named_result Symbol.

(* simplify_set_of_closures.mli:30  val simplify_non_lifted_set_of_closures : Downwards_acc.t -> Bound_pattern.t -> Set_of_closures.t -> Alloc_mode.For_allocations.t -> simplify_function_body:Simplify_common.simplify_function_body -> Simplify_named_result.t *)
Parameter simplify_non_lifted_set_of_closures : Downwards_acc.t -> Bound_pattern.t -> Flambda.Set_of_closures.t -> Alloc_mode.For_allocations.t -> Simplify_common.simplify_function_body -> M Simplify_named_result.t.
Extract Inlined Constant simplify_non_lifted_set_of_closures => "Simplify_set_of_closures.simplify_non_lifted_set_of_closures".
(* simplify_set_of_closures.mli:40  val simplify_lifted_sets_of_closures : Downwards_acc.t -> all_sets_of_closures_and_symbols: (Symbol.t Function_slot.Lmap.t * Set_of_closures.t) list -> closure_bound_names_all_sets:Bound_name.t Function_slot.Map.t list -> simplify_function_body:Simplify_common.simplify_function_body -> Bound_static.t * Rebuilt_static_const.Group.t * Downwards_acc.t *)
Parameter simplify_lifted_sets_of_closures : Downwards_acc.t -> list (Function_slot.Lmap.t Symbol.t * Flambda.Set_of_closures.t) -> list (Function_slot.Map.t Bound_name.t) -> Simplify_common.simplify_function_body -> M (tuple3 Bound_static.t Rebuilt_static_const.Group.t Downwards_acc.t).
Extract Inlined Constant simplify_lifted_sets_of_closures => "Simplify_set_of_closures.simplify_lifted_sets_of_closures".
(* simplify_set_of_closures.mli:48  val simplify_static_stub_function : Downwards_acc.t -> Code.t -> all_code:Code.t Code_id.Map.t -> simplify_function_body:Simplify_common.simplify_function_body -> Rebuilt_static_const.t * Downwards_acc.t *)
Parameter simplify_static_stub_function : Downwards_acc.t -> Code.t -> Code_id.Map.t Code.t -> Simplify_common.simplify_function_body -> M (Rebuilt_static_const.t * Downwards_acc.t).
Extract Inlined Constant simplify_static_stub_function => "Simplify_set_of_closures.simplify_static_stub_function".
