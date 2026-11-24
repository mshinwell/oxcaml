(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2022 OCamlPro SAS                                    *)
(*   Copyright 2014--2022 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplify_set_of_closures_context], after its interface
   middle_end/flambda2/simplify/simplify_set_of_closures_context.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Bound_name Code Code_id Downwards_acc Downwards_env Flambda Flambda2_types Function_slot Or_unknown Simplify_common Value_slot Variable_.

(* simplify_set_of_closures_context.mli:24  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Simplify_set_of_closures_context.t".
(* simplify_set_of_closures_context.mli:26  val create : dacc_prior_to_sets:DA.t -> simplify_function_body:Simplify_common.simplify_function_body -> all_sets_of_closures:(Set_of_closures.t * Alloc_mode.For_types.t) list -> closure_bound_names_all_sets:Bound_name.t Function_slot.Map.t list -> value_slot_types_all_sets:T.t Value_slot.Map.t list -> t *)
Parameter create : Downwards_acc.t -> Simplify_common.simplify_function_body -> list (Flambda.Set_of_closures.t * Alloc_mode.For_types.t) -> list (Function_slot.Map.t Bound_name.t) -> list (Value_slot.Map.t Flambda2_types.t) -> M t.
Extract Inlined Constant create => "Simplify_set_of_closures_context.create".
(* simplify_set_of_closures_context.mli:34  val create_for_static_stub : DA.t -> all_code:Code.t Code_id.Map.t -> simplify_function_body:Simplify_common.simplify_function_body -> t *)
Parameter create_for_static_stub : Downwards_acc.t -> Code_id.Map.t Code.t -> Simplify_common.simplify_function_body -> M t.
Extract Inlined Constant create_for_static_stub => "Simplify_set_of_closures_context.create_for_static_stub".
(* simplify_set_of_closures_context.mli:40  val dacc_inside_functions : t -> DA.t *)
Parameter dacc_inside_functions : t -> M Downwards_acc.t.
Extract Inlined Constant dacc_inside_functions => "Simplify_set_of_closures_context.dacc_inside_functions".
(* simplify_set_of_closures_context.mli:42  val dacc_prior_to_sets : t -> DA.t *)
Parameter dacc_prior_to_sets : t -> M Downwards_acc.t.
Extract Inlined Constant dacc_prior_to_sets => "Simplify_set_of_closures_context.dacc_prior_to_sets".
(* simplify_set_of_closures_context.mli:46  val old_to_new_code_ids_all_sets : t -> Code_id.t Code_id.Map.t *)
Parameter old_to_new_code_ids_all_sets : t -> M (Code_id.Map.t Code_id.t).
Extract Inlined Constant old_to_new_code_ids_all_sets => "Simplify_set_of_closures_context.old_to_new_code_ids_all_sets".
(* simplify_set_of_closures_context.mli:48  val closure_bound_names_inside_functions_all_sets : t -> Bound_name.t Function_slot.Map.t list *)
Parameter closure_bound_names_inside_functions_all_sets : t -> M (list (Function_slot.Map.t Bound_name.t)).
Extract Inlined Constant closure_bound_names_inside_functions_all_sets => "Simplify_set_of_closures_context.closure_bound_names_inside_functions_all_sets".
(* simplify_set_of_closures_context.mli:51  val closure_bound_names_inside_functions_exactly_one_set : t -> Bound_name.t Function_slot.Map.t *)
Parameter closure_bound_names_inside_functions_exactly_one_set : t -> M (Function_slot.Map.t Bound_name.t).
Extract Inlined Constant closure_bound_names_inside_functions_exactly_one_set => "Simplify_set_of_closures_context.closure_bound_names_inside_functions_exactly_one_set".
(* simplify_set_of_closures_context.mli:54  val simplify_function_body : t -> Simplify_common.simplify_function_body *)
Parameter simplify_function_body : t -> M Simplify_common.simplify_function_body.
Extract Inlined Constant simplify_function_body => "Simplify_set_of_closures_context.simplify_function_body".
(* simplify_set_of_closures_context.mli:56  val previously_free_depth_variables : t -> Variable.Set.t *)
Parameter previously_free_depth_variables : t -> M Variable_.Set_.t.
Extract Inlined Constant previously_free_depth_variables => "Simplify_set_of_closures_context.previously_free_depth_variables".
(* simplify_set_of_closures_context.mli:58  val function_decl_type : ?new_code_id:Code_id.t -> rec_info:T.t -> Code_id.t -> Function_type.t Or_unknown.t *)
Parameter function_decl_type : option Code_id.t -> Flambda2_types.t -> Code_id.t -> M (Or_unknown.t Flambda2_types.Function_type.t).
Extract Inlined Constant function_decl_type => "(fun x__1 x__2 x__3 -> Simplify_set_of_closures_context.function_decl_type ?new_code_id:x__1 x__2 x__3)".
(* simplify_set_of_closures_context.mli:64  val stub_can_be_simplified : DE.t -> bool *)
Parameter stub_can_be_simplified : Downwards_env.t -> M bool.
Extract Inlined Constant stub_can_be_simplified => "Simplify_set_of_closures_context.stub_can_be_simplified".
(* simplify_set_of_closures_context.mli:66  val single_set_of_size_one : t -> bool *)
Parameter single_set_of_size_one : t -> M bool.
Extract Inlined Constant single_set_of_size_one => "Simplify_set_of_closures_context.single_set_of_size_one".
