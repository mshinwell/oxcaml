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
   Simplify uses of the compiler's module [Simplified_named], after its interface
   middle_end/flambda2/simplify/simplified_named.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Bound_pattern Code_id Cost_metrics Debuginfo Flambda Flambda_primitive Format Name_occurrences Rec_info_expr Simple Target_system.

(* simplified_named.mli:21  type simplified_named = private | Simple of Simple.t | Prim of Flambda_primitive.t * Debuginfo.t | Set_of_closures of Set_of_closures.t * Alloc_mode.For_allocations.t | Rec_info of Rec_info_expr.t *)
Inductive simplified_named : Type :=
| Simple : Simple.t -> simplified_named
| Prim : Flambda_primitive.t -> Debuginfo.t -> simplified_named
| Set_of_closures : Flambda.Import_.Set_of_closures.t -> Alloc_mode.For_allocations.t -> simplified_named
| Rec_info : Rec_info_expr.t -> simplified_named.
(* simplified_named.mli:27  val to_named : simplified_named -> Named.t *)
Parameter to_named : simplified_named -> M Flambda.Import_.Named.t.
Extract Inlined Constant to_named => "Simplified_named.to_named".
(* simplified_named.mli:29  type t = private { named : simplified_named; cost_metrics : Cost_metrics.t; free_names : Name_occurrences.t } *)
Record t : Type := { named : simplified_named; cost_metrics : Cost_metrics.t; free_names : Name_occurrences.t }.
(* simplified_named.mli:38  val create : machine_width:Target_system.Machine_width.t -> Named.t -> t *)
Parameter create : Target_system.Machine_width.t -> Flambda.Import_.Named.t -> M t.
Extract Inlined Constant create => "Simplified_named.create".
(* simplified_named.mli:41  val create_with_known_free_names : machine_width:Target_system.Machine_width.t -> find_code_characteristics:(Code_id.t -> Cost_metrics.code_characteristics) -> Named.t -> free_names:Name_occurrences.t -> t *)
Parameter create_with_known_free_names : Target_system.Machine_width.t -> (Code_id.t -> M Cost_metrics.code_characteristics) -> Flambda.Import_.Named.t -> Name_occurrences.t -> M t.
Extract Inlined Constant create_with_known_free_names => "Simplified_named.create_with_known_free_names".
(* simplified_named.mli:48  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Simplified_named.print".
(* simplified_named.mli:50  val cost_metrics : t -> Cost_metrics.t *)
Parameter cost_metrics_ : t -> M Cost_metrics.t.
Extract Inlined Constant cost_metrics_ => "Simplified_named.cost_metrics".
(* simplified_named.mli:52  val update_cost_metrics : Cost_metrics.t -> t -> t *)
Parameter update_cost_metrics : Cost_metrics.t -> t -> M t.
Extract Inlined Constant update_cost_metrics => "Simplified_named.update_cost_metrics".
(* simplified_named.mli:54  type 'a or_rewritten = | Simplified of 'a | Rewritten of (body:Flambda.Expr.t -> Flambda.Expr.t) *)
Inductive or_rewritten (A : Type) : Type :=
| Simplified : A -> or_rewritten A
| Rewritten : (Flambda.Expr.t -> M Flambda.Expr.t) -> or_rewritten A.
Arguments Simplified {A}.
Arguments Rewritten {A}.
(* simplified_named.mli:58  type binding_to_place = | Keep_binding of { let_bound : Bound_pattern.t; simplified_defining_expr : t; original_defining_expr : Named.t option } | Delete_binding of { original_defining_expr : Named.t option } *)
Record keep_binding_payload_ : Type := { let_bound : Bound_pattern.t; simplified_defining_expr : t; original_defining_expr : option Flambda.Import_.Named.t }.
(* The inline record of [Delete_binding]: abstract (a name of its fields is taken, or it holds the type); [mk_Delete_binding] makes one, [match_binding_to_place] reads it. *)
Parameter delete_binding_payload_ : Type.
Inductive binding_to_place : Type :=
| Keep_binding : keep_binding_payload_ -> binding_to_place
| Delete_binding : delete_binding_payload_ -> binding_to_place.
Parameter mk_Keep_binding : Bound_pattern.t -> t -> option Flambda.Import_.Named.t -> binding_to_place.
Extract Inlined Constant mk_Keep_binding => "(fun x__1 x__2 x__3 -> Simplified_named.Keep_binding { let_bound = x__1; simplified_defining_expr = x__2; original_defining_expr = x__3 })".
Parameter mk_Delete_binding : option Flambda.Import_.Named.t -> binding_to_place.
Extract Inlined Constant mk_Delete_binding => "(fun x__1 -> Simplified_named.Delete_binding { original_defining_expr = x__1 })".
Parameter match_binding_to_place : forall {Res : Type}, binding_to_place -> (Bound_pattern.t -> t -> option Flambda.Import_.Named.t -> M Res) -> (option Flambda.Import_.Named.t -> M Res) -> M Res.
Extract Inlined Constant match_binding_to_place => "(fun x__0 f__1 f__2 -> match x__0 with Simplified_named.Keep_binding { let_bound = x__1; simplified_defining_expr = x__2; original_defining_expr = x__3 } -> f__1 x__1 x__2 x__3 | Simplified_named.Delete_binding { original_defining_expr = x__1 } -> f__2 x__1)".
