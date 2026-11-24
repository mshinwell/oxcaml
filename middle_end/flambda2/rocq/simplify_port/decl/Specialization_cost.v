(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Specialization_cost], after its interface
   middle_end/flambda2/simplify/specialization_cost.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_var Cost_metrics Flambda2_types Flambda_primitive Format Original_handlers Set_of_closures Switch_expr.

(* specialization_cost.mli:47  type reason = | Specialization_disabled | At_toplevel | Contains_static_consts | Contains_set_of_closures *)
Inductive reason : Type :=
| Specialization_disabled : reason
| At_toplevel : reason
| Contains_static_consts : reason
| Contains_set_of_closures : reason.
Extract Inductive reason => "Specialization_cost.reason" [ "Specialization_cost.Specialization_disabled" "Specialization_cost.At_toplevel" "Specialization_cost.Contains_static_consts" "Specialization_cost.Contains_set_of_closures" ].
(* specialization_cost.mli:53  type cost *)
Parameter cost : Type.
Extract Inlined Constant cost => "Specialization_cost.cost".
(* specialization_cost.mli:56  type t = private | Can_specialize of cost | Cannot_specialize of { reason : reason } *)
Inductive t : Type :=
| Can_specialize : cost -> t
| Cannot_specialize : reason -> t.
Extract Inductive t => "Specialization_cost.t" [ "Specialization_cost.Can_specialize" "(fun x__1 -> (Specialization_cost.Cannot_specialize { reason = x__1 } : Specialization_cost.t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Specialization_cost.t) with Specialization_cost.Can_specialize x__1 -> f__1 x__1 | Specialization_cost.Cannot_specialize { reason = x__1 } -> f__2 x__1)".
(* specialization_cost.mli:62  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Specialization_cost.print".
(* specialization_cost.mli:67  val can_specialize : unit -> t *)
Parameter can_specialize : unit -> M t.
Extract Inlined Constant can_specialize => "Specialization_cost.can_specialize".
(* specialization_cost.mli:70  val cannot_specialize : reason -> t *)
Parameter cannot_specialize : reason -> M t.
Extract Inlined Constant cannot_specialize => "Specialization_cost.cannot_specialize".
(* specialization_cost.mli:75  val add_prim : Bound_var.t -> Flambda_primitive.t -> t -> t *)
Parameter add_prim : Bound_var.t -> Flambda_primitive.t -> t -> M t.
Extract Inlined Constant add_prim => "Specialization_cost.add_prim".
(* specialization_cost.mli:77  val add_continuations : can_be_lifted:bool -> Original_handlers.t -> t -> t *)
Parameter add_continuations : bool -> Original_handlers.t -> t -> M t.
Extract Inlined Constant add_continuations => "Specialization_cost.add_continuations".
(* specialization_cost.mli:81  val add_set_of_closures : Set_of_closures.t -> t -> t *)
Parameter add_set_of_closures : Set_of_closures.t -> t -> M t.
Extract Inlined Constant add_set_of_closures => "Specialization_cost.add_set_of_closures".
(* specialization_cost.mli:83  val add_lifted_set_of_closures : Set_of_closures.t -> t -> t *)
Parameter add_lifted_set_of_closures : Set_of_closures.t -> t -> M t.
Extract Inlined Constant add_lifted_set_of_closures => "Specialization_cost.add_lifted_set_of_closures".
(* specialization_cost.mli:87  val cost_metrics : Typing_env.t -> switch:Switch_expr.t -> join_analysis:Apply_cont_rewrite_id.t Join_analysis.t -> specialized:Apply_cont_rewrite_id.Set.t -> generic:Apply_cont_rewrite_id.Set.t -> cost -> Cost_metrics.t *)
Parameter cost_metrics : Flambda2_types.Typing_env.t -> Switch_expr.t -> Flambda2_types.Join_analysis.t Apply_cont_rewrite_id.t -> Apply_cont_rewrite_id.Set_.t -> Apply_cont_rewrite_id.Set_.t -> cost -> M Cost_metrics.t.
Extract Inlined Constant cost_metrics => "Specialization_cost.cost_metrics".
