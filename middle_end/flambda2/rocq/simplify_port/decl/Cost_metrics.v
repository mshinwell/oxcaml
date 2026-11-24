(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Cost_metrics], after its interface
   middle_end/flambda2/terms/cost_metrics.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Code_size Format Inlining_arguments Removed_operations Set_of_closures Stdlib_.

(* cost_metrics.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Cost_metrics.t".
(* cost_metrics.mli:19  val zero : t *)
Parameter zero : t.
Extract Inlined Constant zero => "Cost_metrics.zero".
(* cost_metrics.mli:21  val from_size : Code_size.t -> t *)
Parameter from_size : Code_size.t -> M t.
Extract Inlined Constant from_size => "Cost_metrics.from_size".
(* cost_metrics.mli:23  val size : t -> Code_size.t *)
Parameter size : t -> M Code_size.t.
Extract Inlined Constant size => "Cost_metrics.size".
(* cost_metrics.mli:25  val removed : t -> Removed_operations.t *)
Parameter removed : t -> M Removed_operations.t.
Extract Inlined Constant removed => "Cost_metrics.removed".
(* cost_metrics.mli:27  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Cost_metrics.print".
(* cost_metrics.mli:29  val ( + ) : t -> t -> t *)
Parameter op_plus : t -> t -> M t.
Extract Inlined Constant op_plus => "Cost_metrics.( + )".
(* cost_metrics.mli:31  type code_characteristics = { cost_metrics : t; function_slot_size : int } *)
Record code_characteristics : Type := { cost_metrics : t; function_slot_size : int }.
(* cost_metrics.mli:36  val set_of_closures : find_code_characteristics:(Code_id.t -> code_characteristics) -> Set_of_closures.t -> t *)
Parameter set_of_closures : (Code_id.t -> M code_characteristics) -> Set_of_closures.t -> M t.
Extract Inlined Constant set_of_closures => "Cost_metrics.set_of_closures".
(* cost_metrics.mli:41  val increase_due_to_let_expr : is_phantom:bool -> cost_metrics_of_defining_expr:t -> t *)
Parameter increase_due_to_let_expr : bool -> t -> M t.
Extract Inlined Constant increase_due_to_let_expr => "Cost_metrics.increase_due_to_let_expr".
(* cost_metrics.mli:44  val increase_due_to_let_cont_non_recursive : cost_metrics_of_handler:t -> t *)
Parameter increase_due_to_let_cont_non_recursive : t -> M t.
Extract Inlined Constant increase_due_to_let_cont_non_recursive => "Cost_metrics.increase_due_to_let_cont_non_recursive".
(* cost_metrics.mli:46  val increase_due_to_let_cont_recursive : cost_metrics_of_handlers:t -> t *)
Parameter increase_due_to_let_cont_recursive : t -> M t.
Extract Inlined Constant increase_due_to_let_cont_recursive => "Cost_metrics.increase_due_to_let_cont_recursive".
(* cost_metrics.mli:48  val notify_added : code_size:Code_size.t -> t -> t *)
Parameter notify_added : Code_size.t -> t -> M t.
Extract Inlined Constant notify_added => "Cost_metrics.notify_added".
(* cost_metrics.mli:50  val notify_removed : operation:Removed_operations.t -> t -> t *)
Parameter notify_removed : Removed_operations.t -> t -> M t.
Extract Inlined Constant notify_removed => "Cost_metrics.notify_removed".
(* cost_metrics.mli:52  val evaluate : args:Inlining_arguments.t -> t -> float *)
Parameter evaluate : Inlining_arguments.t -> t -> M Stdlib_.float_.
Extract Inlined Constant evaluate => "Cost_metrics.evaluate".
