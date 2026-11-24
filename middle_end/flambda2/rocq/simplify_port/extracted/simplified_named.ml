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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Simplified_named.v, which follows
   middle_end/flambda2/simplify/simplified_named.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Flambda.Import
open Port_monad

type simplified_named =
  | Simple of Simple.t
  | Prim of Flambda_primitive.t * Debuginfo.t
  | Set_of_closures of
      Flambda.Import.Set_of_closures.t * Alloc_mode.For_allocations.t
  | Rec_info of Rec_info_expr.t

(** val to_named : simplified_named -> Flambda.Import.Named.t coq_M **)

let to_named = function
  | Simple simple -> Flambda.Import.Named.create_simple simple
  | Prim (prim, dbg) -> Flambda.Import.Named.create_prim prim dbg
  | Set_of_closures (set, alloc_mode) ->
    Flambda.Import.Named.create_set_of_closures alloc_mode set
  | Rec_info rec_info_expr -> Flambda.Import.Named.create_rec_info rec_info_expr

type t =
  { named : simplified_named;
    cost_metrics : Cost_metrics.t;
    free_names : Name_occurrences.t
  }

(** val named : t -> simplified_named **)

let named t0 = t0.named

(** val cost_metrics : t -> Cost_metrics.t **)

let cost_metrics t0 = t0.cost_metrics

(** val free_names : t -> Name_occurrences.t **)

let free_names t0 = t0.free_names

(** val create : Target_system.Machine_width.t -> Flambda.Import.Named.t -> t
    coq_M **)

let create machine_width named0 =
  let simplified_named0, cost_metrics0 =
    match named0 with
    | Flambda.Simple simple ->
      Simple simple, Cost_metrics.from_size (Code_size.simple simple)
    | Flambda.Prim (prim, dbg) ->
      ( Prim (prim, dbg),
        Cost_metrics.from_size (Code_size.prim machine_width prim) )
    | Flambda.Set_of_closures (_, _) ->
      Misc.fatal_errorf
        "Cannot use [Simplified_named.create] on [Set_of_closures];@ use \
         [create_with_known_free_names] instead:@ %a"
        Flambda.Import.Named.print named0
    | Flambda.Static_consts _ ->
      Misc.fatal_errorf
        "Cannot create [Simplified_named] from [Static_consts];@ use the \
         lifted constant infrastructure instead:@ %a"
        Flambda.Import.Named.print named0
    | Flambda.Rec_info rec_info_expr ->
      Rec_info rec_info_expr, Cost_metrics.zero
  in
  { named = simplified_named0;
    cost_metrics = cost_metrics0;
    free_names = Flambda.Import.Named.free_names named0
  }

(** val create_with_known_free_names : Target_system.Machine_width.t ->
    (Code_id.t -> Cost_metrics.code_characteristics coq_M) ->
    Flambda.Import.Named.t -> Name_occurrences.t -> t coq_M **)

let create_with_known_free_names machine_width find_code_characteristics named0
    free_names0 =
  let simplified_named0, cost_metrics0 =
    match named0 with
    | Flambda.Simple simple ->
      Simple simple, Cost_metrics.from_size (Code_size.simple simple)
    | Flambda.Prim (prim, dbg) ->
      ( Prim (prim, dbg),
        Cost_metrics.from_size (Code_size.prim machine_width prim) )
    | Flambda.Set_of_closures (set, alloc_mode) ->
      ( Set_of_closures (set, alloc_mode),
        Cost_metrics.set_of_closures find_code_characteristics set )
    | Flambda.Static_consts _ ->
      Misc.fatal_errorf
        "Cannot create [Simplified_named] from [Static_consts];@ use the \
         lifted constant infrastructure instead:@ %a"
        Flambda.Import.Named.print named0
    | Flambda.Rec_info rec_info_expr ->
      Rec_info rec_info_expr, Cost_metrics.zero
  in
  { named = simplified_named0;
    cost_metrics = cost_metrics0;
    free_names = free_names0
  }

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf pat =
  let { named = named0; cost_metrics = _; free_names = _ } = pat in
  Flambda.Import.Named.print ppf (to_named named0)

(** val update_cost_metrics : Cost_metrics.t -> t -> t coq_M **)

let update_cost_metrics cost_metrics0 t0 =
  (fun t cost_metrics -> { t with cost_metrics }) t0 cost_metrics0

type 'a or_rewritten =
  | Simplified of 'a
  | Rewritten of (Flambda.Expr.t -> Flambda.Expr.t coq_M)

type binding_to_place =
  | Keep_binding of
      { let_bound : Bound_pattern.t;
        simplified_defining_expr : t;
        original_defining_expr : Named.t option
      }
  | Delete_binding of { original_defining_expr : Named.t option }
