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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Specialization_cost.v, which follows
   middle_end/flambda2/simplify/specialization_cost.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Port_monad

type reason =
  | Specialization_disabled
  | At_toplevel
  | Contains_static_consts
  | Contains_set_of_closures

type cost =
  { primitives : (Bound_var.t * Flambda_primitive.t) list;
    non_lifted_continuations : Original_handlers.t list
  }

(** val primitives : cost -> (Bound_var.t * Flambda_primitive.t) list **)

let primitives c = c.primitives

(** val non_lifted_continuations : cost -> Original_handlers.t list **)

let non_lifted_continuations c = c.non_lifted_continuations

type t =
  | Can_specialize of cost
  | Cannot_specialize of { reason : reason }

(** val print_reason : Format.formatter -> reason -> unit coq_M **)

let print_reason ppf = function
  | Specialization_disabled -> Format.fprintf ppf "specialization_disabled"
  | At_toplevel -> Format.fprintf ppf "at_top_level"
  | Contains_static_consts -> Format.fprintf ppf "contains_static_consts"
  | Contains_set_of_closures -> Format.fprintf ppf "contains_set_of_closures"

(** val print_prim : Format.formatter -> (Bound_var.t * Flambda_primitive.t) ->
    unit coq_M **)

let print_prim ppf = function
  | bound_var, prim ->
    Format.fprintf ppf "@[<hov 1>(%a %a)@]" Bound_var.print bound_var
      Flambda_primitive.print prim

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  (fun f__1 f__2 x__0 ->
    match (x__0 : t) with
    | Can_specialize x__1 -> f__1 x__1
    | Cannot_specialize { reason = x__1 } -> f__2 x__1)
    (fun c ->
      let { primitives = primitives0;
            non_lifted_continuations = non_lifted_continuations0
          } =
        c
      in
      Format.fprintf ppf
        "@[<hv>(can_specialize@ @[<hv 1>(primitives@ %a)@]@ @[<hv \
         1>(non_lifted_continuations@ %a)@])@]"
        ((fun x__1 x__2 x__3 x__4 ->
           Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
           None print_prim)
        primitives0
        ((fun x__1 x__2 x__3 x__4 ->
           Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)
           None Original_handlers.print)
        non_lifted_continuations0)
    (fun reason0 ->
      Format.fprintf ppf "@[<hv>(cannot_specialize@ @[<hv 1>(reason@ %a)@])@]"
        print_reason reason0)
    t0

(** val cannot_specialize : reason -> t coq_M **)

let cannot_specialize reason0 =
  (fun x__1 -> (Cannot_specialize { reason = x__1 } : t)) reason0

(** val can_specialize : unit -> t coq_M **)

let can_specialize _ =
  if Flambda_features.match_in_match ()
  then Can_specialize { primitives = []; non_lifted_continuations = [] }
  else cannot_specialize Specialization_disabled

(** val update_cost : (cost -> cost coq_M) -> t -> t coq_M **)

let update_cost f res =
  (fun f__1 f__2 x__0 ->
    match (x__0 : t) with
    | Can_specialize x__1 -> f__1 x__1
    | Cannot_specialize { reason = x__1 } -> f__2 x__1)
    (fun cost0 -> Can_specialize (f cost0))
    (fun _ -> res)
    res

(** val add_set_of_closures : Set_of_closures.t -> t -> t coq_M **)

let add_set_of_closures _ _ =
  (fun x__1 -> (Cannot_specialize { reason = x__1 } : t))
    Contains_set_of_closures

(** val add_lifted_set_of_closures : Set_of_closures.t -> t -> t coq_M **)

let add_lifted_set_of_closures _ _ =
  (fun x__1 -> (Cannot_specialize { reason = x__1 } : t))
    Contains_set_of_closures

(** val add_prim : Bound_var.t -> Flambda_primitive.t -> t -> t coq_M **)

let add_prim bound_var prim t0 =
  update_cost
    (fun cost0 ->
      let { primitives = primitives0; non_lifted_continuations = _ } = cost0 in
      let primitives1 = (bound_var, prim) :: primitives0 in
      { primitives = primitives1;
        non_lifted_continuations = cost0.non_lifted_continuations
      })
    t0

(** val add_continuations : bool -> Original_handlers.t -> t -> t coq_M **)

let add_continuations can_be_lifted0 handlers t0 =
  if can_be_lifted0
  then t0
  else
    update_cost
      (fun cost0 ->
        let { primitives = _;
              non_lifted_continuations = non_lifted_continuations0
            } =
          cost0
        in
        let non_lifted_continuations1 = handlers :: non_lifted_continuations0 in
        { primitives = cost0.primitives;
          non_lifted_continuations = non_lifted_continuations1
        })
      t0

(** val repeat : int -> 'a1 -> ('a1 -> 'a1 coq_M) -> 'a1 coq_M **)

let rec repeat n acc f = if n <= 0 then acc else repeat (n - 1) (f acc) f

(** val cost_metrics : Flambda2_types.Typing_env.t -> Switch_expr.t ->
    Apply_cont_rewrite_id.t Flambda2_types.Join_analysis.t ->
    Apply_cont_rewrite_id.Set.t -> Apply_cont_rewrite_id.Set.t -> cost ->
    Cost_metrics.t coq_M **)

let cost_metrics typing_env switch join_analysis specialized generic cost0 =
  let machine_width = Flambda2_types.Typing_env.machine_width typing_env in
  let n_specialized = Apply_cont_rewrite_id.Set.cardinal specialized in
  let n_generic = Apply_cont_rewrite_id.Set.cardinal generic in
  let n_total = n_specialized + if n_generic = 0 then 0 else 1 in
  let metrics =
    if n_generic = 0
    then
      let code_size =
        List.fold_left
          (fun acc pat ->
            let _, primitive = pat in
            Code_size.( + ) acc (Code_size.prim machine_width primitive))
          (Code_size.switch switch) cost0.primitives
      in
      Cost_metrics.from_size (Code_size.( - ) Code_size.zero code_size)
    else Cost_metrics.zero
  in
  let metrics0 =
    repeat n_specialized metrics
      (Cost_metrics.notify_removed Removed_operations.branch)
  in
  let metrics1 =
    List.fold_left
      (fun metrics1 pat ->
        let bound_var, prim = pat in
        let simple = Simple.var (Bound_var.var bound_var) in
        let disappears, stays =
          match
            Flambda2_types.Join_analysis.simple_refined_at_join join_analysis
              typing_env simple
          with
          | Not_refined_at_join -> 0, n_total
          | Invariant_in_all_uses _ -> 0, 0
          | Variable_refined_at_these_uses var_analysis ->
            Flambda2_types.Join_analysis.Variable_refined_at_join
            .fold_values_at_uses
              (fun id value pat0 ->
                let disappears, stays = pat0 in
                if Apply_cont_rewrite_id.Set.mem id specialized
                then
                  match value with
                  | Known _ -> disappears + 1, stays
                  | Unknown -> disappears, stays + 1
                else disappears, stays + 1)
              var_analysis (0, 0)
        in
        let metrics2 =
          repeat disappears metrics1
            (Cost_metrics.notify_removed (Removed_operations.prim prim))
        in
        let metrics3 =
          repeat stays metrics2
            (Cost_metrics.notify_added (Code_size.prim machine_width prim))
        in
        metrics3)
      metrics0 cost0.primitives
  in
  let handler_metrics = fun _ -> Cost_metrics.from_size (Code_size.of_int 5) in
  let metrics2 =
    List.fold_left
      (fun metrics2 handlers ->
        (fun f__1 f__2 x__0 ->
          match (x__0 : Original_handlers.t) with
          | Original_handlers.Recursive
              { invariant_params = x__1;
                lifted_params = x__2;
                continuation_handlers = x__3;
                can_be_lifted = x__4
              } ->
            f__1 x__1 x__2 x__3 x__4
          | Original_handlers.Non_recursive x__1 -> f__2 x__1)
          (fun _ _ continuation_handlers _ ->
            Continuation.Lmap.fold
              (fun _ one_rec_handler metrics3 ->
                let handler0 = one_rec_handler.One_recursive_handler.handler in
                Cost_metrics.( + ) metrics3 (handler_metrics handler0))
              continuation_handlers metrics2)
          (fun t0 ->
            let { Non_recursive_handler.cont = _;
                  Non_recursive_handler.params = _;
                  Non_recursive_handler.lifted_params = _;
                  Non_recursive_handler.handler = handler0;
                  Non_recursive_handler.is_exn_handler = _;
                  Non_recursive_handler.can_be_lifted = _;
                  Non_recursive_handler.is_cold = _
                } =
              t0
            in
            Cost_metrics.( + ) metrics2 (handler_metrics handler0))
          handlers)
      metrics1 cost0.non_lifted_continuations
  in
  metrics2
