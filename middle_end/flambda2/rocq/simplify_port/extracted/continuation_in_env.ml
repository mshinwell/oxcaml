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
   middle_end/flambda2/rocq/simplify_port/Continuation_in_env.v, which follows
   middle_end/flambda2/simplify/continuation_in_env.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

type t =
  | Linearly_used_and_inlinable of
      { params : Bound_parameters.t;
        handler : Rebuilt_expr.t;
        free_names_of_handler : Name_occurrences.t;
        cost_metrics_of_handler : Cost_metrics.t
      }
  | Non_inlinable_zero_arity of { handler : Rebuilt_expr.t Or_unknown.t }
  | Non_inlinable_non_zero_arity of { arity : [`Unarized] Flambda_arity.t }
  | Toplevel_or_function_return_or_exn_continuation of
      { arity : [`Unarized] Flambda_arity.t }
  | Invalid of { arity : [`Unarized] Flambda_arity.t }

open Port_monad

(** val print : Are_rebuilding_terms.t -> Format.formatter -> t -> unit coq_M **)

let print are_rebuilding_terms ppf t0 =
  (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
    match (x__0 : t) with
    | Linearly_used_and_inlinable
        { params = x__1;
          handler = x__2;
          free_names_of_handler = x__3;
          cost_metrics_of_handler = x__4
        } ->
      f__1 x__1 x__2 x__3 x__4
    | Non_inlinable_zero_arity { handler = x__1 } -> f__2 x__1
    | Non_inlinable_non_zero_arity { arity = x__1 } -> f__3 x__1
    | Toplevel_or_function_return_or_exn_continuation { arity = x__1 } ->
      f__4 x__1
    | Invalid { arity = x__1 } -> f__5 x__1)
    (fun params handler free_names_of_handler cost_metrics_of_handler ->
      Format.fprintf ppf
        "@[<hov 1>(Linearly_used_and_inlinable@ @[<hov 1>(params@ %a)@]@ \
         @[<hov 1>(handler@ %a)@]@ @[<hov 1>(free_names_of_handler@ %a)@]@ \
         @[<hov 1>(cost_metrics_of_handler@ %a)@])@]"
        Bound_parameters.print params
        (Rebuilt_expr.print are_rebuilding_terms)
        handler Name_occurrences.print free_names_of_handler Cost_metrics.print
        cost_metrics_of_handler)
    (fun handler ->
      Format.fprintf ppf
        "@[<hov 1>(Non_inlinable_zero_arity@ @[<hov 1>(handler@ %a)@])@]"
        (Or_unknown.print (Rebuilt_expr.print are_rebuilding_terms))
        handler)
    (fun arity0 ->
      Format.fprintf ppf
        "@[<hov 1>(Non_inlinable_non_zero_arity@ @[<hov 1>(arity@ %a)@])@]"
        Flambda_arity.print arity0)
    (fun arity0 ->
      Format.fprintf ppf
        "@[<hov 1>(Toplevel_or_function_return_or_exn_continuation@ @[<hov \
         1>(arity@ %a)@])@]"
        Flambda_arity.print arity0)
    (fun arity0 ->
      Format.fprintf ppf "@[<hov 1>(Invalid@ @[<hov 1>(arity@ %a)@])@]"
        Flambda_arity.print arity0)
    t0

(** val arity : t -> (_) Flambda_arity.t coq_M **)

let arity t0 =
  (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
    match (x__0 : t) with
    | Linearly_used_and_inlinable
        { params = x__1;
          handler = x__2;
          free_names_of_handler = x__3;
          cost_metrics_of_handler = x__4
        } ->
      f__1 x__1 x__2 x__3 x__4
    | Non_inlinable_zero_arity { handler = x__1 } -> f__2 x__1
    | Non_inlinable_non_zero_arity { arity = x__1 } -> f__3 x__1
    | Toplevel_or_function_return_or_exn_continuation { arity = x__1 } ->
      f__4 x__1
    | Invalid { arity = x__1 } -> f__5 x__1)
    (fun params _ _ _ -> Bound_parameters.arity params)
    (fun _ -> Flambda_arity.nullary)
    (fun arity0 -> arity0)
    (fun arity0 -> arity0)
    (fun arity0 -> arity0)
    t0
