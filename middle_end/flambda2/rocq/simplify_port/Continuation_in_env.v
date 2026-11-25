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

(* This file follows middle_end/flambda2/simplify/continuation_in_env.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN], the type kept as OCaml text) is that of GUIDE.md. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Are_rebuilding_terms Bound_parameters
  Cost_metrics Flambda_arity Format Name_occurrences Or_unknown Rebuilt_expr.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17-28. The type is the compiler's text: its constructors have inline
   records, which Rocq cannot print. *)
(*OCAML
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
OCAML*)

(* 17-28. The fields of the inline records are taken by place, as in
   decl/Continuation_in_env.v: a constructor is built by a function of the
   tuple of its fields, and the type is matched by one function for each
   constructor. *)
Inductive t : Type :=
| Linearly_used_and_inlinable :
    Bound_parameters.t -> Rebuilt_expr.t -> Name_occurrences.t ->
    Cost_metrics.t -> t
| Non_inlinable_zero_arity : Or_unknown.t Rebuilt_expr.t -> t
| Non_inlinable_non_zero_arity : Flambda_arity.t -> t
| Toplevel_or_function_return_or_exn_continuation : Flambda_arity.t -> t
| Invalid : Flambda_arity.t -> t.
Extract Inductive t => "t" [ "(fun (x__1, x__2, x__3, x__4) -> (Linearly_used_and_inlinable { params = x__1; handler = x__2; free_names_of_handler = x__3; cost_metrics_of_handler = x__4 } : t))" "(fun x__1 -> (Non_inlinable_zero_arity { handler = x__1 } : t))" "(fun x__1 -> (Non_inlinable_non_zero_arity { arity = x__1 } : t))" "(fun x__1 -> (Toplevel_or_function_return_or_exn_continuation { arity = x__1 } : t))" "(fun x__1 -> (Invalid { arity = x__1 } : t))" ] "(fun f__1 f__2 f__3 f__4 f__5 x__0 -> match (x__0 : t) with Linearly_used_and_inlinable { params = x__1; handler = x__2; free_names_of_handler = x__3; cost_metrics_of_handler = x__4 } -> f__1 x__1 x__2 x__3 x__4 | Non_inlinable_zero_arity { handler = x__1 } -> f__2 x__1 | Non_inlinable_non_zero_arity { arity = x__1 } -> f__3 x__1 | Toplevel_or_function_return_or_exn_continuation { arity = x__1 } -> f__4 x__1 | Invalid { arity = x__1 } -> f__5 x__1)".

(* 30-64 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept. *)
Definition print (are_rebuilding_terms : Are_rebuilding_terms.t)
    (ppf : Format.formatter) (t : Continuation_in_env.t) : M unit :=
  match t with
  | Linearly_used_and_inlinable params handler free_names_of_handler
      cost_metrics_of_handler =>
    let! tmp1 := papp1 Rebuilt_expr.print are_rebuilding_terms in
    Format.fprintf8 ppf
      "@[<hov 1>(Linearly_used_and_inlinable@ @[<hov 1>(params@ %a)@]@ @[<hov 1>(handler@ %a)@]@ @[<hov 1>(free_names_of_handler@ %a)@]@ @[<hov 1>(cost_metrics_of_handler@ %a)@])@]"
      Bound_parameters.print params tmp1 handler Name_occurrences.print
      free_names_of_handler Cost_metrics.print cost_metrics_of_handler
  | Non_inlinable_zero_arity handler =>
    let! tmp1 := papp1 Rebuilt_expr.print are_rebuilding_terms in
    let! tmp2 := papp1 Or_unknown.print tmp1 in
    Format.fprintf2 ppf
      "@[<hov 1>(Non_inlinable_zero_arity@ @[<hov 1>(handler@ %a)@])@]" tmp2
      handler
  | Non_inlinable_non_zero_arity arity =>
    Format.fprintf2 ppf
      "@[<hov 1>(Non_inlinable_non_zero_arity@ @[<hov 1>(arity@ %a)@])@]"
      Flambda_arity.print arity
  | Toplevel_or_function_return_or_exn_continuation arity =>
    Format.fprintf2 ppf
      "@[<hov 1>(Toplevel_or_function_return_or_exn_continuation@ @[<hov 1>(arity@ %a)@])@]"
      Flambda_arity.print arity
  | Invalid arity =>
    Format.fprintf2 ppf "@[<hov 1>(Invalid@ @[<hov 1>(arity@ %a)@])@]"
      Flambda_arity.print arity
  end.

(* 66-79 *)
Definition arity (t : Continuation_in_env.t) : M Flambda_arity.t :=
  match t with
  | Linearly_used_and_inlinable params _ _ _ => Bound_parameters.arity params
  | Non_inlinable_zero_arity _ => ret Flambda_arity.nullary
  | Non_inlinable_non_zero_arity arity
  | Toplevel_or_function_return_or_exn_continuation arity
  | Invalid arity =>
    ret arity
  end.
