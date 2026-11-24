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
   Simplify uses of the compiler's module [Continuation_in_env], after its interface
   middle_end/flambda2/simplify/continuation_in_env.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Are_rebuilding_terms Bound_parameters Cost_metrics Flambda_arity Format Name_occurrences Or_unknown Rebuilt_expr.

(* continuation_in_env.mli:17  type t = | Linearly_used_and_inlinable of { params : Bound_parameters.t; ( ** To avoid re-opening name abstractions, we store the opened parameters and handler here. * ) handler : Rebuilt_expr.t; ( ** [free_names_of_handler] includes entries for any occurrences of the [params] in the [handler]. * ) free_names_of_handler : Name_occurrences.t; cost_metrics_of_handler : Cost_metrics.t } | Non_inli... *)
(* PORT-GAP(type): the name of the field [handler] is taken in Rocq: abstract, with a maker for each constructor and one eliminator. *)
Parameter t : Type.
Extract Inlined Constant t => "Continuation_in_env.t".
Parameter mk_Linearly_used_and_inlinable : Bound_parameters.t -> Rebuilt_expr.t -> Name_occurrences.t -> Cost_metrics.t -> t.
Extract Inlined Constant mk_Linearly_used_and_inlinable => "(fun x__1 x__2 x__3 x__4 -> Continuation_in_env.Linearly_used_and_inlinable { params = x__1; handler = x__2; free_names_of_handler = x__3; cost_metrics_of_handler = x__4 })".
Parameter mk_Non_inlinable_zero_arity : Or_unknown.t Rebuilt_expr.t -> t.
Extract Inlined Constant mk_Non_inlinable_zero_arity => "(fun x__1 -> Continuation_in_env.Non_inlinable_zero_arity { handler = x__1 })".
Parameter mk_Non_inlinable_non_zero_arity : Flambda_arity.t -> t.
Extract Inlined Constant mk_Non_inlinable_non_zero_arity => "(fun x__1 -> Continuation_in_env.Non_inlinable_non_zero_arity { arity = x__1 })".
Parameter mk_Toplevel_or_function_return_or_exn_continuation : Flambda_arity.t -> t.
Extract Inlined Constant mk_Toplevel_or_function_return_or_exn_continuation => "(fun x__1 -> Continuation_in_env.Toplevel_or_function_return_or_exn_continuation { arity = x__1 })".
Parameter mk_Invalid : Flambda_arity.t -> t.
Extract Inlined Constant mk_Invalid => "(fun x__1 -> Continuation_in_env.Invalid { arity = x__1 })".
Parameter match_t : forall {Res : Type}, t -> (Bound_parameters.t -> Rebuilt_expr.t -> Name_occurrences.t -> Cost_metrics.t -> M Res) -> (Or_unknown.t Rebuilt_expr.t -> M Res) -> (Flambda_arity.t -> M Res) -> (Flambda_arity.t -> M Res) -> (Flambda_arity.t -> M Res) -> M Res.
Extract Inlined Constant match_t => "(fun x__0 f__1 f__2 f__3 f__4 f__5 -> match x__0 with Continuation_in_env.Linearly_used_and_inlinable { params = x__1; handler = x__2; free_names_of_handler = x__3; cost_metrics_of_handler = x__4 } -> f__1 x__1 x__2 x__3 x__4 | Continuation_in_env.Non_inlinable_zero_arity { handler = x__1 } -> f__2 x__1 | Continuation_in_env.Non_inlinable_non_zero_arity { arity = x__1 } -> f__3 x__1 | Continuation_in_env.Toplevel_or_function_return_or_exn_continuation { arity = x__1 } -> f__4 x__1 | Continuation_in_env.Invalid { arity = x__1 } -> f__5 x__1)".
(* continuation_in_env.mli:40  val print : Are_rebuilding_terms.t -> Format.formatter -> t -> unit *)
Parameter print : Are_rebuilding_terms.t -> Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Continuation_in_env.print".
(* continuation_in_env.mli:42  val arity : t -> [`Unarized] Flambda_arity.t *)
Parameter arity : t -> M Flambda_arity.t.
Extract Inlined Constant arity => "Continuation_in_env.arity".
