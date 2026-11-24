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
Inductive t : Type :=
| Linearly_used_and_inlinable : Bound_parameters.t -> Rebuilt_expr.t -> Name_occurrences.t -> Cost_metrics.t -> t
| Non_inlinable_zero_arity : Or_unknown.t Rebuilt_expr.t -> t
| Non_inlinable_non_zero_arity : Flambda_arity.t_Unarized -> t
| Toplevel_or_function_return_or_exn_continuation : Flambda_arity.t_Unarized -> t
| Invalid : Flambda_arity.t_Unarized -> t.
Extract Inductive t => "Continuation_in_env.t" [ "(fun (x__1, x__2, x__3, x__4) -> (Continuation_in_env.Linearly_used_and_inlinable { params = x__1; handler = x__2; free_names_of_handler = x__3; cost_metrics_of_handler = x__4 } : Continuation_in_env.t))" "(fun x__1 -> (Continuation_in_env.Non_inlinable_zero_arity { handler = x__1 } : Continuation_in_env.t))" "(fun x__1 -> (Continuation_in_env.Non_inlinable_non_zero_arity { arity = x__1 } : Continuation_in_env.t))" "(fun x__1 -> (Continuation_in_env.Toplevel_or_function_return_or_exn_continuation { arity = x__1 } : Continuation_in_env.t))" "(fun x__1 -> (Continuation_in_env.Invalid { arity = x__1 } : Continuation_in_env.t))" ] "(fun f__1 f__2 f__3 f__4 f__5 x__0 -> match (x__0 : Continuation_in_env.t) with Continuation_in_env.Linearly_used_and_inlinable { params = x__1; handler = x__2; free_names_of_handler = x__3; cost_metrics_of_handler = x__4 } -> f__1 x__1 x__2 x__3 x__4 | Continuation_in_env.Non_inlinable_zero_arity { handler = x__1 } -> f__2 x__1 | Continuation_in_env.Non_inlinable_non_zero_arity { arity = x__1 } -> f__3 x__1 | Continuation_in_env.Toplevel_or_function_return_or_exn_continuation { arity = x__1 } -> f__4 x__1 | Continuation_in_env.Invalid { arity = x__1 } -> f__5 x__1)".
(* continuation_in_env.mli:40  val print : Are_rebuilding_terms.t -> Format.formatter -> t -> unit *)
Parameter print : Are_rebuilding_terms.t -> Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Continuation_in_env.print".
(* continuation_in_env.mli:42  val arity : t -> [`Unarized] Flambda_arity.t *)
Parameter arity : t -> M Flambda_arity.t_Unarized.
Extract Inlined Constant arity => "Continuation_in_env.arity".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Continuation_in_env. End Continuation_in_env.
