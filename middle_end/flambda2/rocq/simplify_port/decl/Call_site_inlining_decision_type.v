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
   Simplify uses of the compiler's module [Call_site_inlining_decision_type], after its interface
   middle_end/flambda2/simplify_shared/call_site_inlining_decision_type.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* call_site_inlining_decision_type.mli:20  type t = | Missing_code | Definition_says_not_to_inline | In_a_stub | Doing_speculative_inlining | Argument_types_not_useful | Unrolling_depth_exceeded | Max_inlining_depth_exceeded | Recursion_depth_exceeded | Never_inlined_attribute | Forward_inlined_attribute_but_nothing_to_forward | Speculatively_not_inline of { cost_metrics : Cost_metrics.t; evaluated_to : float; threshold : float; is_a_fu... *)
Parameter t : Type.
Extract Inlined Constant t => "Call_site_inlining_decision_type.t".
