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
From SimplifyPort.decl Require Cost_metrics Format Stdlib_.

(* call_site_inlining_decision_type.mli:20  type t = | Missing_code | Definition_says_not_to_inline | In_a_stub | Doing_speculative_inlining | Argument_types_not_useful | Unrolling_depth_exceeded | Max_inlining_depth_exceeded | Recursion_depth_exceeded | Never_inlined_attribute | Forward_inlined_attribute_but_nothing_to_forward | Speculatively_not_inline of { cost_metrics : Cost_metrics.t; evaluated_to : float; threshold : float; is_a_fu... *)
Record speculatively_not_inline_payload_ : Type := { cost_metrics : Cost_metrics.t; evaluated_to : Stdlib_.float_; threshold : Stdlib_.float_; is_a_functor : bool }.
Record definition_says_inline_payload_ : Type := { was_inline_always : bool }.
Inductive t : Type :=
| Missing_code : t
| Definition_says_not_to_inline : t
| In_a_stub : t
| Doing_speculative_inlining : t
| Argument_types_not_useful : t
| Unrolling_depth_exceeded : t
| Max_inlining_depth_exceeded : t
| Recursion_depth_exceeded : t
| Never_inlined_attribute : t
| Forward_inlined_attribute_but_nothing_to_forward : t
| Speculatively_not_inline : speculatively_not_inline_payload_ -> t
| Attribute_always : t
| Replay_history_says_must_inline : t -> t
| Begin_unrolling : int -> t
| Continue_unrolling : t
| Definition_says_inline : definition_says_inline_payload_ -> t
| Speculatively_inline : speculatively_not_inline_payload_ -> t
| Jsir_inlining_disabled : t.
(* call_site_inlining_decision_type.mli:50  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Call_site_inlining_decision_type.print".
(* call_site_inlining_decision_type.mli:54  type can_inline = private | Do_not_inline of { erase_attribute_if_ignored : bool } | Inline of { unroll_to : int option; was_inline_always : bool } *)
Record do_not_inline_payload_ : Type := { erase_attribute_if_ignored : bool }.
(* The inline record of [Inline]: abstract (a name of its fields is taken, or it holds the type); [mk_Inline] makes one, [match_can_inline_] reads it. *)
Parameter inline_payload_ : Type.
Inductive can_inline_ : Type :=
| Do_not_inline : do_not_inline_payload_ -> can_inline_
| Inline : inline_payload_ -> can_inline_.
Parameter match_can_inline_ : forall {Res : Type}, can_inline_ -> (bool -> M Res) -> (option int -> bool -> M Res) -> M Res.
Extract Inlined Constant match_can_inline_ => "(fun x__0 f__1 f__2 -> match x__0 with Call_site_inlining_decision_type.Do_not_inline { erase_attribute_if_ignored = x__1 } -> f__1 x__1 | Call_site_inlining_decision_type.Inline { unroll_to = x__1; was_inline_always = x__2 } -> f__2 x__1 x__2)".
(* call_site_inlining_decision_type.mli:61  val can_inline : t -> can_inline *)
Parameter can_inline : t -> M can_inline_.
Extract Inlined Constant can_inline => "Call_site_inlining_decision_type.can_inline".
