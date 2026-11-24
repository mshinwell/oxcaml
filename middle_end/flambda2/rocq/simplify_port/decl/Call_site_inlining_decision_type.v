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
| Speculatively_not_inline : Cost_metrics.t -> Stdlib_.float_ -> Stdlib_.float_ -> bool -> t
| Attribute_always : t
| Replay_history_says_must_inline : t -> t
| Begin_unrolling : int -> t
| Continue_unrolling : t
| Definition_says_inline : bool -> t
| Speculatively_inline : Cost_metrics.t -> Stdlib_.float_ -> Stdlib_.float_ -> bool -> t
| Jsir_inlining_disabled : t.
Extract Inductive t => "Call_site_inlining_decision_type.t" [ "Call_site_inlining_decision_type.Missing_code" "Call_site_inlining_decision_type.Definition_says_not_to_inline" "Call_site_inlining_decision_type.In_a_stub" "Call_site_inlining_decision_type.Doing_speculative_inlining" "Call_site_inlining_decision_type.Argument_types_not_useful" "Call_site_inlining_decision_type.Unrolling_depth_exceeded" "Call_site_inlining_decision_type.Max_inlining_depth_exceeded" "Call_site_inlining_decision_type.Recursion_depth_exceeded" "Call_site_inlining_decision_type.Never_inlined_attribute" "Call_site_inlining_decision_type.Forward_inlined_attribute_but_nothing_to_forward" "(fun (x__1, x__2, x__3, x__4) -> (Call_site_inlining_decision_type.Speculatively_not_inline { cost_metrics = x__1; evaluated_to = x__2; threshold = x__3; is_a_functor = x__4 } : Call_site_inlining_decision_type.t))" "Call_site_inlining_decision_type.Attribute_always" "Call_site_inlining_decision_type.Replay_history_says_must_inline" "Call_site_inlining_decision_type.Begin_unrolling" "Call_site_inlining_decision_type.Continue_unrolling" "(fun x__1 -> (Call_site_inlining_decision_type.Definition_says_inline { was_inline_always = x__1 } : Call_site_inlining_decision_type.t))" "(fun (x__1, x__2, x__3, x__4) -> (Call_site_inlining_decision_type.Speculatively_inline { cost_metrics = x__1; evaluated_to = x__2; threshold = x__3; is_a_functor = x__4 } : Call_site_inlining_decision_type.t))" "Call_site_inlining_decision_type.Jsir_inlining_disabled" ] "(fun f__1 f__2 f__3 f__4 f__5 f__6 f__7 f__8 f__9 f__10 f__11 f__12 f__13 f__14 f__15 f__16 f__17 f__18 x__0 -> match (x__0 : Call_site_inlining_decision_type.t) with Call_site_inlining_decision_type.Missing_code -> f__1 () | Call_site_inlining_decision_type.Definition_says_not_to_inline -> f__2 () | Call_site_inlining_decision_type.In_a_stub -> f__3 () | Call_site_inlining_decision_type.Doing_speculative_inlining -> f__4 () | Call_site_inlining_decision_type.Argument_types_not_useful -> f__5 () | Call_site_inlining_decision_type.Unrolling_depth_exceeded -> f__6 () | Call_site_inlining_decision_type.Max_inlining_depth_exceeded -> f__7 () | Call_site_inlining_decision_type.Recursion_depth_exceeded -> f__8 () | Call_site_inlining_decision_type.Never_inlined_attribute -> f__9 () | Call_site_inlining_decision_type.Forward_inlined_attribute_but_nothing_to_forward -> f__10 () | Call_site_inlining_decision_type.Speculatively_not_inline { cost_metrics = x__1; evaluated_to = x__2; threshold = x__3; is_a_functor = x__4 } -> f__11 x__1 x__2 x__3 x__4 | Call_site_inlining_decision_type.Attribute_always -> f__12 () | Call_site_inlining_decision_type.Replay_history_says_must_inline x__1 -> f__13 x__1 | Call_site_inlining_decision_type.Begin_unrolling x__1 -> f__14 x__1 | Call_site_inlining_decision_type.Continue_unrolling -> f__15 () | Call_site_inlining_decision_type.Definition_says_inline { was_inline_always = x__1 } -> f__16 x__1 | Call_site_inlining_decision_type.Speculatively_inline { cost_metrics = x__1; evaluated_to = x__2; threshold = x__3; is_a_functor = x__4 } -> f__17 x__1 x__2 x__3 x__4 | Call_site_inlining_decision_type.Jsir_inlining_disabled -> f__18 ())".
(* call_site_inlining_decision_type.mli:50  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Call_site_inlining_decision_type.print".
(* call_site_inlining_decision_type.mli:54  type can_inline = private | Do_not_inline of { erase_attribute_if_ignored : bool } | Inline of { unroll_to : int option; was_inline_always : bool } *)
Inductive can_inline_ : Type :=
| Do_not_inline : bool -> can_inline_
| Inline : option int -> bool -> can_inline_.
Extract Inductive can_inline_ => "Call_site_inlining_decision_type.can_inline" [ "(fun x__1 -> (Call_site_inlining_decision_type.Do_not_inline { erase_attribute_if_ignored = x__1 } : Call_site_inlining_decision_type.can_inline))" "(fun (x__1, x__2) -> (Call_site_inlining_decision_type.Inline { unroll_to = x__1; was_inline_always = x__2 } : Call_site_inlining_decision_type.can_inline))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Call_site_inlining_decision_type.can_inline) with Call_site_inlining_decision_type.Do_not_inline { erase_attribute_if_ignored = x__1 } -> f__1 x__1 | Call_site_inlining_decision_type.Inline { unroll_to = x__1; was_inline_always = x__2 } -> f__2 x__1 x__2)".
(* call_site_inlining_decision_type.mli:61  val can_inline : t -> can_inline *)
Parameter can_inline : t -> M can_inline_.
Extract Inlined Constant can_inline => "Call_site_inlining_decision_type.can_inline".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Call_site_inlining_decision_type. End Call_site_inlining_decision_type.
