(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Unboxing_types], after its interface
   middle_end/flambda2/simplify/unboxing/unboxing_types.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter Continuation_extra_params_and_args Flambda_debug_uid Flambda_kind Format Function_slot Tag Value_slot Variable_.

(* unboxing_types.mli:22  type do_not_unbox_reason = | Not_beneficial | Max_depth_exceeded | Incomplete_parameter_type | Not_enough_information_at_use | Not_of_kind_value | Unboxing_not_requested | All_fields_invalid *)
Inductive do_not_unbox_reason : Type :=
| Not_beneficial : do_not_unbox_reason
| Max_depth_exceeded : do_not_unbox_reason
| Incomplete_parameter_type : do_not_unbox_reason
| Not_enough_information_at_use : do_not_unbox_reason
| Not_of_kind_value : do_not_unbox_reason
| Unboxing_not_requested : do_not_unbox_reason
| All_fields_invalid : do_not_unbox_reason.
Extract Inductive do_not_unbox_reason => "Unboxing_types.do_not_unbox_reason" [ "Unboxing_types.Not_beneficial" "Unboxing_types.Max_depth_exceeded" "Unboxing_types.Incomplete_parameter_type" "Unboxing_types.Not_enough_information_at_use" "Unboxing_types.Not_of_kind_value" "Unboxing_types.Unboxing_not_requested" "Unboxing_types.All_fields_invalid" ].
Module Extra_param_and_args.
  (* unboxing_types.mli:32  type t = private { param : Variable.t; param_debug_uid : Flambda_debug_uid.t; args : EPA.Extra_arg.t Apply_cont_rewrite_id.Map.t } *)
  Record t : Type := { param : Variable_.t; param_debug_uid : Flambda_debug_uid.t; args : Apply_cont_rewrite_id.Map.t Continuation_extra_params_and_args.Extra_arg.t }.
  (* unboxing_types.mli:38  val create : name:string -> debug_uid:Flambda_debug_uid.t -> Flambda_kind.t -> t *)
  Parameter create : string -> Flambda_debug_uid.t -> Flambda_kind.t -> M t.
  Extract Inlined Constant create => "Unboxing_types.Extra_param_and_args.create".
  (* unboxing_types.mli:41  val update_param_args : t -> Apply_cont_rewrite_id.t -> EPA.Extra_arg.t -> t *)
  Parameter update_param_args : t -> Apply_cont_rewrite_id.t -> Continuation_extra_params_and_args.Extra_arg.t -> M t.
  Extract Inlined Constant update_param_args => "Unboxing_types.Extra_param_and_args.update_param_args".
  (* unboxing_types.mli:43  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Unboxing_types.Extra_param_and_args.print".
End Extra_param_and_args.
(* unboxing_types.mli:66  and field_decision = { epa : Extra_param_and_args.t; decision : decision; kind : Flambda_kind.With_subkind.t } *)
(* PORT-GAP(type): it is a record that is recursive with other types: abstract, with one maker and one eliminator. *)
Parameter field_decision : Type.
Extract Inlined Constant field_decision => "Unboxing_types.field_decision".
(* unboxing_types.mli:46  type unboxing_decision = | Unique_tag_and_size of { tag : Tag.t; shape : Flambda_kind.Block_shape.t; fields : field_decision list } | Variant of { tag : Extra_param_and_args.t; const_ctors : const_ctors_decision; fields_by_tag : (Flambda_kind.Block_shape.t * field_decision list) Tag.Scannable.Map.t } | Closure_single_entry of { function_slot : Function_slot.t; vars_within_closure : field_decisi... *)
(* unboxing_types.mli:72  and const_ctors_decision = | Zero | At_least_one of { is_int : Extra_param_and_args.t; ctor : decision } *)
(* unboxing_types.mli:79  and decision = | Unbox of unboxing_decision | Do_not_unbox of do_not_unbox_reason *)
Inductive unboxing_decision : Type :=
| Unique_tag_and_size : Tag.t -> Flambda_kind.Block_shape.t -> list field_decision -> unboxing_decision
| Variant : Unboxing_types.Extra_param_and_args.t -> const_ctors_decision -> Tag.Scannable.Map.t (Flambda_kind.Block_shape.t * list field_decision) -> unboxing_decision
| Closure_single_entry : Function_slot.t -> Value_slot.Map.t field_decision -> unboxing_decision
| Number : Flambda_kind.Naked_number_kind.t -> Unboxing_types.Extra_param_and_args.t -> unboxing_decision
with const_ctors_decision : Type :=
| Zero : const_ctors_decision
| At_least_one : Unboxing_types.Extra_param_and_args.t -> decision_ -> const_ctors_decision
with decision_ : Type :=
| Unbox : unboxing_decision -> decision_
| Do_not_unbox : do_not_unbox_reason -> decision_.
Extract Inductive unboxing_decision => "Unboxing_types.unboxing_decision" [ "(fun (x__1, x__2, x__3) -> (Unboxing_types.Unique_tag_and_size { tag = x__1; shape = x__2; fields = x__3 } : Unboxing_types.unboxing_decision))" "(fun (x__1, x__2, x__3) -> (Unboxing_types.Variant { tag = x__1; const_ctors = x__2; fields_by_tag = x__3 } : Unboxing_types.unboxing_decision))" "(fun (x__1, x__2) -> (Unboxing_types.Closure_single_entry { function_slot = x__1; vars_within_closure = x__2 } : Unboxing_types.unboxing_decision))" "Unboxing_types.Number" ] "(fun f__1 f__2 f__3 f__4 x__0 -> match (x__0 : Unboxing_types.unboxing_decision) with Unboxing_types.Unique_tag_and_size { tag = x__1; shape = x__2; fields = x__3 } -> f__1 x__1 x__2 x__3 | Unboxing_types.Variant { tag = x__1; const_ctors = x__2; fields_by_tag = x__3 } -> f__2 x__1 x__2 x__3 | Unboxing_types.Closure_single_entry { function_slot = x__1; vars_within_closure = x__2 } -> f__3 x__1 x__2 | Unboxing_types.Number (x__1, x__2) -> f__4 x__1 x__2)".
Extract Inductive const_ctors_decision => "Unboxing_types.const_ctors_decision" [ "Unboxing_types.Zero" "(fun (x__1, x__2) -> (Unboxing_types.At_least_one { is_int = x__1; ctor = x__2 } : Unboxing_types.const_ctors_decision))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Unboxing_types.const_ctors_decision) with Unboxing_types.Zero -> f__1 () | Unboxing_types.At_least_one { is_int = x__1; ctor = x__2 } -> f__2 x__1 x__2)".
Extract Inductive decision_ => "Unboxing_types.decision" [ "Unboxing_types.Unbox" "Unboxing_types.Do_not_unbox" ].
Parameter mk_field_decision : Unboxing_types.Extra_param_and_args.t -> decision_ -> Flambda_kind.With_subkind.t -> field_decision.
Extract Inlined Constant mk_field_decision => "(fun x__1 x__2 x__3 -> { Unboxing_types.epa = x__1; decision = x__2; kind = x__3 })".
Parameter match_field_decision : forall {Res : Type}, field_decision -> (Unboxing_types.Extra_param_and_args.t -> decision_ -> Flambda_kind.With_subkind.t -> M Res) -> M Res.
Extract Inlined Constant match_field_decision => "(fun x__0 f__1 -> let { Unboxing_types.epa = x__1; decision = x__2; kind = x__3 } = x__0 in f__1 x__1 x__2 x__3)".
(* unboxing_types.mli:84  val print_decision : Format.formatter -> decision -> unit *)
Parameter print_decision : Format.formatter -> decision_ -> M unit.
Extract Inlined Constant print_decision => "Unboxing_types.print_decision".
Module Decisions.
  (* unboxing_types.mli:87  type t = { decisions : (BP.t * decision) list; rewrite_ids_seen : Apply_cont_rewrite_id.Set.t; rewrites_ids_known_as_invalid : Apply_cont_rewrite_id.Set.t } *)
  Record t : Type := { decisions : list (Bound_parameter.t * Unboxing_types.decision_); rewrite_ids_seen : Apply_cont_rewrite_id.Set_.t; rewrites_ids_known_as_invalid : Apply_cont_rewrite_id.Set_.t }.
  (* unboxing_types.mli:93  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Unboxing_types.Decisions.print".
End Decisions.
(* unboxing_types.mli:114  type pass = | Filter ( * First pass when computing unboxing decisions. This is done before inspecting the handler of the continuation whose parameters we are trying to unbox. For a non-recursive continuation, that means that all use sites of the continuation are known, but for recursive continuations, there are likely use sites that are not known at this point, so we only keep the original deci... *)
Inductive pass : Type :=
| Filter : pass
| Compute_all_extra_args : pass.
Extract Inductive pass => "Unboxing_types.pass" [ "Unboxing_types.Filter" "Unboxing_types.Compute_all_extra_args" ].

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Unboxing_types. End Unboxing_types.
