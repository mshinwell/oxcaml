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
   Simplify uses of the compiler's module [Unboxing_epa], after its interface
   middle_end/flambda2/simplify/unboxing/unboxing_epa.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Continuation_extra_params_and_args Flambda2_types Simple Target_system Unboxing_types Variable_.

(* _none_  exception Invalid_apply_cont *)
Parameter Invalid_apply_cont : exception unit.
Extract Inlined Constant Invalid_apply_cont => "((fun () -> Unboxing_epa.Invalid_apply_cont), (function Unboxing_epa.Invalid_apply_cont -> Some () | _ -> None))".
(* unboxing_epa.mli:22  type unboxed_arg = | Poison ( * used for recursive calls * ) | Available of Simple.t | Generated of Variable.t | Added_by_wrapper_at_rewrite_use of { nth_arg : int } *)
Record added_by_wrapper_at_rewrite_use_payload_ : Type := { nth_arg : int }.
Inductive unboxed_arg : Type :=
| Poison : unboxed_arg
| Available : Simple.t -> unboxed_arg
| Generated : Variable_.t -> unboxed_arg
| Added_by_wrapper_at_rewrite_use : added_by_wrapper_at_rewrite_use_payload_ -> unboxed_arg.
(* unboxing_epa.mli:28  val compute_extra_args_for_one_decision_and_use : pass:Unboxing_types.pass -> Apply_cont_rewrite_id.t -> typing_env_at_use:Flambda2_types.Typing_env.t -> machine_width:Target_system.Machine_width.t -> unboxed_arg -> Unboxing_types.decision -> Unboxing_types.decision *)
Parameter compute_extra_args_for_one_decision_and_use : Unboxing_types.pass -> Apply_cont_rewrite_id.t -> Flambda2_types.Typing_env.t -> Target_system.Machine_width.t -> unboxed_arg -> Unboxing_types.decision_ -> M Unboxing_types.decision_.
Extract Inlined Constant compute_extra_args_for_one_decision_and_use => "Unboxing_epa.compute_extra_args_for_one_decision_and_use".
(* unboxing_epa.mli:37  val add_extra_params_and_args : Continuation_extra_params_and_args.t -> invalids:Apply_cont_rewrite_id.Set.t -> Unboxing_types.decision -> Continuation_extra_params_and_args.t *)
Parameter add_extra_params_and_args : Continuation_extra_params_and_args.t -> Apply_cont_rewrite_id.Set_.t -> Unboxing_types.decision_ -> M Continuation_extra_params_and_args.t.
Extract Inlined Constant add_extra_params_and_args => "Unboxing_epa.add_extra_params_and_args".
