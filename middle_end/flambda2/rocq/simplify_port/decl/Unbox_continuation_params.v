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
   Simplify uses of the compiler's module [Unbox_continuation_params], after its interface
   middle_end/flambda2/simplify/unboxing/unbox_continuation_params.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Continuation_extra_params_and_args Continuation_uses Downwards_env Flambda2_types Format Target_system.

Module Decisions.
  (* unbox_continuation_params.mli:20  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Unbox_continuation_params.Decisions.t".
  (* unbox_continuation_params.mli:22  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Unbox_continuation_params.Decisions.print".
End Decisions.
(* unbox_continuation_params.mli:25  val make_do_not_unbox_decisions : Bound_parameters.t -> Decisions.t *)
Parameter make_do_not_unbox_decisions : Bound_parameters.t -> M Unbox_continuation_params.Decisions.t.
Extract Inlined Constant make_do_not_unbox_decisions => "Unbox_continuation_params.make_do_not_unbox_decisions".
(* unbox_continuation_params.mli:27  type continuation_arg_types = | Recursive | Non_recursive of Continuation_uses.arg_types_by_use_id *)
Inductive continuation_arg_types : Type :=
| Recursive : continuation_arg_types
| Non_recursive : Continuation_uses.arg_types_by_use_id -> continuation_arg_types.
Extract Inductive continuation_arg_types => "Unbox_continuation_params.continuation_arg_types" [ "Unbox_continuation_params.Recursive" "Unbox_continuation_params.Non_recursive" ].
(* unbox_continuation_params.mli:31  val make_decisions : continuation_arg_types:continuation_arg_types -> DE.t -> Bound_parameters.t -> T.t list -> DE.t * Decisions.t *)
Parameter make_decisions : continuation_arg_types -> Downwards_env.t -> Bound_parameters.t -> list Flambda2_types.t -> M (Downwards_env.t * Unbox_continuation_params.Decisions.t).
Extract Inlined Constant make_decisions => "Unbox_continuation_params.make_decisions".
(* unbox_continuation_params.mli:38  val compute_extra_params_and_args : machine_width:Target_system.Machine_width.t -> Decisions.t -> arg_types_by_use_id:Continuation_uses.arg_types_by_use_id -> EPA.t -> EPA.t *)
Parameter compute_extra_params_and_args : Target_system.Machine_width.t -> Unbox_continuation_params.Decisions.t -> Continuation_uses.arg_types_by_use_id -> Continuation_extra_params_and_args.t -> M Continuation_extra_params_and_args.t.
Extract Inlined Constant compute_extra_params_and_args => "Unbox_continuation_params.compute_extra_params_and_args".
