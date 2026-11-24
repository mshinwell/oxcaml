(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Join_points], after its interface
   middle_end/flambda2/simplify/join_points.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Continuation_extra_params_and_args Downwards_env Lifted_constant_state One_continuation_use Replay_history Scope.

(* join_points.mli:21  type result = private { handler_env : Downwards_env.t; extra_params_and_args : Continuation_extra_params_and_args.t; is_single_inlinable_use : bool; escapes : bool } *)
Record result : Type := { handler_env : Downwards_env.t; extra_params_and_args : Continuation_extra_params_and_args.t; is_single_inlinable_use : bool; escapes : bool }.
(* join_points.mli:28  val compute_handler_env : ?replay:Replay_history.t * bool -> ?cut_after:Scope.t -> One_continuation_use.t list -> is_recursive:bool -> env_at_fork:Downwards_env.t -> consts_lifted_after_fork:Lifted_constant_state.t -> params:Bound_parameters.t -> previous_extra_params_and_args:Continuation_extra_params_and_args.t -> result *)
Parameter compute_handler_env : option (Replay_history.t * bool) -> option Scope.t -> list One_continuation_use.t -> bool -> Downwards_env.t -> Lifted_constant_state.t -> Bound_parameters.t -> Continuation_extra_params_and_args.t -> M result.
Extract Inlined Constant compute_handler_env => "(fun x__1 x__2 x__3 x__4 x__5 x__6 x__7 x__8 -> Join_points.compute_handler_env ?replay:x__1 ?cut_after:x__2 x__3 x__4 x__5 x__6 x__7 x__8)".
