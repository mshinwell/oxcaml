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
   Simplify uses of the compiler's module [Common_subexpression_elimination], after its interface
   middle_end/flambda2/simplify/common_subexpression_elimination.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameters Continuation_extra_params_and_args Flambda2_types Flambda_primitive Format Scope Simple.

(* module EPA = Continuation_extra_params_and_args *)
Module EPA := Continuation_extra_params_and_args.
(* module P = Flambda_primitive *)
Module P := Flambda_primitive.
(* module RI = Apply_cont_rewrite_id *)
Module RI := Apply_cont_rewrite_id.
(* module T = Flambda2_types *)
Module T := Flambda2_types.
(* module TE = Flambda2_types.Typing_env *)
Module TE := Flambda2_types.Typing_env.
(* module TEE = Flambda2_types.Typing_env_extension *)
Module TEE := Flambda2_types.Typing_env_extension.
(* common_subexpression_elimination.mli:27  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Common_subexpression_elimination.t".
(* common_subexpression_elimination.mli:29  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Common_subexpression_elimination.print".
(* common_subexpression_elimination.mli:31  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Common_subexpression_elimination.empty".
(* common_subexpression_elimination.mli:37  val add : t -> P.Eligible_for_cse.t -> bound_to:Simple.t -> Scope.t -> t *)
Parameter add : t -> Flambda_primitive.Eligible_for_cse.t -> Simple.t -> Scope.t -> M t.
Extract Inlined Constant add => "Common_subexpression_elimination.add".
(* common_subexpression_elimination.mli:39  val find : t -> P.Eligible_for_cse.t -> Simple.t option *)
Parameter find : t -> Flambda_primitive.Eligible_for_cse.t -> M (option Simple.t).
Extract Inlined Constant find => "Common_subexpression_elimination.find".
Module Join_result.
  (* common_subexpression_elimination.mli:42  type nonrec t = private { cse_at_join_point : t; extra_params : EPA.t; env_extension : TEE.t; extra_allowed_names : Name_occurrences.t } *)
  Parameter t : Type.
  Extract Inlined Constant t => "Common_subexpression_elimination.Join_result.t".
End Join_result.
(* common_subexpression_elimination.mli:52  val join : typing_env_at_fork:TE.t -> cse_at_fork:t -> use_info:'a list -> get_typing_env:('a -> TE.t) -> get_rewrite_id:('a -> RI.t) -> get_cse:('a -> t) -> params:Bound_parameters.t -> Join_result.t option *)
Parameter join : forall {A : Type}, Flambda2_types.Typing_env.t -> t -> list A -> (A -> M Flambda2_types.Typing_env.t) -> (A -> M Apply_cont_rewrite_id.t) -> (A -> M t) -> Bound_parameters.t -> M (option Common_subexpression_elimination.Join_result.t).
Extract Inlined Constant join => "Common_subexpression_elimination.join".
