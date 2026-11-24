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
   Simplify uses of the compiler's module [Continuation_uses], after its interface
   middle_end/flambda2/simplify/env/continuation_uses.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Continuation Flambda2_types Flambda_arity Format One_continuation_use.

(* continuation_uses.mli:22  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Continuation_uses.t".
(* continuation_uses.mli:24  val create : Continuation.t -> [`Unarized] Flambda_arity.t -> t *)
Parameter create : Continuation.t -> Flambda_arity.t -> M t.
Extract Inlined Constant create => "Continuation_uses.create".
(* continuation_uses.mli:26  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Continuation_uses.print".
(* continuation_uses.mli:28  val add_use : t -> One_continuation_use.t -> t *)
Parameter add_use : t -> One_continuation_use.t -> M t.
Extract Inlined Constant add_use => "Continuation_uses.add_use".
(* continuation_uses.mli:30  val get_uses : t -> One_continuation_use.t list *)
Parameter get_uses : t -> M (list One_continuation_use.t).
Extract Inlined Constant get_uses => "Continuation_uses.get_uses".
(* continuation_uses.mli:32  type arg_at_use = { arg_type : Flambda2_types.t; typing_env : Flambda2_types.Typing_env.t } *)
Record arg_at_use : Type := { arg_type : Flambda2_types.t; typing_env : Flambda2_types.Typing_env.t }.
(* continuation_uses.mli:37  type arg_types_by_use_id = arg_at_use Apply_cont_rewrite_id.Map.t list *)
Definition arg_types_by_use_id : Type := list (Apply_cont_rewrite_id.Map.t arg_at_use).
Extract Inlined Constant arg_types_by_use_id => "Continuation_uses.arg_types_by_use_id".
(* continuation_uses.mli:39  val print_arg_type_at_use : Format.formatter -> arg_at_use -> unit *)
Parameter print_arg_type_at_use : Format.formatter -> arg_at_use -> M unit.
Extract Inlined Constant print_arg_type_at_use => "Continuation_uses.print_arg_type_at_use".
(* continuation_uses.mli:41  val get_arg_types_by_use_id : t -> arg_types_by_use_id *)
Parameter get_arg_types_by_use_id : t -> M arg_types_by_use_id.
Extract Inlined Constant get_arg_types_by_use_id => "Continuation_uses.get_arg_types_by_use_id".
(* continuation_uses.mli:48  val get_arg_types_by_use_id_for_invariant_params : [`Unarized] Flambda_arity.t -> t list -> arg_types_by_use_id *)
Parameter get_arg_types_by_use_id_for_invariant_params : Flambda_arity.t -> list t -> M arg_types_by_use_id.
Extract Inlined Constant get_arg_types_by_use_id_for_invariant_params => "Continuation_uses.get_arg_types_by_use_id_for_invariant_params".
(* continuation_uses.mli:51  val get_use_ids : t -> Apply_cont_rewrite_id.Set.t *)
Parameter get_use_ids : t -> M Apply_cont_rewrite_id.Set_.t.
Extract Inlined Constant get_use_ids => "Continuation_uses.get_use_ids".
(* continuation_uses.mli:53  val number_of_uses : t -> int *)
Parameter number_of_uses : t -> M int.
Extract Inlined Constant number_of_uses => "Continuation_uses.number_of_uses".
(* continuation_uses.mli:55  val arity : t -> [`Unarized] Flambda_arity.t *)
Parameter arity : t -> M Flambda_arity.t.
Extract Inlined Constant arity => "Continuation_uses.arity".
(* continuation_uses.mli:57  val get_typing_env_no_more_than_one_use : t -> Flambda2_types.Typing_env.t option *)
Parameter get_typing_env_no_more_than_one_use : t -> M (option Flambda2_types.Typing_env.t).
Extract Inlined Constant get_typing_env_no_more_than_one_use => "Continuation_uses.get_typing_env_no_more_than_one_use".
(* continuation_uses.mli:60  val union : t -> t -> t *)
Parameter union : t -> t -> M t.
Extract Inlined Constant union => "Continuation_uses.union".
(* continuation_uses.mli:62  val mark_non_inlinable : t -> t *)
Parameter mark_non_inlinable : t -> M t.
Extract Inlined Constant mark_non_inlinable => "Continuation_uses.mark_non_inlinable".
(* continuation_uses.mli:64  val clear_uses : t -> t *)
Parameter clear_uses : t -> M t.
Extract Inlined Constant clear_uses => "Continuation_uses.clear_uses".
