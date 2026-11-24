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
   Simplify uses of the compiler's module [One_continuation_use], after its interface
   middle_end/flambda2/simplify/env/one_continuation_use.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Continuation_use_kind Downwards_env Flambda2_types Format.

(* module DE = Downwards_env *)
Module DE := Downwards_env.
(* module T = Flambda2_types *)
Module T := Flambda2_types.
(* one_continuation_use.mli:20  type t *)
Parameter t : Type.
Extract Inlined Constant t => "One_continuation_use.t".
(* one_continuation_use.mli:22  val create : Continuation_use_kind.t -> env_at_use:DE.t -> Apply_cont_rewrite_id.t -> arg_types:T.t list -> t *)
Parameter create : Continuation_use_kind.t -> Downwards_env.t -> Apply_cont_rewrite_id.t -> list Flambda2_types.t -> M t.
Extract Inlined Constant create => "One_continuation_use.create".
(* one_continuation_use.mli:29  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "One_continuation_use.print".
(* one_continuation_use.mli:31  val id : t -> Apply_cont_rewrite_id.t *)
Parameter id : t -> M Apply_cont_rewrite_id.t.
Extract Inlined Constant id => "One_continuation_use.id".
(* one_continuation_use.mli:33  val use_kind : t -> Continuation_use_kind.t *)
Parameter use_kind : t -> M Continuation_use_kind.t.
Extract Inlined Constant use_kind => "One_continuation_use.use_kind".
(* one_continuation_use.mli:35  val arg_types : t -> T.t list *)
Parameter arg_types : t -> M (list Flambda2_types.t).
Extract Inlined Constant arg_types => "One_continuation_use.arg_types".
(* one_continuation_use.mli:37  val env_at_use : t -> DE.t *)
Parameter env_at_use : t -> M Downwards_env.t.
Extract Inlined Constant env_at_use => "One_continuation_use.env_at_use".
(* one_continuation_use.mli:39  val mark_non_inlinable : t -> t *)
Parameter mark_non_inlinable : t -> M t.
Extract Inlined Constant mark_non_inlinable => "One_continuation_use.mark_non_inlinable".
