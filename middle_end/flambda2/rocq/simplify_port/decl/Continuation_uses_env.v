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
   Simplify uses of the compiler's module [Continuation_uses_env], after its interface
   middle_end/flambda2/simplify/env/continuation_uses_env.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Continuation Continuation_use_kind Continuation_uses Downwards_env Flambda2_types Flambda_arity Format Original_handlers.

(* continuation_uses_env.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Continuation_uses_env.t".
(* continuation_uses_env.mli:19  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Continuation_uses_env.print".
(* continuation_uses_env.mli:21  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Continuation_uses_env.empty".
(* continuation_uses_env.mli:23  include Continuation_uses_env_intf.S with type t := t *)
Parameter record_continuation : t -> Continuation.t -> Flambda_arity.t -> M t.
Extract Inlined Constant record_continuation => "Continuation_uses_env.record_continuation".
(* continuation_uses_env.mli:23  include Continuation_uses_env_intf.S with type t := t *)
Parameter record_continuation_use : t -> Continuation.t -> Continuation_use_kind.t -> Downwards_env.t -> list Flambda2_types.t -> M (t * Apply_cont_rewrite_id.t).
Extract Inlined Constant record_continuation_use => "Continuation_uses_env.record_continuation_use".
(* continuation_uses_env.mli:23  include Continuation_uses_env_intf.S with type t := t *)
Parameter delete_continuation_uses : t -> Continuation.t -> M t.
Extract Inlined Constant delete_continuation_uses => "Continuation_uses_env.delete_continuation_uses".
(* continuation_uses_env.mli:23  include Continuation_uses_env_intf.S with type t := t *)
Parameter get_typing_env_no_more_than_one_use : t -> Continuation.t -> M (option Flambda2_types.Typing_env.t).
Extract Inlined Constant get_typing_env_no_more_than_one_use => "Continuation_uses_env.get_typing_env_no_more_than_one_use".
(* continuation_uses_env.mli:23  include Continuation_uses_env_intf.S with type t := t *)
Parameter num_continuation_uses : t -> Continuation.t -> M int.
Extract Inlined Constant num_continuation_uses => "Continuation_uses_env.num_continuation_uses".
(* continuation_uses_env.mli:23  include Continuation_uses_env_intf.S with type t := t *)
Parameter all_continuations_used : t -> M Continuation.Set_.t.
Extract Inlined Constant all_continuations_used => "Continuation_uses_env.all_continuations_used".
(* continuation_uses_env.mli:25  val record_continuation_arity : t -> Original_handlers.t -> t *)
Parameter record_continuation_arity : t -> Original_handlers.t -> M t.
Extract Inlined Constant record_continuation_arity => "Continuation_uses_env.record_continuation_arity".
(* continuation_uses_env.mli:27  val get_continuation_uses : t -> Continuation.t -> Continuation_uses.t option *)
Parameter get_continuation_uses : t -> Continuation.t -> M (option Continuation_uses.t).
Extract Inlined Constant get_continuation_uses => "Continuation_uses_env.get_continuation_uses".
(* continuation_uses_env.mli:29  val remove : t -> Continuation.t -> t *)
Parameter remove : t -> Continuation.t -> M t.
Extract Inlined Constant remove => "Continuation_uses_env.remove".
(* continuation_uses_env.mli:32  val reset_uses : t -> t *)
Parameter reset_uses : t -> M t.
Extract Inlined Constant reset_uses => "Continuation_uses_env.reset_uses".
(* continuation_uses_env.mli:34  val clear_continuation_uses : t -> Continuation.t -> t *)
Parameter clear_continuation_uses : t -> Continuation.t -> M t.
Extract Inlined Constant clear_continuation_uses => "Continuation_uses_env.clear_continuation_uses".
(* continuation_uses_env.mli:36  val union : t -> t -> t *)
Parameter union : t -> t -> M t.
Extract Inlined Constant union => "Continuation_uses_env.union".
(* continuation_uses_env.mli:38  val mark_non_inlinable : t -> t *)
Parameter mark_non_inlinable : t -> M t.
Extract Inlined Constant mark_non_inlinable => "Continuation_uses_env.mark_non_inlinable".
(* continuation_uses_env.mli:44  val add_continuation_use : t -> Continuation.t -> Continuation_use_kind.t -> id:Apply_cont_rewrite_id.t -> env_at_use:Downwards_env.t -> arg_types:Flambda2_types.t list -> t *)
Parameter add_continuation_use : t -> Continuation.t -> Continuation_use_kind.t -> Apply_cont_rewrite_id.t -> Downwards_env.t -> list Flambda2_types.t -> M t.
Extract Inlined Constant add_continuation_use => "Continuation_uses_env.add_continuation_use".
