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

(* This file follows
   middle_end/flambda2/simplify/env/continuation_uses_env_intf.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9: the module type [S], item by item
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the arguments
   by place) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Continuation
  Continuation_use_kind Downwards_env Flambda2_types Flambda_arity.

(* PORT-GAP(decl): decl/Flambda_arity.v prints the type of an arity as
   [(_) Flambda_arity.t], which OCaml refuses in a signature. This name is
   the same type in Rocq and is printed with the compiler's index. *)
Definition unarized_arity : Type := Flambda_arity.t.
Extract Inlined Constant unarized_arity => "[ `Unarized ] Flambda_arity.t".

(* 17-39 *)
Module Type S.
  (* 18 *)
  Parameter t : Type.

  (* 20-21 *)
  Parameter record_continuation :
    t -> Continuation.t -> unarized_arity -> M t.

  (* 23-29. PORT-GAP(loose): the labels [~env_at_use] and [~arg_types] are
     not kept. *)
  Parameter record_continuation_use :
    t ->
    Continuation.t ->
    Continuation_use_kind.t ->
    Downwards_env.t ->
    list Flambda2_types.t ->
    M (t * Apply_cont_rewrite_id.t).

  (* 31 *)
  Parameter delete_continuation_uses : t -> Continuation.t -> M t.

  (* 33-34 *)
  Parameter get_typing_env_no_more_than_one_use :
    t -> Continuation.t -> M (option Flambda2_types.Typing_env.t).

  (* 36 *)
  Parameter num_continuation_uses : t -> Continuation.t -> M int.

  (* 38 *)
  Parameter all_continuations_used : t -> M Continuation.Set_.t.
End S.
