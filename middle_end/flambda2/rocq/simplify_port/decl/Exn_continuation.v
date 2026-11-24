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
   Simplify uses of the compiler's module [Exn_continuation], after its interface
   middle_end/flambda2/terms/exn_continuation.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Flambda_arity Flambda_kind Format Simple.

(* exn_continuation.mli:27  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Exn_continuation.t".
Module T.
  (* exn_continuation.mli:29  include Container_types.S with type t := t *)
  Definition t : Type := Exn_continuation.t.
  Extract Inlined Constant t => "Exn_continuation.T.t".
End T.
(* exn_continuation.mli:29  include Container_types.S with type t := t *)
Parameter equal : Exn_continuation.T.t -> Exn_continuation.T.t -> M bool.
Extract Inlined Constant equal => "Exn_continuation.equal".
(* exn_continuation.mli:31  include Expr_std.S with type t := t *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Exn_continuation.print".
(* exn_continuation.mli:36  val create : exn_handler:Continuation.t -> extra_args:(Simple.t * Flambda_kind.With_subkind.t) list -> t *)
Parameter create : Continuation.t -> list (Simple.t * Flambda_kind.With_subkind.t) -> M t.
Extract Inlined Constant create => "Exn_continuation.create".
(* exn_continuation.mli:42  val exn_handler : t -> Continuation.t *)
Parameter exn_handler : t -> M Continuation.t.
Extract Inlined Constant exn_handler => "Exn_continuation.exn_handler".
(* exn_continuation.mli:45  val extra_args : t -> (Simple.t * Flambda_kind.With_subkind.t) list *)
Parameter extra_args : t -> M (list (Simple.t * Flambda_kind.With_subkind.t)).
Extract Inlined Constant extra_args => "Exn_continuation.extra_args".
(* exn_continuation.mli:49  val arity : t -> [> `Unarized] Flambda_arity.t *)
Parameter arity : t -> M Flambda_arity.t.
Extract Inlined Constant arity => "Exn_continuation.arity".
(* exn_continuation.mli:51  val with_exn_handler : t -> Continuation.t -> t *)
Parameter with_exn_handler : t -> Continuation.t -> M t.
Extract Inlined Constant with_exn_handler => "Exn_continuation.with_exn_handler".
(* exn_continuation.mli:53  val without_extra_args : t -> t *)
Parameter without_extra_args : t -> M t.
Extract Inlined Constant without_extra_args => "Exn_continuation.without_extra_args".
