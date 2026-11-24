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
   Simplify uses of the compiler's module [Apply_expr], after its interface
   middle_end/flambda2/terms/apply_expr.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Call_kind Continuation Flambda_arity Format Inlined_attribute.

(* apply_expr.mli:20  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Apply_expr.t".
(* apply_expr.mli:24  include Expr_std.S with type t := t *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Apply_expr.print".
Module Result_continuation.
  (* apply_expr.mli:31  type t = | Return of Continuation.t | Never_returns *)
  Inductive t : Type :=
  | Return : Continuation.t -> t
  | Never_returns : t.
  Extract Inductive t => "Apply_expr.Result_continuation.t" [ "Apply_expr.Result_continuation.Return" "Apply_expr.Result_continuation.Never_returns" ].
End Result_continuation.
Module Position.
  (* apply_expr.mli:41  type t = | Normal | Nontail *)
  Inductive t : Type :=
  | Normal : t
  | Nontail : t.
  Extract Inductive t => "Apply_expr.Position.t" [ "Apply_expr.Position.Normal" "Apply_expr.Position.Nontail" ].
End Position.
(* apply_expr.mli:83  val return_arity : t -> [`Complex] Flambda_arity.t *)
Parameter return_arity : t -> M Flambda_arity.t.
Extract Inlined Constant return_arity => "Apply_expr.return_arity".
(* apply_expr.mli:89  val return_mode : t -> Alloc_mode.For_applications.t *)
Parameter return_mode : t -> M Alloc_mode.For_applications.t.
Extract Inlined Constant return_mode => "Apply_expr.return_mode".
(* apply_expr.mli:120  val with_call_kind : t -> Call_kind.t -> t *)
Parameter with_call_kind : t -> Call_kind.t -> M t.
Extract Inlined Constant with_call_kind => "Apply_expr.with_call_kind".
(* apply_expr.mli:134  val with_inlined_attribute : t -> Inlined_attribute.t -> t *)
Parameter with_inlined_attribute : t -> Inlined_attribute.t -> M t.
Extract Inlined Constant with_inlined_attribute => "Apply_expr.with_inlined_attribute".
