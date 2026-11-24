(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*   Copyright 2021--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplify_extcall], after its interface
   middle_end/flambda2/simplify/simplify_extcall.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Downwards_acc Flambda Flambda2_types Or_unknown Removed_operations.

(* simplify_extcall.mli:18  type t = | Unchanged of { return_types : Flambda2_types.t list Or_unknown.t } | Specialised of Downwards_acc.t * Flambda.Expr.t * Removed_operations.t | Invalid *)
Record unchanged_payload_ : Type := { return_types : Or_unknown.t (list Flambda2_types.t) }.
Inductive t : Type :=
| Unchanged : unchanged_payload_ -> t
| Specialised : Downwards_acc.t -> Flambda.Expr.t -> Removed_operations.t -> t
| Invalid : t.
(* simplify_extcall.mli:23  val simplify_extcall : Downwards_acc.t -> Flambda.Apply.t -> callee_ty:Flambda2_types.t -> arg_types:Flambda2_types.t list -> t *)
Parameter simplify_extcall : Downwards_acc.t -> Flambda.Apply.t -> Flambda2_types.t -> list Flambda2_types.t -> M t.
Extract Inlined Constant simplify_extcall => "Simplify_extcall.simplify_extcall".
