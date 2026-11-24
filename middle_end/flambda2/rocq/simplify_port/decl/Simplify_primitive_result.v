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
   Simplify uses of the compiler's module [Simplify_primitive_result], after its interface
   middle_end/flambda2/simplify/simplify_primitive_result.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_var Downwards_acc Flambda Flambda_kind Or_invalid Simplified_named.

(* simplify_primitive_result.mli:19  type t_simplified = private { simplified_named : Simplified_named.t Or_invalid.t; try_reify : bool; dacc : Downwards_acc.t } *)
Record t_simplified : Type := { simplified_named : Or_invalid.t Simplified_named.t; try_reify : bool; dacc : Downwards_acc.t }.
(* simplify_primitive_result.mli:25  type t = t_simplified Simplified_named.or_rewritten *)
Definition t : Type := Simplified_named.or_rewritten t_simplified.
Extract Inlined Constant t => "Simplify_primitive_result.t".
(* simplify_primitive_result.mli:27  val create : Flambda.Named.t -> try_reify:bool -> Downwards_acc.t -> t *)
Parameter create : Flambda.Named.t -> bool -> Downwards_acc.t -> M t.
Extract Inlined Constant create => "Simplify_primitive_result.create".
(* simplify_primitive_result.mli:29  val create_simplified : Simplified_named.t -> try_reify:bool -> Downwards_acc.t -> t *)
Parameter create_simplified : Simplified_named.t -> bool -> Downwards_acc.t -> M t.
Extract Inlined Constant create_simplified => "Simplify_primitive_result.create_simplified".
(* simplify_primitive_result.mli:32  val create_invalid : Downwards_acc.t -> t *)
Parameter create_invalid : Downwards_acc.t -> M t.
Extract Inlined Constant create_invalid => "Simplify_primitive_result.create_invalid".
(* simplify_primitive_result.mli:34  val create_unit : Downwards_acc.t -> result_var:Bound_var.t -> original_term:Flambda.Named.t -> t *)
Parameter create_unit : Downwards_acc.t -> Bound_var.t -> Flambda.Named.t -> M t.
Extract Inlined Constant create_unit => "Simplify_primitive_result.create_unit".
(* simplify_primitive_result.mli:43  val create_unknown : Downwards_acc.t -> result_var:Bound_var.t -> Flambda_kind.t -> original_term:Flambda.Named.t -> t *)
Parameter create_unknown : Downwards_acc.t -> Bound_var.t -> Flambda_kind.t -> Flambda.Named.t -> M t.
Extract Inlined Constant create_unknown => "Simplify_primitive_result.create_unknown".
(* simplify_primitive_result.mli:50  val create_rewritten : (body:Flambda.Expr.t -> Flambda.Expr.t) -> t *)
Parameter create_rewritten : (Flambda.Expr.t -> M Flambda.Expr.t) -> M t.
Extract Inlined Constant create_rewritten => "Simplify_primitive_result.create_rewritten".
(* simplify_primitive_result.mli:52  val is_invalid : t -> bool *)
Parameter is_invalid : t -> M bool.
Extract Inlined Constant is_invalid => "Simplify_primitive_result.is_invalid".
(* simplify_primitive_result.mli:54  val map_dacc : t -> (Downwards_acc.t -> Downwards_acc.t) -> t *)
Parameter map_dacc : t -> (Downwards_acc.t -> M Downwards_acc.t) -> M t.
Extract Inlined Constant map_dacc => "Simplify_primitive_result.map_dacc".
