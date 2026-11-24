(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [One_recursive_handler], after its interface
   middle_end/flambda2/simplify/one_recursive_handler.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Flambda Format.

(* one_recursive_handler.mli:16  type t = private { params : Bound_parameters.t; handler : Flambda.Expr.t; is_cold : bool } *)
Record t : Type := { params : Bound_parameters.t; handler : Flambda.Expr.t; is_cold : bool }.
(* one_recursive_handler.mli:22  val create : params:Bound_parameters.t -> handler:Flambda.Expr.t -> is_cold:bool -> t *)
Parameter create : Bound_parameters.t -> Flambda.Expr.t -> bool -> M t.
Extract Inlined Constant create => "One_recursive_handler.create".
(* one_recursive_handler.mli:25  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "One_recursive_handler.print".
(* one_recursive_handler.mli:27  val with_handler : Flambda.Expr.t -> t -> t *)
Parameter with_handler : Flambda.Expr.t -> t -> M t.
Extract Inlined Constant with_handler => "One_recursive_handler.with_handler".
