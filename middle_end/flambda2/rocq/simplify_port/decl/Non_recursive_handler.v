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
   Simplify uses of the compiler's module [Non_recursive_handler], after its interface
   middle_end/flambda2/simplify/non_recursive_handler.mli
   (Git blob 44aa0da4f86f0d0c8562cb36be39cfbb913ec063). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Continuation Flambda Format Lifted_cont_params.

(* non_recursive_handler.mli:16  type t = private { cont : Continuation.t; params : Bound_parameters.t; lifted_params : Lifted_cont_params.t; handler : Flambda.Expr.t; is_exn_handler : bool; can_be_lifted : bool; is_cold : bool } *)
Record t : Type := { cont : Continuation.t; params : Bound_parameters.t; lifted_params : Lifted_cont_params.t; handler : Flambda.Expr.t; is_exn_handler : bool; can_be_lifted : bool; is_cold : bool }.
(* non_recursive_handler.mli:26  val create : cont:Continuation.t -> params:Bound_parameters.t -> lifted_params:Lifted_cont_params.t -> handler:Flambda.Expr.t -> is_exn_handler:bool -> can_be_lifted:bool -> is_cold:bool -> t *)
Parameter create : Continuation.t -> Bound_parameters.t -> Lifted_cont_params.t -> Flambda.Expr.t -> bool -> bool -> bool -> M t.
Extract Inlined Constant create => "Non_recursive_handler.create".
(* non_recursive_handler.mli:36  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Non_recursive_handler.print".
(* non_recursive_handler.mli:38  val with_handler : Flambda.Expr.t -> t -> t *)
Parameter with_handler : Flambda.Expr.t -> t -> M t.
Extract Inlined Constant with_handler => "Non_recursive_handler.with_handler".
(* non_recursive_handler.mli:40  val rename_params : t -> t *)
Parameter rename_params : t -> M t.
Extract Inlined Constant rename_params => "Non_recursive_handler.rename_params".
(* non_recursive_handler.mli:42  val with_can_be_lifted : bool -> t -> t *)
Parameter with_can_be_lifted : bool -> t -> M t.
Extract Inlined Constant with_can_be_lifted => "Non_recursive_handler.with_can_be_lifted".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Non_recursive_handler. End Non_recursive_handler.
