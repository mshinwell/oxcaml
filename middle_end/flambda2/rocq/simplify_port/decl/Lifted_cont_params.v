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
   Simplify uses of the compiler's module [Lifted_cont_params], after its interface
   middle_end/flambda2/simplify/lifted_cont_params.mli
   (Git blob fced26a860fc5e662f51bb4cdbb025b33cfb1e45). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameter Bound_parameters Format Renaming Replay_history Simple.

(* lifted_cont_params.mli:41  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Lifted_cont_params.t".
(* lifted_cont_params.mli:44  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Lifted_cont_params.print".
(* lifted_cont_params.mli:47  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Lifted_cont_params.empty".
(* lifted_cont_params.mli:50  val is_empty : t -> bool *)
Parameter is_empty : t -> M bool.
Extract Inlined Constant is_empty => "Lifted_cont_params.is_empty".
(* lifted_cont_params.mli:53  val length : t -> int *)
Parameter length : t -> M int.
Extract Inlined Constant length => "Lifted_cont_params.length".
(* lifted_cont_params.mli:56  val new_param : t -> replay_history:Replay_history.t -> Bound_parameter.t -> t *)
Parameter new_param : t -> Replay_history.t -> Bound_parameter.t -> M t.
Extract Inlined Constant new_param => "Lifted_cont_params.new_param".
(* lifted_cont_params.mli:59  val rename : t -> t * Renaming.t *)
Parameter rename : t -> M (t * Renaming.t).
Extract Inlined Constant rename => "Lifted_cont_params.rename".
(* lifted_cont_params.mli:64  val args : callee_lifted_params:t -> caller_stack_lifted_params:t list -> Simple.t list *)
Parameter args : t -> list t -> M (list Simple.t).
Extract Inlined Constant args => "Lifted_cont_params.args".
(* lifted_cont_params.mli:70  val bound_parameters : t -> Bound_parameters.t *)
Parameter bound_parameters : t -> M Bound_parameters.t.
Extract Inlined Constant bound_parameters => "Lifted_cont_params.bound_parameters".
(* lifted_cont_params.mli:74  val fold : init:'a -> f:(Bound_parameter.t -> 'a -> 'a) -> t -> 'a *)
Parameter fold : forall {A : Type}, A -> (Bound_parameter.t -> A -> M A) -> t -> M A.
Extract Inlined Constant fold => "Lifted_cont_params.fold".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Lifted_cont_params. End Lifted_cont_params.
