(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2022 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Result_types], after its interface
   middle_end/flambda2/terms/result_types.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Flambda2_types Format.

(* result_types.mli:15  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Result_types.t".
(* result_types.mli:17  val create : params:Bound_parameters.t -> results:Bound_parameters.t -> Flambda2_types.Typing_env_extension.With_extra_variables.t -> t *)
Parameter create : Bound_parameters.t -> Bound_parameters.t -> Flambda2_types.Typing_env_extension.With_extra_variables.t -> M t.
Extract Inlined Constant create => "Result_types.create".
(* result_types.mli:23  val pattern_match : t -> f: (params:Bound_parameters.t -> results:Bound_parameters.t -> Flambda2_types.Typing_env_extension.With_extra_variables.t -> 'a) -> 'a *)
Parameter pattern_match : forall {A : Type}, t -> (Bound_parameters.t -> Bound_parameters.t -> Flambda2_types.Typing_env_extension.With_extra_variables.t -> M A) -> M A.
Extract Inlined Constant pattern_match => "Result_types.pattern_match".
(* result_types.mli:36  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Result_types.print".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Result_types. End Result_types.
