(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Optimistic_unboxing_decision], after its interface
   middle_end/flambda2/simplify/unboxing/optimistic_unboxing_decision.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda2_types Unboxing_types.

(* optimistic_unboxing_decision.mli:33  val make_optimistic_decision : depth:int -> recursive:bool -> Flambda2_types.Typing_env.t -> param_type:Flambda2_types.t -> Unboxing_types.decision *)
Parameter make_optimistic_decision : int -> bool -> Flambda2_types.Typing_env.t -> Flambda2_types.t -> M Unboxing_types.decision_.
Extract Inlined Constant make_optimistic_decision => "Optimistic_unboxing_decision.make_optimistic_decision".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Optimistic_unboxing_decision. End Optimistic_unboxing_decision.
