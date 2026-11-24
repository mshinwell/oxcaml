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
   Simplify uses of the compiler's module [Inlining_transforms], after its interface
   middle_end/flambda2/simplify/inlining/inlining_transforms.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Downwards_acc Flambda Flambda2_types.

(* inlining_transforms.mli:19  val inline : Downwards_acc.t -> apply:Apply.t -> unroll_to:int option -> was_inline_always:bool -> Flambda2_types.Function_type.t -> Downwards_acc.t * Expr.t *)
Parameter inline : Downwards_acc.t -> Flambda.Import_.Apply.t -> option int -> bool -> Flambda2_types.Function_type.t -> M (Downwards_acc.t * Flambda.Import_.Expr.t).
Extract Inlined Constant inline => "Inlining_transforms.inline".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Inlining_transforms. End Inlining_transforms.
