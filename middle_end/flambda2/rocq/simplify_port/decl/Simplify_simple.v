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
   Simplify uses of the compiler's module [Simplify_simple], after its interface
   middle_end/flambda2/simplify/simplify_simple.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Downwards_acc Flambda2_types Name_mode Simple.

(* simplify_simple.mli:20  val simplify_simple : Downwards_acc.t -> Simple.t -> min_name_mode:Name_mode.t -> Flambda2_types.t * Simple.t *)
Parameter simplify_simple : Downwards_acc.t -> Simple.t -> Name_mode.t -> M (Flambda2_types.t * Simple.t).
Extract Inlined Constant simplify_simple => "Simplify_simple.simplify_simple".
(* simplify_simple.mli:26  val simplify_simple_if_in_scope : Downwards_acc.t -> Simple.t -> min_name_mode:Name_mode.t -> Flambda2_types.t option *)
Parameter simplify_simple_if_in_scope : Downwards_acc.t -> Simple.t -> Name_mode.t -> M (option Flambda2_types.t).
Extract Inlined Constant simplify_simple_if_in_scope => "Simplify_simple.simplify_simple_if_in_scope".
(* simplify_simple.mli:32  type simplify_simples_result = private { simples : Simple.t list; simple_tys : Flambda2_types.t list } *)
Record simplify_simples_result : Type := { simples : list Simple.t; simple_tys : list Flambda2_types.t }.
(* simplify_simple.mli:37  val simplify_simples : Downwards_acc.t -> Simple.t list -> simplify_simples_result *)
Parameter simplify_simples : Downwards_acc.t -> list Simple.t -> M simplify_simples_result.
Extract Inlined Constant simplify_simples => "Simplify_simple.simplify_simples".
