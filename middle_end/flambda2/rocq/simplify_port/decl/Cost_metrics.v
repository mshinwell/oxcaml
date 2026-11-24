(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Cost_metrics], after its interface
   middle_end/flambda2/terms/cost_metrics.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_size.

(* cost_metrics.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Cost_metrics.t".
(* cost_metrics.mli:19  val zero : t *)
Parameter zero : t.
Extract Inlined Constant zero => "Cost_metrics.zero".
(* cost_metrics.mli:21  val from_size : Code_size.t -> t *)
Parameter from_size : Code_size.t -> M t.
Extract Inlined Constant from_size => "Cost_metrics.from_size".
(* cost_metrics.mli:31  type code_characteristics = { cost_metrics : t; function_slot_size : int } *)
Parameter code_characteristics : Type.
Extract Inlined Constant code_characteristics => "Cost_metrics.code_characteristics".
