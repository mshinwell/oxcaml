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
   Simplify uses of the compiler's module [Is_unboxing_beneficial], after its interface
   middle_end/flambda2/simplify/unboxing/is_unboxing_beneficial.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Unboxing_types.

(* is_unboxing_beneficial.mli:20  val filter_non_beneficial_decisions : Unboxing_types.decision -> Unboxing_types.decision *)
Parameter filter_non_beneficial_decisions : Unboxing_types.decision_ -> M Unboxing_types.decision_.
Extract Inlined Constant filter_non_beneficial_decisions => "Is_unboxing_beneficial.filter_non_beneficial_decisions".
