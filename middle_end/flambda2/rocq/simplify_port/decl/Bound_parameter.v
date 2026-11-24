(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018--2020 OCamlPro SAS                                    *)
(*   Copyright 2018--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Bound_parameter], after its interface
   middle_end/flambda2/bound_identifiers/bound_parameter.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_debug_uid Variable_.

(* bound_parameter.mli:18  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Bound_parameter.t".
(* bound_parameter.mli:27  val var_and_uid : t -> Variable.t * Flambda_debug_uid.t *)
Parameter var_and_uid : t -> M (Variable_.t * Flambda_debug_uid.t).
Extract Inlined Constant var_and_uid => "Bound_parameter.var_and_uid".
