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
   Simplify uses of the compiler's module [Build_unboxing_denv], after its interface
   middle_end/flambda2/simplify/unboxing/build_unboxing_denv.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Downwards_env Unboxing_types Variable_.

(* build_unboxing_denv.mli:22  val denv_of_decision : DE.t -> param_var:Variable.t -> Unboxing_types.decision -> DE.t *)
Parameter denv_of_decision : Downwards_env.t -> Variable_.t -> Unboxing_types.decision_ -> M Downwards_env.t.
Extract Inlined Constant denv_of_decision => "Build_unboxing_denv.denv_of_decision".
