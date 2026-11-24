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
   Simplify uses of the compiler's module [Function_decl_inlining_decision_type], after its interface
   middle_end/flambda2/terms/function_decl_inlining_decision_type.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* function_decl_inlining_decision_type.mli:17  type t = | Not_yet_decided | Never_inline_attribute | Function_body_too_large of Code_size.t | Functor_body_too_large of Code_size.t | Stub | Attribute_inline ( * CR mshinwell/bclement: we could consider combining Small_function and Small_functor in the future, with a flag for functors * ) | Small_function of { size : Code_size.t; small_function_size : Code_size.t } | Small_functor of { size : ... *)
Parameter t : Type.
Extract Inlined Constant t => "Function_decl_inlining_decision_type.t".
