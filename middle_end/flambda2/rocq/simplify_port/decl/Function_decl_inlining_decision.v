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
   Simplify uses of the compiler's module [Function_decl_inlining_decision], after its interface
   middle_end/flambda2/simplify_shared/function_decl_inlining_decision.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Cost_metrics Function_decl_inlining_decision_type Inline_attribute Inlining_arguments Recursive.

(* function_decl_inlining_decision.mli:17  val make_decision : inlining_arguments:Inlining_arguments.t -> inline:Inline_attribute.t -> stub:bool -> cost_metrics:Cost_metrics.t -> is_a_functor:bool -> recursive:Recursive.t -> Function_decl_inlining_decision_type.t *)
Parameter make_decision : Inlining_arguments.t -> Inline_attribute.t -> bool -> Cost_metrics.t -> bool -> Recursive.t -> M Function_decl_inlining_decision_type.t.
Extract Inlined Constant make_decision => "Function_decl_inlining_decision.make_decision".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Function_decl_inlining_decision. End Function_decl_inlining_decision.
