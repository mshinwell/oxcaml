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
   Simplify uses of the compiler's module [Code_metadata], after its interface
   middle_end/flambda2/terms/code_metadata.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Code_id Cost_metrics Debuginfo First_complex_local_param Flambda_arity Function_decl_inlining_decision_type Inline_attribute Inlining_arguments Inlining_history Lambda Loopify_attribute Or_unknown_or_bottom Poll_attribute Recursive Regalloc_attribute Regalloc_param_attribute Result_types Zero_alloc_attribute.

(* code_metadata.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Code_metadata.t".
(* code_metadata.mli:95  type 'a create_type = Code_id.t -> newer_version_of:Code_id.t option -> params_arity:[`Complex] Flambda_arity.t -> param_modes:Alloc_mode.For_types.t list -> first_complex_local_param:First_complex_local_param.t -> result_arity:[`Complex] Flambda_arity.t -> result_types:Result_types.t Or_unknown_or_bottom.t -> result_mode:Lambda.return_mode -> stub:bool -> inline:Inline_attribute.t -> zero_allo... *)
Definition create_type (A : Type) : Type := Code_id.t -> option Code_id.t -> Flambda_arity.t -> list Alloc_mode.For_types.t -> First_complex_local_param.t -> Flambda_arity.t -> Or_unknown_or_bottom.t Result_types.t -> Lambda.return_mode -> bool -> Inline_attribute.t -> Zero_alloc_attribute.t -> Poll_attribute.t -> Regalloc_attribute.t -> Regalloc_param_attribute.t -> bool -> bool -> bool -> Recursive.t -> Cost_metrics.t -> Inlining_arguments.t -> Debuginfo.t -> bool -> bool -> Function_decl_inlining_decision_type.t -> Inlining_history.Absolute.t -> Inlining_history.Relative.t -> Loopify_attribute.t -> M A.
Extract Constant create_type "'a1" => "('a1) Code_metadata.create_type".
