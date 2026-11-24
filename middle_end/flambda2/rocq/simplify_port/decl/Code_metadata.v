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
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter code_id : t -> M Code_id.t.
Extract Inlined Constant code_id => "Code_metadata.code_id".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter params_arity : t -> M Flambda_arity.t_Complex.
Extract Inlined Constant params_arity => "Code_metadata.params_arity".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter param_modes : t -> M (list Alloc_mode.For_types.t).
Extract Inlined Constant param_modes => "Code_metadata.param_modes".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter first_complex_local_param : t -> M First_complex_local_param.t.
Extract Inlined Constant first_complex_local_param => "Code_metadata.first_complex_local_param".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter result_arity : t -> M Flambda_arity.t_Complex.
Extract Inlined Constant result_arity => "Code_metadata.result_arity".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter result_types : t -> M (Or_unknown_or_bottom.t Result_types.t).
Extract Inlined Constant result_types => "Code_metadata.result_types".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter result_mode : t -> M Lambda.return_mode.
Extract Inlined Constant result_mode => "Code_metadata.result_mode".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter stub : t -> M bool.
Extract Inlined Constant stub => "Code_metadata.stub".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter zero_alloc_attribute : t -> M Zero_alloc_attribute.t.
Extract Inlined Constant zero_alloc_attribute => "Code_metadata.zero_alloc_attribute".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter cold : t -> M bool.
Extract Inlined Constant cold => "Code_metadata.cold".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter is_a_functor : t -> M bool.
Extract Inlined Constant is_a_functor => "Code_metadata.is_a_functor".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter recursive : t -> M Recursive.t.
Extract Inlined Constant recursive => "Code_metadata.recursive".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter cost_metrics : t -> M Cost_metrics.t.
Extract Inlined Constant cost_metrics => "Code_metadata.cost_metrics".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter dbg : t -> M Debuginfo.t.
Extract Inlined Constant dbg => "Code_metadata.dbg".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter is_tupled : t -> M bool.
Extract Inlined Constant is_tupled => "Code_metadata.is_tupled".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter inlining_decision : t -> M Function_decl_inlining_decision_type.t.
Extract Inlined Constant inlining_decision => "Code_metadata.inlining_decision".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter absolute_history : t -> M Inlining_history.Absolute.t.
Extract Inlined Constant absolute_history => "Code_metadata.absolute_history".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter relative_history : t -> M Inlining_history.Relative.t.
Extract Inlined Constant relative_history => "Code_metadata.relative_history".
(* code_metadata.mli:93  include Code_metadata_accessors_result_type with type 'a t := t *)
Parameter function_slot_size : t -> M int.
Extract Inlined Constant function_slot_size => "Code_metadata.function_slot_size".
(* code_metadata.mli:95  type 'a create_type = Code_id.t -> newer_version_of:Code_id.t option -> params_arity:[`Complex] Flambda_arity.t -> param_modes:Alloc_mode.For_types.t list -> first_complex_local_param:First_complex_local_param.t -> result_arity:[`Complex] Flambda_arity.t -> result_types:Result_types.t Or_unknown_or_bottom.t -> result_mode:Lambda.return_mode -> stub:bool -> inline:Inline_attribute.t -> zero_allo... *)
Definition create_type (A : Type) : Type := Code_id.t -> option Code_id.t -> Flambda_arity.t_Complex -> list Alloc_mode.For_types.t -> First_complex_local_param.t -> Flambda_arity.t_Complex -> Or_unknown_or_bottom.t Result_types.t -> Lambda.return_mode -> bool -> Inline_attribute.t -> Zero_alloc_attribute.t -> Poll_attribute.t -> Regalloc_attribute.t -> Regalloc_param_attribute.t -> bool -> bool -> bool -> Recursive.t -> Cost_metrics.t -> Inlining_arguments.t -> Debuginfo.t -> bool -> bool -> Function_decl_inlining_decision_type.t -> Inlining_history.Absolute.t -> Inlining_history.Relative.t -> Loopify_attribute.t -> M A.
Extract Constant create_type "'a1" => "('a1) Code_metadata.create_type".
(* code_metadata.mli:125  val createk : (t -> 'a) -> 'a create_type *)
Parameter createk : forall {A : Type}, (t -> M A) -> create_type A.
Extract Inlined Constant createk => "Code_metadata.createk".
(* code_metadata.mli:133  val with_cost_metrics : Cost_metrics.t -> t -> t *)
Parameter with_cost_metrics : Cost_metrics.t -> t -> M t.
Extract Inlined Constant with_cost_metrics => "Code_metadata.with_cost_metrics".
