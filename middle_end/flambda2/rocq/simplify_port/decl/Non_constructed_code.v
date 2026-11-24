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
   Simplify uses of the compiler's module [Non_constructed_code], after its interface
   middle_end/flambda2/simplify/non_constructed_code.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Code0 Code_id Code_metadata Cost_metrics Debuginfo First_complex_local_param Flambda_arity Format Function_decl_inlining_decision_type Inline_attribute Inlining_arguments Inlining_history Lambda Loopify_attribute Name_occurrences Or_unknown_or_bottom Poll_attribute Recursive Regalloc_attribute Regalloc_param_attribute Renaming Result_types Zero_alloc_attribute.

(* non_constructed_code.mli:20  type t = unit Code0.t *)
Definition t : Type := Code0.t unit.
Extract Inlined Constant t => "Non_constructed_code.t".
(* non_constructed_code.mli:22  val code_metadata : t -> Code_metadata.t *)
Parameter code_metadata : t -> M Code_metadata.t.
Extract Inlined Constant code_metadata => "Non_constructed_code.code_metadata".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter code_id : t -> M Code_id.t.
Extract Inlined Constant code_id => "Non_constructed_code.code_id".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter newer_version_of : t -> M (option Code_id.t).
Extract Inlined Constant newer_version_of => "Non_constructed_code.newer_version_of".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter params_arity : t -> M Flambda_arity.t_Complex.
Extract Inlined Constant params_arity => "Non_constructed_code.params_arity".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter param_modes : t -> M (list Alloc_mode.For_types.t).
Extract Inlined Constant param_modes => "Non_constructed_code.param_modes".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter first_complex_local_param : t -> M First_complex_local_param.t.
Extract Inlined Constant first_complex_local_param => "Non_constructed_code.first_complex_local_param".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter result_arity : t -> M Flambda_arity.t_Complex.
Extract Inlined Constant result_arity => "Non_constructed_code.result_arity".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter result_types : t -> M (Or_unknown_or_bottom.t Result_types.t).
Extract Inlined Constant result_types => "Non_constructed_code.result_types".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter result_mode : t -> M Lambda.return_mode.
Extract Inlined Constant result_mode => "Non_constructed_code.result_mode".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter stub : t -> M bool.
Extract Inlined Constant stub => "Non_constructed_code.stub".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter inline : t -> M Inline_attribute.t.
Extract Inlined Constant inline => "Non_constructed_code.inline".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter zero_alloc_attribute : t -> M Zero_alloc_attribute.t.
Extract Inlined Constant zero_alloc_attribute => "Non_constructed_code.zero_alloc_attribute".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter poll_attribute : t -> M Poll_attribute.t.
Extract Inlined Constant poll_attribute => "Non_constructed_code.poll_attribute".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter regalloc_attribute : t -> M Regalloc_attribute.t.
Extract Inlined Constant regalloc_attribute => "Non_constructed_code.regalloc_attribute".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter regalloc_param_attribute : t -> M Regalloc_param_attribute.t.
Extract Inlined Constant regalloc_param_attribute => "Non_constructed_code.regalloc_param_attribute".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter cold : t -> M bool.
Extract Inlined Constant cold => "Non_constructed_code.cold".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter is_a_functor : t -> M bool.
Extract Inlined Constant is_a_functor => "Non_constructed_code.is_a_functor".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter is_opaque : t -> M bool.
Extract Inlined Constant is_opaque => "Non_constructed_code.is_opaque".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter recursive : t -> M Recursive.t.
Extract Inlined Constant recursive => "Non_constructed_code.recursive".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter cost_metrics : t -> M Cost_metrics.t.
Extract Inlined Constant cost_metrics => "Non_constructed_code.cost_metrics".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter inlining_arguments : t -> M Inlining_arguments.t.
Extract Inlined Constant inlining_arguments => "Non_constructed_code.inlining_arguments".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter dbg : t -> M Debuginfo.t.
Extract Inlined Constant dbg => "Non_constructed_code.dbg".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter is_tupled : t -> M bool.
Extract Inlined Constant is_tupled => "Non_constructed_code.is_tupled".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter is_my_closure_used : t -> M bool.
Extract Inlined Constant is_my_closure_used => "Non_constructed_code.is_my_closure_used".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter inlining_decision : t -> M Function_decl_inlining_decision_type.t.
Extract Inlined Constant inlining_decision => "Non_constructed_code.inlining_decision".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter absolute_history : t -> M Inlining_history.Absolute.t.
Extract Inlined Constant absolute_history => "Non_constructed_code.absolute_history".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter relative_history : t -> M Inlining_history.Relative.t.
Extract Inlined Constant relative_history => "Non_constructed_code.relative_history".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter loopify : t -> M Loopify_attribute.t.
Extract Inlined Constant loopify => "Non_constructed_code.loopify".
(* non_constructed_code.mli:24  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter function_slot_size : t -> M int.
Extract Inlined Constant function_slot_size => "Non_constructed_code.function_slot_size".
(* non_constructed_code.mli:26  val create_with_metadata : free_names_of_params_and_body:Name_occurrences.t -> code_metadata:Code_metadata.t -> t *)
Parameter create_with_metadata : Name_occurrences.t -> Code_metadata.t -> M t.
Extract Inlined Constant create_with_metadata => "Non_constructed_code.create_with_metadata".
(* non_constructed_code.mli:31  val create : free_names_of_params_and_body:Name_occurrences.t -> t Code_metadata.create_type *)
Parameter create : Name_occurrences.t -> Code_metadata.create_type t.
Extract Inlined Constant create => "Non_constructed_code.create".
(* non_constructed_code.mli:35  include Contains_names.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Non_constructed_code.free_names".
(* non_constructed_code.mli:35  include Contains_names.S with type t := t *)
Parameter apply_renaming : t -> Renaming.t -> M t.
Extract Inlined Constant apply_renaming => "Non_constructed_code.apply_renaming".
(* non_constructed_code.mli:37  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Non_constructed_code.print".
