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
   Simplify uses of the compiler's module [Code], after its interface
   middle_end/flambda2/terms/code.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Code0 Code_id Code_metadata Debuginfo First_complex_local_param Flambda Flambda_arity Format Inline_attribute Inlining_arguments Inlining_history Lambda Loopify_attribute Name_occurrences Poll_attribute Regalloc_attribute Regalloc_param_attribute Zero_alloc_attribute.

(* code.mli:21  type t = Flambda.Function_params_and_body.t Code0.t *)
Definition t : Type := Code0.t Flambda.Function_params_and_body.t.
Extract Inlined Constant t => "Code.t".
(* code.mli:23  val code_metadata : t -> Code_metadata.t *)
Parameter code_metadata : t -> M Code_metadata.t.
Extract Inlined Constant code_metadata => "Code.code_metadata".
(* code.mli:25  val params_and_body : t -> Flambda.Function_params_and_body.t *)
Parameter params_and_body : t -> M Flambda.Function_params_and_body.t.
Extract Inlined Constant params_and_body => "Code.params_and_body".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter code_id : t -> M Code_id.t.
Extract Inlined Constant code_id => "Code.code_id".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter newer_version_of : t -> M (option Code_id.t).
Extract Inlined Constant newer_version_of => "Code.newer_version_of".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter params_arity : t -> M Flambda_arity.t.
Extract Inlined Constant params_arity => "Code.params_arity".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter param_modes : t -> M (list Alloc_mode.For_types.t).
Extract Inlined Constant param_modes => "Code.param_modes".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter first_complex_local_param : t -> M First_complex_local_param.t.
Extract Inlined Constant first_complex_local_param => "Code.first_complex_local_param".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter result_arity : t -> M Flambda_arity.t.
Extract Inlined Constant result_arity => "Code.result_arity".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter result_mode : t -> M Lambda.return_mode.
Extract Inlined Constant result_mode => "Code.result_mode".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter stub : t -> M bool.
Extract Inlined Constant stub => "Code.stub".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter inline : t -> M Inline_attribute.t.
Extract Inlined Constant inline => "Code.inline".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter zero_alloc_attribute : t -> M Zero_alloc_attribute.t.
Extract Inlined Constant zero_alloc_attribute => "Code.zero_alloc_attribute".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter poll_attribute : t -> M Poll_attribute.t.
Extract Inlined Constant poll_attribute => "Code.poll_attribute".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter regalloc_attribute : t -> M Regalloc_attribute.t.
Extract Inlined Constant regalloc_attribute => "Code.regalloc_attribute".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter regalloc_param_attribute : t -> M Regalloc_param_attribute.t.
Extract Inlined Constant regalloc_param_attribute => "Code.regalloc_param_attribute".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter cold : t -> M bool.
Extract Inlined Constant cold => "Code.cold".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter is_a_functor : t -> M bool.
Extract Inlined Constant is_a_functor => "Code.is_a_functor".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter is_opaque : t -> M bool.
Extract Inlined Constant is_opaque => "Code.is_opaque".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter inlining_arguments : t -> M Inlining_arguments.t.
Extract Inlined Constant inlining_arguments => "Code.inlining_arguments".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter dbg : t -> M Debuginfo.t.
Extract Inlined Constant dbg => "Code.dbg".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter is_tupled : t -> M bool.
Extract Inlined Constant is_tupled => "Code.is_tupled".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter absolute_history : t -> M Inlining_history.Absolute.t.
Extract Inlined Constant absolute_history => "Code.absolute_history".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter relative_history : t -> M Inlining_history.Relative.t.
Extract Inlined Constant relative_history => "Code.relative_history".
(* code.mli:27  include Code_metadata.Code_metadata_accessors_result_type with type 'a t := t *)
Parameter loopify : t -> M Loopify_attribute.t.
Extract Inlined Constant loopify => "Code.loopify".
(* code.mli:29  val create_with_metadata : params_and_body:Flambda.Function_params_and_body.t -> free_names_of_params_and_body:Name_occurrences.t -> code_metadata:Code_metadata.t -> t *)
Parameter create_with_metadata : Flambda.Function_params_and_body.t -> Name_occurrences.t -> Code_metadata.t -> M t.
Extract Inlined Constant create_with_metadata => "Code.create_with_metadata".
(* code.mli:35  val create : params_and_body:Flambda.Function_params_and_body.t -> free_names_of_params_and_body:Name_occurrences.t -> t Code_metadata.create_type *)
Parameter create : Flambda.Function_params_and_body.t -> Name_occurrences.t -> Code_metadata.create_type t.
Extract Inlined Constant create => "Code.create".
(* code.mli:40  val with_code_id : Code_id.t -> t -> t *)
Parameter with_code_id : Code_id.t -> t -> M t.
Extract Inlined Constant with_code_id => "Code.with_code_id".
(* code.mli:49  val with_newer_version_of : Code_id.t option -> t -> t *)
Parameter with_newer_version_of : option Code_id.t -> t -> M t.
Extract Inlined Constant with_newer_version_of => "Code.with_newer_version_of".
(* code.mli:51  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Code.print".
(* code.mli:53  include Contains_names.S with type t := t *)
Parameter free_names : t -> M Name_occurrences.t.
Extract Inlined Constant free_names => "Code.free_names".
