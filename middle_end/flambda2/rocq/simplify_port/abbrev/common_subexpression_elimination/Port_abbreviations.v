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

(* This file follows
   middle_end/flambda2/simplify/common_subexpression_elimination.ml
   (Git blob 2d097a00e62af6c65f516baa0932149da53d2d65): the abbreviations of
   modules that that file makes itself (lines 18-29), as Rocq's [Module A :=
   P.], for Common_subexpression_elimination.v (GUIDE.md, section 7,
   ABBREVIATIONS OF MODULES). The OCaml text at the head of
   Common_subexpression_elimination.v has the compiler's own lines, [module A =
   P]. What is not from that file: the [Require] lines; and the name of the
   library: every such library is named Port_abbreviations, because Rocq writes
   [open Port_abbreviations] in an extracted file that needs it, and
   runtime/port_abbreviations.ml is that
   (empty) module. *)

From SimplifyPort.decl Require Continuation_extra_params_and_args
  Flambda_primitive Flambda_kind Bound_parameter Name_mode
  Apply_cont_rewrite_id Flambda2_types ListLabels.

Module EA := Continuation_extra_params_and_args.Extra_arg.
Module EP := Flambda_primitive.Eligible_for_cse.
Module EPA := Continuation_extra_params_and_args.
Module K := Flambda_kind.
Module BP := Bound_parameter.
Module NM := Name_mode.
Module P := Flambda_primitive.
Module RI := Apply_cont_rewrite_id.
Module T := Flambda2_types.
Module TE := Flambda2_types.Typing_env.
Module TEE := Flambda2_types.Typing_env_extension.
Module List := ListLabels.
