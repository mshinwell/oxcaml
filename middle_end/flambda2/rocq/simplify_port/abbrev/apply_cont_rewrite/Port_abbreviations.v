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

(* This file follows middle_end/flambda2/simplify/apply_cont_rewrite.ml
   (Git blob 4c8cae93858064fb677a2e1aa0d4adeaace66b84): the abbreviations of
   modules that that file makes itself (lines 17-19), as Rocq's [Module A :=
   P.], for Apply_cont_rewrite.v (GUIDE.md, section 7, ABBREVIATIONS OF
   MODULES). The OCaml text at the head of Apply_cont_rewrite.v has the
   compiler's own lines, [module A = P]. What is not from that file: the
   [Require] lines; and the name of the library: every such library is named
   Port_abbreviations, because Rocq writes [open Port_abbreviations] in an
   extracted file that needs it, and runtime/port_abbreviations.ml is that
   (empty) module. *)

From SimplifyPort.decl Require Continuation_extra_params_and_args
  Apply_cont_rewrite_id.

Module EPA := Continuation_extra_params_and_args.
Module EA := EPA.Extra_arg.
Module Id := Apply_cont_rewrite_id.
