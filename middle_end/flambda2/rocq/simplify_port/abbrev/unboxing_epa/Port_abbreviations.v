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

(* This file follows middle_end/flambda2/simplify/unboxing/unboxing_epa.ml
   (Git blob 792ec77dbde724d5607fc29ad4e507bd3cb4ff22): the abbreviations of
   modules that that file makes itself (lines 18-19), as Rocq's [Module A :=
   P.], for unboxing/Unboxing_epa.v (GUIDE.md, section 7, ABBREVIATIONS OF
   MODULES). The OCaml text at the head of unboxing/Unboxing_epa.v has the
   compiler's own lines, [module A = P]. What is not from that file: the
   [Require] lines; and the name of the library: every such library is named
   Port_abbreviations, because Rocq writes [open Port_abbreviations] in an
   extracted file that needs it, and runtime/port_abbreviations.ml is that
   (empty) module. *)

From SimplifyPort.decl Require Unboxing_types.

Module U := Unboxing_types.
Module Extra_param_and_args := U.Extra_param_and_args.
