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

(* This file follows
   middle_end/flambda2/simplify/inlining/call_site_inlining_decision.ml
   (Git blob 3035e3840781d8b06f8c64bcec35c09f897bc3e1): the abbreviations of
   modules that that file makes itself (lines 18-23, 43), as Rocq's [Module A
   := P.], for inlining/Call_site_inlining_decision.v (GUIDE.md, section 7,
   ABBREVIATIONS OF MODULES). The OCaml text at the head of
   inlining/Call_site_inlining_decision.v has the compiler's own lines,
   [module A = P]. What is not from that file: the [Require] lines; and the
   name of the library: every such library is named Port_abbreviations,
   because Rocq writes [open Port_abbreviations] in an extracted file that
   needs it, and runtime/port_abbreviations.ml is that (empty) module. *)

From SimplifyPort.decl Require Downwards_env Downwards_acc Flambda2_types
  Upwards_acc Upwards_env.

Module DE := Downwards_env.
Module DA := Downwards_acc.
Module T := Flambda2_types.
Module TE := T.Typing_env.
Module UA := Upwards_acc.
Module UE := Upwards_env.
Module FT := Flambda2_types.Function_type.
