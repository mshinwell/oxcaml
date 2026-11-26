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

(* This file follows middle_end/flambda2/simplify/env/continuation_uses.ml
   (Git blob f52e9a52a77626a0a6d3c3748ec75aa586724a50): the abbreviations of
   modules that that file makes itself (lines 17-19), as Rocq's [Module A :=
   P.], for env/Continuation_uses.v (GUIDE.md, section 7, ABBREVIATIONS OF
   MODULES). The OCaml text at the head of env/Continuation_uses.v has the
   compiler's own lines, [module A = P]. What is not from that file: the
   [Require] lines; and the name of the library: every such library is named
   Port_abbreviations, because Rocq writes [open Port_abbreviations] in an
   extracted file that needs it, and runtime/port_abbreviations.ml is that
   (empty) module. *)

From SimplifyPort.decl Require Downwards_env Flambda2_types
  One_continuation_use.

Module DE := Downwards_env.
Module T := Flambda2_types.
Module U := One_continuation_use.
