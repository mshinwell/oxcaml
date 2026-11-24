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

(* This file follows middle_end/flambda2/simplify/simplify_simple.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9: the abbreviations of modules that
   that file makes itself (lines 17-19), as Rocq's [Module A := P.], for
   Simplify_simple.v (GUIDE.md, section 7, ABBREVIATIONS OF MODULES). The
   OCaml text at the head of Simplify_simple.v has the compiler's own lines,
   [module A = P]. What is not from that file: the [Require] lines; and the
   name of the library: every such library is named Port_abbreviations,
   because Rocq writes [open Port_abbreviations] in an extracted file that
   needs it, and runtime/port_abbreviations.ml is that (empty) module. *)

From SimplifyPort.decl Require Downwards_acc Flambda2_types.

Module DA := Downwards_acc.
Module T := Flambda2_types.
Module TE := T.Typing_env.
