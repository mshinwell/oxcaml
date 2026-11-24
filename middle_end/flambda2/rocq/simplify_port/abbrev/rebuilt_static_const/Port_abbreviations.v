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

(* This file follows middle_end/flambda2/simplify/rebuilt_static_const.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9: the abbreviations of
   modules that that file makes itself (lines 18-19), as Rocq's [Module A :=
   P.], for Rebuilt_static_const.v (GUIDE.md, section 7, ABBREVIATIONS OF
   MODULES). The OCaml text at the head of Rebuilt_static_const.v has the
   compiler's own lines, [module A = P]. What is not from that file: the
   [Require] lines; and the name of the library: every such library is named
   Port_abbreviations, because Rocq writes [open Port_abbreviations] in an
   extracted file that needs it, and runtime/port_abbreviations.ml is that
   (empty) module. *)

From SimplifyPort.decl Require Are_rebuilding_terms Static_const.

Module ART := Are_rebuilding_terms.
Module SC := Static_const.
