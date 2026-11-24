(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/flow/flow_analysis.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9: the abbreviations of
   modules that that file makes itself (line 15), as Rocq's [Module A := P.],
   for flow/Flow_analysis.v (GUIDE.md, section 7, ABBREVIATIONS OF MODULES).
   The OCaml text at the head of flow/Flow_analysis.v has the compiler's own
   lines, [module A = P]. What is not from that file: the [Require] lines; and
   the name of the library: every such library is named Port_abbreviations,
   because Rocq writes [open Port_abbreviations] in an extracted file that
   needs it, and runtime/port_abbreviations.ml is that (empty) module. *)

From SimplifyPort.decl Require Flow_types.

Module T := Flow_types.
