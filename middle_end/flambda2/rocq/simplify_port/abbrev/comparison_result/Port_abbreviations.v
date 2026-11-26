(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Vincent Laviron, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023 OCamlPro SAS                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/comparison_result.ml
   (Git blob f430725de413111dad62d5b58d981510619181b7): the abbreviations of
   modules that that file makes itself (line 15), as Rocq's [Module A := P.],
   for Comparison_result.v (GUIDE.md, section 7, ABBREVIATIONS OF MODULES).
   The OCaml text at the head of Comparison_result.v has the compiler's own
   lines, [module A = P]. What is not from that file: the [Require] lines; and
   the name of the library: every such library is named Port_abbreviations,
   because Rocq writes [open Port_abbreviations] in an extracted file that
   needs it, and runtime/port_abbreviations.ml is that (empty) module. *)

From SimplifyPort.decl Require Flambda_primitive.

Module P := Flambda_primitive.
