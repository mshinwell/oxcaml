(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/lifted_cont_params.ml
   (Git blob fb354bf3348e0d5ddc534edc64b2252aa4917088): the abbreviations of
   modules that that file makes itself (line 16), as Rocq's [Module A := P.],
   for Lifted_cont_params.v (GUIDE.md, section 7, ABBREVIATIONS OF MODULES).
   The OCaml text at the head of Lifted_cont_params.v has the compiler's own
   lines, [module A = P]. What is not from that file: the [Require] lines; and
   the name of the library: every such library is named Port_abbreviations,
   because Rocq writes [open Port_abbreviations] in an extracted file that
   needs it, and runtime/port_abbreviations.ml is that (empty) module. *)

From SimplifyPort.decl Require Bound_parameter.

Module BP := Bound_parameter.
