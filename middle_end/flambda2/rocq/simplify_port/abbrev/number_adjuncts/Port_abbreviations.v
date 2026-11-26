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

(* This file follows middle_end/flambda2/simplify/number_adjuncts.ml
   (Git blob 52f4c782af5d40a6c8cfc343a7fa9c1881d76106): the abbreviations of
   modules that that file makes itself (lines 18-25), as Rocq's [Module A :=
   P.], for Number_adjuncts.v (GUIDE.md, section 7, ABBREVIATIONS OF MODULES).
   The OCaml text at the head of Number_adjuncts.v has the compiler's own lines,
   [module A = P]. What is not from that file: the [Require] lines; and the
   name of the library: every such library is named Port_abbreviations,
   because Rocq writes [open Port_abbreviations] in an extracted file that
   needs it, and runtime/port_abbreviations.ml is that (empty) module. *)

From SimplifyPort.decl Require Flambda_kind Flambda2_types Numeric_types.

Module K := Flambda_kind.
Module T := Flambda2_types.
Module Float32_by_bit_pattern := Numeric_types.Float32_by_bit_pattern.
Module Float_by_bit_pattern := Numeric_types.Float_by_bit_pattern.
Module Int8 := Numeric_types.Int8.
Module Int16 := Numeric_types.Int16.
Module Int32 := Numeric_types.Int32.
Module Int64 := Numeric_types.Int64.
