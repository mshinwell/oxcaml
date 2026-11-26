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

(* This file follows middle_end/flambda2/simplify/simplify_unary_primitive.ml
   (Git blob 10de6d9b44969d0e3948ac61e2cbf5fb2ea666fd): the abbreviations of
   modules that that file makes itself (lines 18-22), as Rocq's [Module A :=
   P.], for Simplify_unary_primitive.v (GUIDE.md, section 7, ABBREVIATIONS OF
   MODULES). The OCaml text at the head of Simplify_unary_primitive.v has the
   compiler's own lines, [module A = P]. What is not from that file: the
   [Require] lines; and the name of the library: every such library is named
   Port_abbreviations, because Rocq writes [open Port_abbreviations] in an
   extracted file that needs it, and runtime/port_abbreviations.ml is that
   (empty) module. *)

From SimplifyPort.decl Require Number_adjuncts Numeric_types.

Module A := Number_adjuncts.
Module Float32 := Numeric_types.Float32_by_bit_pattern.
Module Float := Numeric_types.Float_by_bit_pattern.
Module Int32 := Numeric_types.Int32.
Module Int64 := Numeric_types.Int64.
