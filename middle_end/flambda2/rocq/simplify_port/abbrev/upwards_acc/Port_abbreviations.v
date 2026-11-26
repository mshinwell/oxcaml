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

(* This file follows middle_end/flambda2/simplify/env/upwards_acc.ml
   (Git blob 146d4b453ca49d8e3fac1321791bf4ca168cdeb2): the abbreviations of
   modules that that file makes itself (lines 17-22), as Rocq's [Module A :=
   P.], for env/Upwards_acc.v (GUIDE.md, section 7, ABBREVIATIONS OF MODULES).
   The OCaml text at the head of env/Upwards_acc.v has the compiler's own lines,
   [module A = P]. What is not from that file: the [Require] lines; and the
   name of the library: every such library is named Port_abbreviations,
   because Rocq writes [open Port_abbreviations] in an extracted file that
   needs it, and runtime/port_abbreviations.ml is that (empty) module. *)

From SimplifyPort.decl Require Are_rebuilding_terms Downwards_acc
  Downwards_env Lifted_constant_state Flambda2_types Upwards_env.

Module ART := Are_rebuilding_terms.
Module DA := Downwards_acc.
Module DE := Downwards_env.
Module LCS := Lifted_constant_state.
Module TE := Flambda2_types.Typing_env.
Module UE := Upwards_env.
