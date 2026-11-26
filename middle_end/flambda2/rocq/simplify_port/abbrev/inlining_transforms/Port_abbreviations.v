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

(* This file follows
   middle_end/flambda2/simplify/inlining/inlining_transforms.ml
   (Git blob e5caa4eaf80f6a0159795c782a62befdab67400c): the abbreviations of
   modules that that file makes itself (lines 18-21), as Rocq's [Module A :=
   P.], for inlining/Inlining_transforms.v (GUIDE.md, section 7, ABBREVIATIONS
   OF MODULES). The OCaml text at the head of inlining/Inlining_transforms.v has
   the compiler's own lines, [module A = P]. What is not from that file: the
   [Require] lines; and the name of the library: every such library is named
   Port_abbreviations, because Rocq writes [open Port_abbreviations] in an
   extracted file that needs it, and runtime/port_abbreviations.ml is that
   (empty) module. *)

From SimplifyPort.decl Require Downwards_acc Downwards_env Flambda2_types
  Bound_var.

Module DA := Downwards_acc.
Module DE := Downwards_env.
Module FT := Flambda2_types.Function_type.
Module VB := Bound_var.
