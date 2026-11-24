(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*      Pierre Chambart & Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplify_nullary_primitive], after its interface
   middle_end/flambda2/simplify/simplify_nullary_primitive.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_var Debuginfo Downwards_acc Flambda_primitive Simplify_primitive_result.

(* simplify_nullary_primitive.mli:18  val simplify_nullary_primitive : Downwards_acc.t -> Flambda_primitive.t -> Flambda_primitive.nullary_primitive -> Debuginfo.t -> result_var:Bound_var.t -> Simplify_primitive_result.t *)
Parameter simplify_nullary_primitive : Downwards_acc.t -> Flambda_primitive.t -> Flambda_primitive.nullary_primitive -> Debuginfo.t -> Bound_var.t -> M Simplify_primitive_result.t.
Extract Inlined Constant simplify_nullary_primitive => "Simplify_nullary_primitive.simplify_nullary_primitive".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_nullary_primitive. End Simplify_nullary_primitive.
