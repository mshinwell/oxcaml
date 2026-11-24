(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Aspen Smith, Jane Street, New York                   *)
(*                                                                        *)
(*   Copyright 2025 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplify_quaternary_primitive], after its interface
   middle_end/flambda2/simplify/simplify_quaternary_primitive.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Bound_var Debuginfo Downwards_acc Flambda2_types Flambda_primitive Simple Simplify_primitive_result.

(* simplify_quaternary_primitive.ml:17  let simplify_atomic_compare_and_set_or_exchange_args *)
Parameter simplify_atomic_compare_and_set_or_exchange_args : Flambda_primitive.Block_access_field_kind.t -> Downwards_acc.t -> Flambda2_types.t -> Flambda2_types.t -> M Flambda_primitive.Block_access_field_kind.t.
Extract Inlined Constant simplify_atomic_compare_and_set_or_exchange_args => "Simplify_quaternary_primitive.simplify_atomic_compare_and_set_or_exchange_args".
(* simplify_quaternary_primitive.ml:45  let simplify_atomic_compare_and_set offset_units *)
Parameter simplify_atomic_compare_and_set : forall {A A1 A2 A3 : Type}, Flambda_primitive.atomic_offset_units -> Flambda_primitive.Block_access_field_kind.t -> Alloc_mode.For_assignments.t -> A -> Downwards_acc.t -> A1 -> Debuginfo.t -> Simple.t -> A2 -> Simple.t -> A3 -> Simple.t -> Flambda2_types.t -> Simple.t -> Flambda2_types.t -> Bound_var.t -> M Simplify_primitive_result.t.
Extract Inlined Constant simplify_atomic_compare_and_set => "Simplify_quaternary_primitive.simplify_atomic_compare_and_set".
(* simplify_quaternary_primitive.ml:70  let simplify_atomic_compare_exchange offset_units *)
Parameter simplify_atomic_compare_exchange : forall {A A1 A2 A3 : Type}, Flambda_primitive.atomic_offset_units -> Flambda_primitive.Block_access_field_kind.t -> Flambda_primitive.Block_access_field_kind.t -> Alloc_mode.For_assignments.t -> A -> Downwards_acc.t -> A1 -> Debuginfo.t -> Simple.t -> A2 -> Simple.t -> A3 -> Simple.t -> Flambda2_types.t -> Simple.t -> Flambda2_types.t -> Bound_var.t -> M Simplify_primitive_result.t.
Extract Inlined Constant simplify_atomic_compare_exchange => "Simplify_quaternary_primitive.simplify_atomic_compare_exchange".
(* simplify_quaternary_primitive.ml:98  let simplify_quaternary_primitive dacc original_prim *)
Parameter simplify_quaternary_primitive : forall {A A1 : Type}, Downwards_acc.t -> Flambda_primitive.t -> Flambda_primitive.quaternary_primitive -> Simple.t -> A -> Simple.t -> A1 -> Simple.t -> Flambda2_types.t -> Simple.t -> Flambda2_types.t -> Debuginfo.t -> Bound_var.t -> M Simplify_primitive_result.t.
Extract Inlined Constant simplify_quaternary_primitive => "Simplify_quaternary_primitive.simplify_quaternary_primitive".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_quaternary_primitive. End Simplify_quaternary_primitive.
