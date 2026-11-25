(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Copyright 2022 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)
(** [@zero_alloc ...] annotations on function declaration (not call sites) *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Zero_alloc_attribute], after its interface
   middle_end/flambda2/terms/zero_alloc_attribute.mli
   (Git blob 8b95288b0d94685b9bc0153627168f1eccc9f716). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Lambda.

(* zero_alloc_attribute.mli:13  type t = Lambda.zero_alloc_attribute = | Default_zero_alloc | Check of { strict : bool; loc : Location.t; custom_error_msg : string option; partial : bool } | Assume of { strict : bool; never_returns_normally : bool; never_raises : bool; loc : Location.t } *)
Definition t : Type := Lambda.zero_alloc_attribute.
Extract Inlined Constant t => "Zero_alloc_attribute.t".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Zero_alloc_attribute. End Zero_alloc_attribute.
