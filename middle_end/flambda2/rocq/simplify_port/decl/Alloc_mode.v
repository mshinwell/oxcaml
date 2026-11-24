(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                  Mark Shinwell, Jane Street Europe                     *)
(*                                                                        *)
(*   Copyright 2022 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Alloc_mode], after its interface
   middle_end/flambda2/bound_identifiers/alloc_mode.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module For_types.
  (* alloc_mode.mli:17  type t = private | Heap ( ** Normal allocation on the OCaml heap. * ) | Local ( ** Allocation on the local allocation stack. * ) | Heap_or_local ( ** Allocation with unknown location * ) *)
  Parameter t : Type.
  Extract Inlined Constant t => "Alloc_mode.For_types.t".
End For_types.
Module For_applications.
  (* alloc_mode.mli:47  type t = private | Not_alloc_stack of { alloc_region : Variable.t } ( ** Normal allocation on the OCaml heap. * ) | Maybe_alloc_stack of { alloc_region : Variable.t; region : Variable.t; ghost_region : Variable.t } ( ** Allocation on the local allocation stack in the given region. * ) *)
  Parameter t : Type.
  Extract Inlined Constant t => "Alloc_mode.For_applications.t".
End For_applications.
