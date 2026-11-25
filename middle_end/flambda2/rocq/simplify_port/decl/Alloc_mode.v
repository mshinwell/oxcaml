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
   (Git blob d3c8da53c1ac5a6afd35992b782e5d6ecafb3901). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Name_occurrences Variable_.

Module For_types.
  (* alloc_mode.mli:17  type t = private | Heap ( ** Normal allocation on the OCaml heap. * ) | Local ( ** Allocation on the local allocation stack. * ) | Heap_or_local ( ** Allocation with unknown location * ) *)
  Inductive t : Type :=
  | Heap : t
  | Local : t
  | Heap_or_local : t.
  Extract Inductive t => "Alloc_mode.For_types.t" [ "Alloc_mode.For_types.Heap" "Alloc_mode.For_types.Local" "Alloc_mode.For_types.Heap_or_local" ].
  (* alloc_mode.mli:28  val heap : t *)
  Parameter heap : t.
  Extract Inlined Constant heap => "Alloc_mode.For_types.heap".
  (* alloc_mode.mli:34  val unknown : unit -> t *)
  Parameter unknown : unit -> M t.
  Extract Inlined Constant unknown => "Alloc_mode.For_types.unknown".
End For_types.
Module For_applications.
  (* alloc_mode.mli:47  type t = private | Not_alloc_stack of { alloc_region : Variable.t } ( ** Normal allocation on the OCaml heap. * ) | Maybe_alloc_stack of { alloc_region : Variable.t; region : Variable.t; ghost_region : Variable.t } ( ** Allocation on the local allocation stack in the given region. * ) *)
  Inductive t : Type :=
  | Not_alloc_stack : Variable_.t -> t
  | Maybe_alloc_stack : Variable_.t -> Variable_.t -> Variable_.t -> t.
  Extract Inductive t => "Alloc_mode.For_applications.t" [ "(fun x__1 -> (Alloc_mode.For_applications.Not_alloc_stack { alloc_region = x__1 } : Alloc_mode.For_applications.t))" "(fun (x__1, x__2, x__3) -> (Alloc_mode.For_applications.Maybe_alloc_stack { alloc_region = x__1; region = x__2; ghost_region = x__3 } : Alloc_mode.For_applications.t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Alloc_mode.For_applications.t) with Alloc_mode.For_applications.Not_alloc_stack { alloc_region = x__1 } -> f__1 x__1 | Alloc_mode.For_applications.Maybe_alloc_stack { alloc_region = x__1; region = x__2; ghost_region = x__3 } -> f__2 x__1 x__2 x__3)".
  (* alloc_mode.mli:58  val not_alloc_stack : alloc_region:Variable.t -> t *)
  Parameter not_alloc_stack : Variable_.t -> M t.
  Extract Inlined Constant not_alloc_stack => "Alloc_mode.For_applications.not_alloc_stack".
  (* alloc_mode.mli:61  val maybe_alloc_stack : alloc_region:Variable.t -> region:Variable.t -> ghost_region:Variable.t -> t *)
  Parameter maybe_alloc_stack : Variable_.t -> Variable_.t -> Variable_.t -> M t.
  Extract Inlined Constant maybe_alloc_stack => "Alloc_mode.For_applications.maybe_alloc_stack".
  (* alloc_mode.mli:64  val as_type : t -> For_types.t *)
  Parameter as_type : t -> M Alloc_mode.For_types.t.
  Extract Inlined Constant as_type => "Alloc_mode.For_applications.as_type".
  (* alloc_mode.mli:73  val alloc_region : t -> Variable.t *)
  Parameter alloc_region : t -> M Variable_.t.
  Extract Inlined Constant alloc_region => "Alloc_mode.For_applications.alloc_region".
  (* alloc_mode.mli:79  include Bindable.S with type t := t *)
  Parameter free_names : t -> M Name_occurrences.t.
  Extract Inlined Constant free_names => "Alloc_mode.For_applications.free_names".
  (* alloc_mode.mli:79  include Bindable.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Alloc_mode.For_applications.print".
End For_applications.
Module For_allocations.
  (* alloc_mode.mli:84  type t = private | Heap of { alloc_region : Variable.t } ( ** Normal allocation on the OCaml heap. * ) | Local of { alloc_region : Variable.t; region : Variable.t } ( ** Allocation on the local allocation stack in the given region. * ) *)
  Inductive t : Type :=
  | Heap : Variable_.t -> t
  | Local : Variable_.t -> Variable_.t -> t.
  Extract Inductive t => "Alloc_mode.For_allocations.t" [ "(fun x__1 -> (Alloc_mode.For_allocations.Heap { alloc_region = x__1 } : Alloc_mode.For_allocations.t))" "(fun (x__1, x__2) -> (Alloc_mode.For_allocations.Local { alloc_region = x__1; region = x__2 } : Alloc_mode.For_allocations.t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Alloc_mode.For_allocations.t) with Alloc_mode.For_allocations.Heap { alloc_region = x__1 } -> f__1 x__1 | Alloc_mode.For_allocations.Local { alloc_region = x__1; region = x__2 } -> f__2 x__1 x__2)".
  (* alloc_mode.mli:96  val heap : alloc_region:Variable.t -> t *)
  Parameter heap : Variable_.t -> M t.
  Extract Inlined Constant heap => "Alloc_mode.For_allocations.heap".
  (* alloc_mode.mli:99  val local : alloc_region:Variable.t -> region:Variable.t -> t *)
  Parameter local : Variable_.t -> Variable_.t -> M t.
  Extract Inlined Constant local => "Alloc_mode.For_allocations.local".
  (* alloc_mode.mli:101  val as_type : t -> For_types.t *)
  Parameter as_type : t -> M Alloc_mode.For_types.t.
  Extract Inlined Constant as_type => "Alloc_mode.For_allocations.as_type".
End For_allocations.
Module For_assignments.
  (* alloc_mode.mli:116  type t = private | Heap | Local *)
  Parameter t : Type.
  Extract Inlined Constant t => "Alloc_mode.For_assignments.t".
End For_assignments.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Alloc_mode. End Alloc_mode.
