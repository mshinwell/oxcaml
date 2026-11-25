(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of the modules that
   middle_end/flambda2/simplify/flow/control_flow_graph.ml
   (Git blob 4d441f39c6523dfe599369d4ace1b3530fc283b8) makes for itself by
   applying a functor of another part of the compiler, and of what the
   file uses of them. The port keeps the definitions of these modules as
   they are in the file, and the realisations name them as the file does.
   Made by tools/declgen (see decl/README.md): a change is made there,
   not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation.

(* module G, lines 16-16 of the file *)
Module G.
  (* strongly_connected_components.mli:91  module Make (Id : Id) : S with module Id := Id *)
  Definition directed_graph : Type := Continuation.Map.t Continuation.Set_.t.
  Extract Inlined Constant directed_graph => "G.directed_graph".
  (* strongly_connected_components.mli:91  module Make (Id : Id) : S with module Id := Id *)
  Inductive component : Type :=
  | Has_loop : list Continuation.t -> component
  | No_loop : Continuation.t -> component.
  Extract Inductive component => "G.component" [ "G.Has_loop" "G.No_loop" ].
  (* strongly_connected_components.mli:91  module Make (Id : Id) : S with module Id := Id *)
  Parameter connected_components_sorted_from_roots_to_leaf : directed_graph -> M (array component).
  Extract Inlined Constant connected_components_sorted_from_roots_to_leaf => "G.connected_components_sorted_from_roots_to_leaf".
End G.

(* Not in the file of Simplify: an empty module with the name of this file.
   With it Rocq's extraction writes no [open] of this file, which is not a
   module of OCaml, and prints each of its names in full. *)
Module Control_flow_graph__local. End Control_flow_graph__local.
