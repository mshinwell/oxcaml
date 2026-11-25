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

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Mutable_unboxing], after its interface
   middle_end/flambda2/simplify/flow/mutable_unboxing.mli
   (Git blob e27855aa03b44fce9567db452fba597e8265097d). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Control_flow_graph Dominator_graph Flow_types Format Name Simple Target_system.

(* mutable_unboxing.mli:15  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Mutable_unboxing.t".
(* mutable_unboxing.mli:17  val create : dom:Dominator_graph.alias_map -> dom_graph:Dominator_graph.t -> source_info:Flow_types.Acc.t -> control_flow_graph:Control_flow_graph.t -> required_names:Name.Set.t -> return_continuation:Continuation.t -> exn_continuation:Continuation.t -> machine_width:Target_system.Machine_width.t -> t *)
Parameter create : Dominator_graph.alias_map -> Dominator_graph.t -> Flow_types.Acc.t -> Control_flow_graph.t -> Name.Set_.t -> Continuation.t -> Continuation.t -> Target_system.Machine_width.t -> M t.
Extract Inlined Constant create => "Mutable_unboxing.create".
(* mutable_unboxing.mli:28  val make_result : t -> Flow_types.Mutable_unboxing_result.t * Simple.Set.t *)
Parameter make_result : t -> M (Flow_types.Mutable_unboxing_result.t * Simple.Set_.t).
Extract Inlined Constant make_result => "Mutable_unboxing.make_result".
(* mutable_unboxing.mli:30  val pp_node : t -> Format.formatter -> Continuation.t -> unit *)
Parameter pp_node : t -> Format.formatter -> Continuation.t -> M unit.
Extract Inlined Constant pp_node => "Mutable_unboxing.pp_node".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Mutable_unboxing. End Mutable_unboxing.
