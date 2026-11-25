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
   Simplify uses of the compiler's module [Control_flow_graph], after its interface
   middle_end/flambda2/simplify/flow/control_flow_graph.mli
   (Git blob f7d3f636879ee3e9c4ed239e5fce342454f92e78). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Flow_types Format Name Simple Variable_.

(* control_flow_graph.mli:16  type t = { dummy_toplevel_cont : Continuation.t; callers : Continuation.Set.t Continuation.Map.t; parents : Continuation.t Continuation.Map.t; children : Continuation.Set.t Continuation.Map.t } *)
Parameter t : Type.
Extract Inlined Constant t => "Control_flow_graph.t".
(* control_flow_graph.mli:24  val create : dummy_toplevel_cont:Continuation.t -> Flow_types.Acc.t -> t *)
Parameter create : Continuation.t -> Flow_types.Acc.t -> M t.
Extract Inlined Constant create => "Control_flow_graph.create".
(* control_flow_graph.mli:26  val fixpoint : t -> init:'a Continuation.Map.t -> eq:('a -> 'a -> bool) -> f: (caller:Continuation.t -> caller_set:'a -> callee:Continuation.t -> callee_set:'a -> 'a) -> 'a Continuation.Map.t *)
Parameter fixpoint : forall {A : Type}, t -> Continuation.Map.t A -> (A -> A -> M bool) -> (Continuation.t -> A -> Continuation.t -> A -> M A) -> M (Continuation.Map.t A).
Extract Inlined Constant fixpoint => "Control_flow_graph.fixpoint".
(* control_flow_graph.mli:39  val compute_continuation_extra_args_for_aliases : speculative:bool -> required_names:Name.Set.t -> source_info:Flow_types.Acc.t -> unboxed_blocks:Simple.Set.t -> Simple.t Variable.Map.t -> t -> Flow_types.Continuation_param_aliases.t Continuation.Map.t *)
Parameter compute_continuation_extra_args_for_aliases : bool -> Name.Set_.t -> Flow_types.Acc.t -> Simple.Set_.t -> Variable_.Map.t Simple.t -> t -> M (Continuation.Map.t Flow_types.Continuation_param_aliases.t).
Extract Inlined Constant compute_continuation_extra_args_for_aliases => "Control_flow_graph.compute_continuation_extra_args_for_aliases".
Module Dot.
  (* control_flow_graph.mli:50  val print : ctx:int -> df:Flow_types.Acc.t -> print_name:string -> Format.formatter -> return_continuation:Continuation.t -> exn_continuation:Continuation.t -> ?pp_node:(Format.formatter -> Continuation.t -> unit) -> continuation_parameters: Flow_types.Continuation_param_aliases.t Continuation.Map.t -> t -> unit *)
  Parameter print : int -> Flow_types.Acc.t -> string -> Format.formatter -> Continuation.t -> Continuation.t -> option (Format.formatter -> Continuation.t -> M unit) -> Continuation.Map.t Flow_types.Continuation_param_aliases.t -> Control_flow_graph.t -> M unit.
  Extract Inlined Constant print => "(fun x__1 x__2 x__3 x__4 x__5 x__6 x__7 x__8 x__9 -> Control_flow_graph.Dot.print x__1 x__2 x__3 x__4 x__5 x__6 ?pp_node:x__7 x__8 x__9)".
End Dot.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Control_flow_graph. End Control_flow_graph.
