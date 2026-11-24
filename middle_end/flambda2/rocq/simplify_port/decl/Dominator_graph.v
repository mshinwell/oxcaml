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
   Simplify uses of the compiler's module [Dominator_graph], after its interface
   middle_end/flambda2/simplify/flow/dominator_graph.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Flambda_kind Flow_types Format Name Simple Stdlib_ Variable_.

Module G.
  (* dominator_graph.mli:15  module G : Strongly_connected_components.S with module Id := Simple *)
  Definition directed_graph : Type := Simple.Map.t Simple.Set_.t.
  Extract Inlined Constant directed_graph => "Dominator_graph.G.directed_graph".
  (* dominator_graph.mli:15  module G : Strongly_connected_components.S with module Id := Simple *)
  Parameter component : Type.
  Extract Inlined Constant component => "Dominator_graph.G.component".
  (* dominator_graph.mli:15  module G : Strongly_connected_components.S with module Id := Simple *)
  Parameter stable_connected_components_sorted_from_roots_to_leaf : list (Simple.t * Simple.Set_.t) -> M (Stdlib_.array component).
  Extract Inlined Constant stable_connected_components_sorted_from_roots_to_leaf => "Dominator_graph.G.stable_connected_components_sorted_from_roots_to_leaf".
  (* dominator_graph.mli:15  module G : Strongly_connected_components.S with module Id := Simple *)
  Parameter connected_components_sorted_from_roots_to_leaf : directed_graph -> M (Stdlib_.array component).
  Extract Inlined Constant connected_components_sorted_from_roots_to_leaf => "Dominator_graph.G.connected_components_sorted_from_roots_to_leaf".
  (* dominator_graph.mli:15  module G : Strongly_connected_components.S with module Id := Simple *)
  Parameter component_graph : directed_graph -> M (Stdlib_.array (component * list int)).
  Extract Inlined Constant component_graph => "Dominator_graph.G.component_graph".
End G.
(* dominator_graph.mli:18  type t = { required_names : Name.Set.t; params_kind : Flambda_kind.With_subkind.t Variable.Map.t; graph : G.directed_graph; dominator_roots : Simple.Set.t ( * variables that are dominated only by themselves, usually because a constant or a symbol can flow to that variable, and thus that variable cannot be dominated by another variable. * ) } *)
Record t : Type := { required_names : Name.Set_.t; params_kind : Variable_.Map.t Flambda_kind.With_subkind.t; graph : Dominator_graph.G.directed_graph; dominator_roots : Simple.Set_.t }.
(* dominator_graph.mli:28  type alias_map = Simple.t Variable.Map.t *)
Definition alias_map : Type := Variable_.Map.t Simple.t.
Extract Inlined Constant alias_map => "Dominator_graph.alias_map".
(* dominator_graph.mli:31  val create : required_names:Name.Set.t -> return_continuation:Continuation.t -> exn_continuation:Continuation.t -> Flow_types.Continuation_info.t Continuation.Map.t -> t *)
Parameter create : Name.Set_.t -> Continuation.t -> Continuation.t -> Continuation.Map.t Flow_types.Continuation_info.t -> M t.
Extract Inlined Constant create => "Dominator_graph.create".
(* dominator_graph.mli:38  val dominator_analysis : t -> alias_map *)
Parameter dominator_analysis : t -> M alias_map.
Extract Inlined Constant dominator_analysis => "Dominator_graph.dominator_analysis".
(* dominator_graph.mli:40  val aliases_kind : t -> alias_map -> Flambda_kind.t Variable.Map.t *)
Parameter aliases_kind : t -> alias_map -> M (Variable_.Map.t Flambda_kind.t).
Extract Inlined Constant aliases_kind => "Dominator_graph.aliases_kind".
Module Dot.
  (* dominator_graph.mli:44  val print : ctx:int -> print_name:string -> doms:alias_map -> Format.formatter -> t -> unit *)
  Parameter print : int -> string -> Dominator_graph.alias_map -> Format.formatter -> Dominator_graph.t -> M unit.
  Extract Inlined Constant print => "Dominator_graph.Dot.print".
End Dot.
