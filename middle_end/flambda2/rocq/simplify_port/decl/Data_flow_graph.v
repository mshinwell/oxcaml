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
   Simplify uses of the compiler's module [Data_flow_graph], after its interface
   middle_end/flambda2/simplify/flow/data_flow_graph.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Continuation Flambda2_types Flow_types Format Name_occurrences Or_unknown.

(* data_flow_graph.mli:16  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Data_flow_graph.t".
(* data_flow_graph.mli:19  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Data_flow_graph.print".
(* data_flow_graph.mli:22  val create : return_continuation:Continuation.t -> exn_continuation:Continuation.t -> code_age_relation:Code_age_relation.t -> used_value_slots:Name_occurrences.t Or_unknown.t -> code_ids_to_never_delete:Code_id.Set.t -> Flow_types.Continuation_info.t Continuation.Map.t -> t *)
Parameter create : Continuation.t -> Continuation.t -> Flambda2_types.Code_age_relation.t -> Or_unknown.t Name_occurrences.t -> Code_id.Set_.t -> Continuation.Map.t Flow_types.Continuation_info.t -> M t.
Extract Inlined Constant create => "Data_flow_graph.create".
(* data_flow_graph.mli:32  val required_names : t -> Flow_types.Data_flow_result.t *)
Parameter required_names : t -> M Flow_types.Data_flow_result.t.
Extract Inlined Constant required_names => "Data_flow_graph.required_names".
