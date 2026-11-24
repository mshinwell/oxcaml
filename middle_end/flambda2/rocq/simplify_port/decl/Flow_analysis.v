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
   Simplify uses of the compiler's module [Flow_analysis], after its interface
   middle_end/flambda2/simplify/flow/flow_analysis.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Continuation Continuation_callsite_map Flambda2_types Flow_types Name_occurrences Or_unknown Target_system.

(* flow_analysis.mli:26  val analyze : ?speculative:bool -> ?print_name:string -> machine_width:Target_system.Machine_width.t -> return_continuation:Continuation.t -> exn_continuation:Continuation.t -> code_age_relation:Code_age_relation.t -> used_value_slots:Name_occurrences.t Or_unknown.t -> code_ids_to_never_delete:Code_id.Set.t -> specialization_map:Continuation.t Continuation_callsite_map.t -> Flow_types.Acc.t -> ... *)
Parameter analyze : option bool -> option string -> Target_system.Machine_width.t -> Continuation.t -> Continuation.t -> Flambda2_types.Code_age_relation.t -> Or_unknown.t Name_occurrences.t -> Code_id.Set_.t -> Continuation_callsite_map.t Continuation.t -> Flow_types.Acc.t -> M Flow_types.Flow_result.t.
Extract Inlined Constant analyze => "(fun x__1 x__2 x__3 x__4 x__5 x__6 x__7 x__8 x__9 x__10 -> Flow_analysis.analyze ?speculative:x__1 ?print_name:x__2 x__3 x__4 x__5 x__6 x__7 x__8 x__9 x__10)".
(* flow_analysis.mli:40  val did_perform_mutable_unboxing : Flow_types.Flow_result.t -> bool *)
Parameter did_perform_mutable_unboxing : Flow_types.Flow_result.t -> M bool.
Extract Inlined Constant did_perform_mutable_unboxing => "Flow_analysis.did_perform_mutable_unboxing".
(* flow_analysis.mli:57  val added_useful_alias_in_loop : Typing_env.t -> Flow_types.Acc.t -> Flow_types.Flow_result.t -> bool *)
Parameter added_useful_alias_in_loop : Flambda2_types.Typing_env.t -> Flow_types.Acc.t -> Flow_types.Flow_result.t -> M bool.
Extract Inlined Constant added_useful_alias_in_loop => "Flow_analysis.added_useful_alias_in_loop".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Flow_analysis. End Flow_analysis.
