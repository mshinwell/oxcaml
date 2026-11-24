(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2020--2020 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Inlining_report], after its interface
   middle_end/flambda2/simplify_shared/inlining_report.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_expr Are_rebuilding_terms Call_site_inlining_decision_type Code_metadata Function_decl_inlining_decision_type Inlined_debuginfo Inlining_history.

Module Pass.
  (* inlining_report.mli:18  type t = | After_closure_conversion | Before_simplify | After_simplify *)
  Inductive t : Type :=
  | After_closure_conversion : t
  | Before_simplify : t
  | After_simplify : t.
  Extract Inductive t => "Inlining_report.Pass.t" [ "Inlining_report.Pass.After_closure_conversion" "Inlining_report.Pass.Before_simplify" "Inlining_report.Pass.After_simplify" ].
End Pass.
(* inlining_report.mli:107  val record_decision_at_call_site_for_known_function : tracker:Inlining_history.Tracker.t -> unrolling_depth:int option -> apply:Apply_expr.t -> pass:Pass.t -> callee:Inlining_history.Absolute.t -> are_rebuilding_terms:Are_rebuilding_terms.t -> inlined_forwarded_from:Inlined_debuginfo.t option -> Call_site_inlining_decision_type.t -> unit *)
Parameter record_decision_at_call_site_for_known_function : Inlining_history.Tracker.t -> option int -> Apply_expr.t -> Inlining_report.Pass.t -> Inlining_history.Absolute.t -> Are_rebuilding_terms.t -> option Inlined_debuginfo.t -> Call_site_inlining_decision_type.t -> M unit.
Extract Inlined Constant record_decision_at_call_site_for_known_function => "Inlining_report.record_decision_at_call_site_for_known_function".
(* inlining_report.mli:118  val record_decision_at_call_site_for_unknown_function : tracker:Inlining_history.Tracker.t -> apply:Apply_expr.t -> pass:Pass.t -> unit -> unit *)
Parameter record_decision_at_call_site_for_unknown_function : Inlining_history.Tracker.t -> Apply_expr.t -> Inlining_report.Pass.t -> unit -> M unit.
Extract Inlined Constant record_decision_at_call_site_for_unknown_function => "Inlining_report.record_decision_at_call_site_for_unknown_function".
(* inlining_report.mli:125  val record_decision_at_function_definition : absolute_history:Inlining_history.Absolute.t -> code_metadata:Code_metadata.t -> pass:Pass.t -> are_rebuilding_terms:Are_rebuilding_terms.t -> Function_decl_inlining_decision_type.t -> unit *)
Parameter record_decision_at_function_definition : Inlining_history.Absolute.t -> Code_metadata.t -> Inlining_report.Pass.t -> Are_rebuilding_terms.t -> Function_decl_inlining_decision_type.t -> M unit.
Extract Inlined Constant record_decision_at_function_definition => "Inlining_report.record_decision_at_function_definition".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Inlining_report. End Inlining_report.
