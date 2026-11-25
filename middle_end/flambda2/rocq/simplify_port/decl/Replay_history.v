(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Guillaume Bury, Pierre Chambart and Nathanaëlle Courant, OCamlPro    *)
(*                                                                        *)
(*   Copyright 2013--2024 OCamlPro SAS                                    *)
(*   Copyright 2014--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Replay_history], after its interface
   middle_end/flambda2/simplify/env/replay_history.mli
   (Git blob d9c5f5f15495addeaff2557fb82ef6e0c861f482). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_expr Call_site_inlining_decision_type Continuation Format Variable_.

(* replay_history.mli:53  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Replay_history.t".
(* replay_history.mli:55  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Replay_history.print".
(* replay_history.mli:60  val first_pass : t *)
Parameter first_pass : t.
Extract Inlined Constant first_pass => "Replay_history.first_pass".
(* replay_history.mli:65  val replay : always_inline:bool -> t -> t *)
Parameter replay : bool -> t -> M t.
Extract Inlined Constant replay => "Replay_history.replay".
(* replay_history.mli:68  val define_variable : Variable.t -> t -> t *)
Parameter define_variable : Variable_.t -> t -> M t.
Extract Inlined Constant define_variable => "Replay_history.define_variable".
(* replay_history.mli:71  val define_continuations : can_be_lifted:bool -> Continuation.t list -> t -> t *)
Parameter define_continuations : bool -> list Continuation.t -> t -> M t.
Extract Inlined Constant define_continuations => "Replay_history.define_continuations".
(* replay_history.mli:73  val record_inlining_decision : apply:Apply_expr.t -> Call_site_inlining_decision_type.t -> t -> t *)
Parameter record_inlining_decision : Apply_expr.t -> Call_site_inlining_decision_type.t -> t -> M t.
Extract Inlined Constant record_inlining_decision => "Replay_history.record_inlining_decision".
(* replay_history.mli:80  val must_inline : t -> bool *)
Parameter must_inline : t -> M bool.
Extract Inlined Constant must_inline => "Replay_history.must_inline".
(* replay_history.mli:84  type 'a replay_result = | Still_recording | Replayed of 'a *)
Inductive replay_result (A : Type) : Type :=
| Still_recording : replay_result A
| Replayed : A -> replay_result A.
Arguments Still_recording {A}.
Arguments Replayed {A}.
Extract Inductive replay_result => "Replay_history.replay_result" [ "Replay_history.Still_recording" "Replay_history.Replayed" ].
(* replay_history.mli:90  val replay_variable_mapping : t -> Variable.t Variable.Map.t replay_result *)
Parameter replay_variable_mapping : t -> M (replay_result (Variable_.Map.t Variable_.t)).
Extract Inlined Constant replay_variable_mapping => "Replay_history.replay_variable_mapping".
(* replay_history.mli:95  val replay_continuation_mapping : t -> Continuation.t Continuation.Map.t replay_result *)
Parameter replay_continuation_mapping : t -> M (replay_result (Continuation.Map.t Continuation.t)).
Extract Inlined Constant replay_continuation_mapping => "Replay_history.replay_continuation_mapping".
(* replay_history.mli:98  val replay_inlining_decision : t -> Call_site_inlining_decision_type.t replay_result *)
Parameter replay_inlining_decision : t -> M (replay_result Call_site_inlining_decision_type.t).
Extract Inlined Constant replay_inlining_decision => "Replay_history.replay_inlining_decision".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Replay_history. End Replay_history.
