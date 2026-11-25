(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Copyright 2021--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Inlining_history], after its interface
   middle_end/flambda2/terms/inlining_history.mli
   (Git blob 18608a9d5212b220657f20f9e9c462d03a17e424). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Compilation_unit Debuginfo.

Module Absolute.
  (* inlining_history.mli:52  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Inlining_history.Absolute.t".
End Absolute.
Module Relative.
  (* inlining_history.mli:97  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Inlining_history.Relative.t".
  (* inlining_history.mli:99  val empty : t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Inlining_history.Relative.empty".
  (* inlining_history.mli:103  val concat : earlier:t -> later:t -> t *)
  Parameter concat : t -> t -> M t.
  Extract Inlined Constant concat => "Inlining_history.Relative.concat".
End Relative.
Module Tracker.
  (* inlining_history.mli:117  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Inlining_history.Tracker.t".
  (* inlining_history.mli:119  val empty : Compilation_unit.t -> t *)
  Parameter empty : Compilation_unit.t -> M t.
  Extract Inlined Constant empty => "Inlining_history.Tracker.empty".
  (* inlining_history.mli:123  val relative : t -> Relative.t *)
  Parameter relative : t -> M Inlining_history.Relative.t.
  Extract Inlined Constant relative => "Inlining_history.Tracker.relative".
  (* inlining_history.mli:132  val fundecl : dbg:Debuginfo.t -> function_relative_history:Relative.t -> name:string -> t -> Absolute.t * Relative.t *)
  Parameter fundecl : Debuginfo.t -> Inlining_history.Relative.t -> string -> t -> M (Inlining_history.Absolute.t * Inlining_history.Relative.t).
  Extract Inlined Constant fundecl => "Inlining_history.Tracker.fundecl".
  (* inlining_history.mli:141  val enter_inlined_apply : dbg:Debuginfo.t -> callee:Absolute.t -> apply_relative_history:Relative.t -> t -> t *)
  Parameter enter_inlined_apply : Debuginfo.t -> Inlining_history.Absolute.t -> Inlining_history.Relative.t -> t -> M t.
  Extract Inlined Constant enter_inlined_apply => "Inlining_history.Tracker.enter_inlined_apply".
  (* inlining_history.mli:150  val inside_function : Absolute.t -> t *)
  Parameter inside_function : Inlining_history.Absolute.t -> M t.
  Extract Inlined Constant inside_function => "Inlining_history.Tracker.inside_function".
End Tracker.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Inlining_history. End Inlining_history.
