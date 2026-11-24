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
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Absolute.
  (* inlining_history.mli:52  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Inlining_history.Absolute.t".
End Absolute.
Module Relative.
  (* inlining_history.mli:97  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Inlining_history.Relative.t".
End Relative.
Module Tracker.
  (* inlining_history.mli:117  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Inlining_history.Tracker.t".
End Tracker.
