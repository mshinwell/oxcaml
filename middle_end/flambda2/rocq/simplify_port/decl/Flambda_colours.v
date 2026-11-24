(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flambda_colours], after its interface
   middle_end/flambda2/ui/flambda_colours.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Misc.

(* flambda_colours.mli:19  type directive = Misc.Colours.directive *)
Definition directive : Type := Misc.Colours.directive.
Extract Inlined Constant directive => "Flambda_colours.directive".
(* flambda_colours.mli:23  val pop : directive *)
Parameter pop : directive.
Extract Inlined Constant pop => "Flambda_colours.pop".
(* flambda_colours.mli:89  val error : directive *)
Parameter error : directive.
Extract Inlined Constant error => "Flambda_colours.error".
(* flambda_colours.mli:91  val each_file : directive *)
Parameter each_file : directive.
Extract Inlined Constant each_file => "Flambda_colours.each_file".
(* flambda_colours.mli:99  val without_colours : f:(unit -> 'a) -> 'a *)
Parameter without_colours : forall {A : Type}, (unit -> M A) -> M A.
Extract Inlined Constant without_colours => "Flambda_colours.without_colours".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Flambda_colours. End Flambda_colours.
