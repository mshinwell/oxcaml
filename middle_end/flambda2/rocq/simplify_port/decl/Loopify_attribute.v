(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                     Nathanaëlle Courant, OCamlPro                      *)
(*                                                                        *)
(*   Copyright 2022 OCamlPro SAS                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Loopify_attribute], after its interface
   middle_end/flambda2/terms/loopify_attribute.mli
   (Git blob 458ffcf87ecbf0e7162b7541bdfb9d0a7fc3dc13). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* loopify_attribute.mli:15  type t = | Always_loopify | Never_loopify | Already_loopified | Default_loopify_and_tailrec | Default_loopify_and_not_tailrec *)
Inductive t : Type :=
| Always_loopify : t
| Never_loopify : t
| Already_loopified : t
| Default_loopify_and_tailrec : t
| Default_loopify_and_not_tailrec : t.
Extract Inductive t => "Loopify_attribute.t" [ "Loopify_attribute.Always_loopify" "Loopify_attribute.Never_loopify" "Loopify_attribute.Already_loopified" "Loopify_attribute.Default_loopify_and_tailrec" "Loopify_attribute.Default_loopify_and_not_tailrec" ].
(* loopify_attribute.mli:24  val should_loopify : t -> bool *)
Parameter should_loopify : t -> M bool.
Extract Inlined Constant should_loopify => "Loopify_attribute.should_loopify".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Loopify_attribute. End Loopify_attribute.
