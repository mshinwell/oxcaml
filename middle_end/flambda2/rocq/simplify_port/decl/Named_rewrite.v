(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Nathanaëlle Courant, Guillaume Bury and Pierre Chambart, OCamlPro    *)
(*                                                                        *)
(*   Copyright 2022--2022 OCamlPro SAS                                    *)
(*   Copyright 2022--2022 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Named_rewrite], after its interface
   middle_end/flambda2/simplify/named_rewrite.mli
   (Git blob f5b4d74784791af259292d955b0ef55cdc294b7e). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_kind Format Simple Variable_.

Module Prim_rewrite.
  (* named_rewrite.mli:18  type t = private | Remove_prim | Invalid of Flambda_kind.t | Replace_by_binding of { var : Variable.t; bound_to : Simple.t } *)
  Inductive t : Type :=
  | Remove_prim : t
  | Invalid : Flambda_kind.t -> t
  | Replace_by_binding : Variable_.t -> Simple.t -> t.
  Extract Inductive t => "Named_rewrite.Prim_rewrite.t" [ "Named_rewrite.Prim_rewrite.Remove_prim" "Named_rewrite.Prim_rewrite.Invalid" "(fun (x__1, x__2) -> (Named_rewrite.Prim_rewrite.Replace_by_binding { var = x__1; bound_to = x__2 } : Named_rewrite.Prim_rewrite.t))" ] "(fun f__1 f__2 f__3 x__0 -> match (x__0 : Named_rewrite.Prim_rewrite.t) with Named_rewrite.Prim_rewrite.Remove_prim -> f__1 () | Named_rewrite.Prim_rewrite.Invalid x__1 -> f__2 x__1 | Named_rewrite.Prim_rewrite.Replace_by_binding { var = x__1; bound_to = x__2 } -> f__3 x__1 x__2)".
  (* named_rewrite.mli:27  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Named_rewrite.Prim_rewrite.print".
  (* named_rewrite.mli:30  val invalid : Flambda_kind.t -> t *)
  Parameter invalid : Flambda_kind.t -> M t.
  Extract Inlined Constant invalid => "Named_rewrite.Prim_rewrite.invalid".
  (* named_rewrite.mli:33  val remove_prim : t *)
  Parameter remove_prim : t.
  Extract Inlined Constant remove_prim => "Named_rewrite.Prim_rewrite.remove_prim".
  (* named_rewrite.mli:36  val replace_by_binding : var:Variable.t -> bound_to:Simple.t -> t *)
  Parameter replace_by_binding : Variable_.t -> Simple.t -> M t.
  Extract Inlined Constant replace_by_binding => "Named_rewrite.Prim_rewrite.replace_by_binding".
End Prim_rewrite.
(* named_rewrite.mli:40  type t = private Prim_rewrite of Prim_rewrite.t *)
Inductive t : Type :=
| Prim_rewrite : Named_rewrite.Prim_rewrite.t -> t.
Extract Inductive t => "Named_rewrite.t" [ "Named_rewrite.Prim_rewrite" ].
(* named_rewrite.mli:42  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Named_rewrite.print".
(* named_rewrite.mli:44  val prim_rewrite : Prim_rewrite.t -> t *)
Parameter prim_rewrite : Named_rewrite.Prim_rewrite.t -> M t.
Extract Inlined Constant prim_rewrite => "Named_rewrite.prim_rewrite".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Named_rewrite. End Named_rewrite.
