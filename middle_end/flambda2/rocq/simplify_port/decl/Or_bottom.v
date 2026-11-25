(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018 OCamlPro SAS                                          *)
(*   Copyright 2018 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Or_bottom], after its interface
   middle_end/flambda2/lattices/or_bottom.mli
   (Git blob 310935bc5b8cd78ae6055708d03fdaf6ad9e68c1). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* or_bottom.mli:17  type 'a t = | Ok of 'a | Bottom *)
Inductive t (A : Type) : Type :=
| Ok : A -> t A
| Bottom : t A.
Arguments Ok {A}.
Arguments Bottom {A}.
Extract Inductive t => "Or_bottom.t" [ "Or_bottom.Ok" "Or_bottom.Bottom" ].
Module Let_syntax.
  (* or_bottom.mli:34  val ( let<* ) : 'a t -> ('a -> 'b t) -> 'b t *)
  Parameter let_op_lt_star : forall {A B : Type}, Or_bottom.t A -> (A -> M (Or_bottom.t B)) -> M (Or_bottom.t B).
  Extract Inlined Constant let_op_lt_star => "Or_bottom.Let_syntax.( let<* )".
  (* or_bottom.mli:36  val ( let<+ ) : 'a t -> ('a -> 'b) -> 'b t *)
  Parameter let_op_lt_plus : forall {A B : Type}, Or_bottom.t A -> (A -> M B) -> M (Or_bottom.t B).
  Extract Inlined Constant let_op_lt_plus => "Or_bottom.Let_syntax.( let<+ )".
End Let_syntax.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Or_bottom. End Or_bottom.
