(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2021 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Simplify_named_result], after its interface
   middle_end/flambda2/simplify/simplify_named_result.mli
   (Git blob 6428bc684a0715c56683e9b261028228bd23f33a). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_var Downwards_acc Flambda Simplified_named Symbol.

(* simplify_named_result.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Simplify_named_result.t".
(* simplify_named_result.mli:19  val create : Downwards_acc.t -> Simplified_named.binding_to_place -> t *)
Parameter create : Downwards_acc.t -> Simplified_named.binding_to_place -> M t.
Extract Inlined Constant create => "Simplify_named_result.create".
(* simplify_named_result.mli:21  val create_empty : Downwards_acc.t -> t *)
Parameter create_empty : Downwards_acc.t -> M t.
Extract Inlined Constant create_empty => "Simplify_named_result.create_empty".
(* simplify_named_result.mli:23  val create_have_lifted_set_of_closures : Downwards_acc.t -> (Bound_var.t * Symbol.t) list -> original_defining_expr:Named.t -> t *)
Parameter create_have_lifted_set_of_closures : Downwards_acc.t -> list (Bound_var.t * Symbol.t) -> Flambda.Import_.Named.t -> M t.
Extract Inlined Constant create_have_lifted_set_of_closures => "Simplify_named_result.create_have_lifted_set_of_closures".
(* simplify_named_result.mli:29  val dacc : t -> Downwards_acc.t *)
Parameter dacc : t -> M Downwards_acc.t.
Extract Inlined Constant dacc => "Simplify_named_result.dacc".
(* simplify_named_result.mli:31  val bindings_to_place : t -> Simplified_named.binding_to_place list *)
Parameter bindings_to_place : t -> M (list Simplified_named.binding_to_place).
Extract Inlined Constant bindings_to_place => "Simplify_named_result.bindings_to_place".
(* simplify_named_result.mli:33  val no_bindings : t -> bool *)
Parameter no_bindings : t -> M bool.
Extract Inlined Constant no_bindings => "Simplify_named_result.no_bindings".
(* simplify_named_result.mli:35  val was_lifted_set_of_closures : t -> bool *)
Parameter was_lifted_set_of_closures : t -> M bool.
Extract Inlined Constant was_lifted_set_of_closures => "Simplify_named_result.was_lifted_set_of_closures".
(* simplify_named_result.mli:37  val with_dacc : dacc:Downwards_acc.t -> t -> t *)
Parameter with_dacc : Downwards_acc.t -> t -> M t.
Extract Inlined Constant with_dacc => "Simplify_named_result.with_dacc".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Simplify_named_result. End Simplify_named_result.
