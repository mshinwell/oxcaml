(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2019--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Bound_pattern], after its interface
   middle_end/flambda2/bound_identifiers/bound_pattern.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_static Bound_var Format Name_mode.

(* bound_pattern.mli:18  type t = private | Singleton of Bound_var.t ( ** The binding of a single variable, which is statically scoped. This case is not used for sets of closures. * ) | Set_of_closures of Bound_var.t list ( ** The binding of one or more variables to the individual closures in a set of closures. The variables are statically scoped. * ) | Static of Bound_static.t *)
Inductive t : Type :=
| Singleton : Bound_var.t -> t
| Set_of_closures : list Bound_var.t -> t
| Static : Bound_static.t -> t.
(* bound_pattern.mli:30  val singleton : Bound_var.t -> t *)
Parameter singleton : Bound_var.t -> M t.
Extract Inlined Constant singleton => "Bound_pattern.singleton".
(* bound_pattern.mli:32  val set_of_closures : Bound_var.t list -> t *)
Parameter set_of_closures : list Bound_var.t -> M t.
Extract Inlined Constant set_of_closures => "Bound_pattern.set_of_closures".
(* bound_pattern.mli:34  val static : Bound_static.t -> t *)
Parameter static : Bound_static.t -> M t.
Extract Inlined Constant static => "Bound_pattern.static".
(* bound_pattern.mli:36  val must_be_singleton : t -> Bound_var.t *)
Parameter must_be_singleton : t -> M Bound_var.t.
Extract Inlined Constant must_be_singleton => "Bound_pattern.must_be_singleton".
(* bound_pattern.mli:38  val must_be_singleton_opt : t -> Bound_var.t option *)
Parameter must_be_singleton_opt : t -> M (option Bound_var.t).
Extract Inlined Constant must_be_singleton_opt => "Bound_pattern.must_be_singleton_opt".
(* bound_pattern.mli:40  val must_be_set_of_closures : t -> Bound_var.t list *)
Parameter must_be_set_of_closures : t -> M (list Bound_var.t).
Extract Inlined Constant must_be_set_of_closures => "Bound_pattern.must_be_set_of_closures".
(* bound_pattern.mli:42  val must_be_static : t -> Bound_static.t *)
Parameter must_be_static : t -> M Bound_static.t.
Extract Inlined Constant must_be_static => "Bound_pattern.must_be_static".
(* bound_pattern.mli:44  val name_mode : t -> Name_mode.t *)
Parameter name_mode : t -> M Name_mode.t.
Extract Inlined Constant name_mode => "Bound_pattern.name_mode".
(* bound_pattern.mli:46  val with_name_mode : t -> Name_mode.t -> t *)
Parameter with_name_mode : t -> Name_mode.t -> M t.
Extract Inlined Constant with_name_mode => "Bound_pattern.with_name_mode".
(* bound_pattern.mli:48  val exists_all_bound_vars : t -> f:(Bound_var.t -> bool) -> bool *)
Parameter exists_all_bound_vars : t -> (Bound_var.t -> M bool) -> M bool.
Extract Inlined Constant exists_all_bound_vars => "Bound_pattern.exists_all_bound_vars".
(* bound_pattern.mli:50  val fold_all_bound_vars : t -> init:'a -> f:('a -> Bound_var.t -> 'a) -> 'a *)
Parameter fold_all_bound_vars : forall {A : Type}, t -> A -> (A -> Bound_var.t -> M A) -> M A.
Extract Inlined Constant fold_all_bound_vars => "Bound_pattern.fold_all_bound_vars".
(* bound_pattern.mli:60  include Bindable.S with type t := t *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Bound_pattern.print".
