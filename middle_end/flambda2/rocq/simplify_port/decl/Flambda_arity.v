(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2023 OCamlPro SAS                                    *)
(*   Copyright 2014--2023 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flambda_arity], after its interface
   middle_end/flambda2/kinds/flambda_arity.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_kind.

(* flambda_arity.mli:30  type _ t *)
Parameter t : Type.
Extract Inlined Constant t => "Flambda_arity.t".
Module Component_for_creation.
  (* flambda_arity.mli:36  type _ t = | Singleton : Flambda_kind.With_subkind.t -> [> ] t ( * The nullary unboxed product is called 'void'. It is important to propagate information about void layouts, even though the corresponding variables have no runtime representation, as they interact with currying. (For example void parameters cannot just be erased.) * ) | Unboxed_product : _ t list -> [`Complex] t *)
  (* PORT-GAP(type): abstract, though Simplify takes it apart: its definition has a polymorphic variant. *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Flambda_arity.Component_for_creation.t".
End Component_for_creation.
(* flambda_arity.mli:51  val create : 'uc Component_for_creation.t list -> 'uc t *)
Parameter create : forall {Uc : Type}, list (Flambda_arity.Component_for_creation.t Uc) -> M t.
Extract Inlined Constant create => "Flambda_arity.create".
(* flambda_arity.mli:55  val create_singletons : Flambda_kind.With_subkind.t list -> [> ] t *)
Parameter create_singletons : list Flambda_kind.With_subkind.t -> M t.
Extract Inlined Constant create_singletons => "Flambda_arity.create_singletons".
(* flambda_arity.mli:118  val unarize_t : [`Complex] t -> [`Unarized] t *)
Parameter unarize_t : t -> M t.
Extract Inlined Constant unarize_t => "Flambda_arity.unarize_t".
