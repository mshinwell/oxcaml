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
From SimplifyPort.decl Require Flambda_kind Format.

(* flambda_arity.mli:30  type _ t *)
Parameter t : Type.
Extract Inlined Constant t => "(_) Flambda_arity.t".
(* flambda_arity.mli:33  val print : Format.formatter -> _ t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Flambda_arity.print".
Module Component_for_creation.
  (* flambda_arity.mli:36  type _ t = | Singleton : Flambda_kind.With_subkind.t -> [> ] t ( * The nullary unboxed product is called 'void'. It is important to propagate information about void layouts, even though the corresponding variables have no runtime representation, as they interact with currying. (For example void parameters cannot just be erased.) * ) | Unboxed_product : _ t list -> [`Complex] t *)
  (* PORT-GAP(type): it is a GADT: abstract, with a maker for each constructor and one eliminator. *)
  Parameter t : Type.
  Extract Inlined Constant t => "(_) Flambda_arity.Component_for_creation.t".
  Parameter mk_Singleton : Flambda_kind.With_subkind.t -> t.
  Extract Inlined Constant mk_Singleton => "(fun x__1 -> Flambda_arity.Component_for_creation.Singleton x__1)".
  Parameter mk_Unboxed_product : list t -> t.
  Extract Inlined Constant mk_Unboxed_product => "(fun x__1 -> Flambda_arity.Component_for_creation.Unboxed_product x__1)".
End Component_for_creation.
(* flambda_arity.mli:51  val create : 'uc Component_for_creation.t list -> 'uc t *)
Parameter create : list Flambda_arity.Component_for_creation.t -> M t.
Extract Inlined Constant create => "Flambda_arity.create".
(* flambda_arity.mli:55  val create_singletons : Flambda_kind.With_subkind.t list -> [> ] t *)
Parameter create_singletons : list Flambda_kind.With_subkind.t -> M t.
Extract Inlined Constant create_singletons => "Flambda_arity.create_singletons".
(* flambda_arity.mli:58  val nullary : [> ] t *)
Parameter nullary : t.
Extract Inlined Constant nullary => "Flambda_arity.nullary".
(* flambda_arity.mli:62  val num_params : _ t -> int *)
Parameter num_params : t -> M int.
Extract Inlined Constant num_params => "Flambda_arity.num_params".
(* flambda_arity.mli:65  val equal_ignoring_subkinds : 'a t -> 'a t -> bool *)
Parameter equal_ignoring_subkinds : t -> t -> M bool.
Extract Inlined Constant equal_ignoring_subkinds => "Flambda_arity.equal_ignoring_subkinds".
(* flambda_arity.mli:75  val is_one_param_of_kind_value : _ t -> bool *)
Parameter is_one_param_of_kind_value : t -> M bool.
Extract Inlined Constant is_one_param_of_kind_value => "Flambda_arity.is_one_param_of_kind_value".
(* flambda_arity.mli:107  val unarize : _ t -> Flambda_kind.With_subkind.t list *)
Parameter unarize : t -> M (list Flambda_kind.With_subkind.t).
Extract Inlined Constant unarize => "Flambda_arity.unarize".
(* flambda_arity.mli:111  val unarized_components : [`Unarized] t -> Flambda_kind.With_subkind.t list *)
Parameter unarized_components : t -> M (list Flambda_kind.With_subkind.t).
Extract Inlined Constant unarized_components => "Flambda_arity.unarized_components".
(* flambda_arity.mli:114  val unarize_per_parameter : [`Complex] t -> Flambda_kind.With_subkind.t list list *)
Parameter unarize_per_parameter : t -> M (list (list Flambda_kind.With_subkind.t)).
Extract Inlined Constant unarize_per_parameter => "Flambda_arity.unarize_per_parameter".
(* flambda_arity.mli:118  val unarize_t : [`Complex] t -> [`Unarized] t *)
Parameter unarize_t : t -> M t.
Extract Inlined Constant unarize_t => "Flambda_arity.unarize_t".
(* flambda_arity.mli:131  val cardinal_unarized : _ t -> int *)
Parameter cardinal_unarized : t -> M int.
Extract Inlined Constant cardinal_unarized => "Flambda_arity.cardinal_unarized".
(* flambda_arity.mli:144  val partially_apply : [`Complex] t -> num_non_unarized_params_provided:int -> [`Complex] t *)
Parameter partially_apply : t -> int -> M t.
Extract Inlined Constant partially_apply => "Flambda_arity.partially_apply".
(* flambda_arity.mli:149  val concat : 'a t -> 'a t -> 'a t *)
Parameter concat : t -> t -> M t.
Extract Inlined Constant concat => "Flambda_arity.concat".
