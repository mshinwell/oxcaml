(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Lifted_constant_state], after its interface
   middle_end/flambda2/simplify/lifting/lifted_constant_state.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Lifted_constant Symbol.

(* module LC = Lifted_constant *)
Module LC := Lifted_constant.
(* lifted_constant_state.mli:19  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Lifted_constant_state.t".
(* lifted_constant_state.mli:21  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Lifted_constant_state.empty".
(* lifted_constant_state.mli:23  val is_empty : t -> bool *)
Parameter is_empty : t -> M bool.
Extract Inlined Constant is_empty => "Lifted_constant_state.is_empty".
(* lifted_constant_state.mli:25  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Lifted_constant_state.print".
(* lifted_constant_state.mli:27  val singleton : LC.t -> t *)
Parameter singleton : Lifted_constant.t -> M t.
Extract Inlined Constant singleton => "Lifted_constant_state.singleton".
(* lifted_constant_state.mli:29  val add : t -> LC.t -> t *)
Parameter add : t -> Lifted_constant.t -> M t.
Extract Inlined Constant add => "Lifted_constant_state.add".
(* lifted_constant_state.mli:31  val singleton_list_of_constants : LC.t list -> t *)
Parameter singleton_list_of_constants : list Lifted_constant.t -> M t.
Extract Inlined Constant singleton_list_of_constants => "Lifted_constant_state.singleton_list_of_constants".
(* lifted_constant_state.mli:33  val union : t -> t -> t *)
Parameter union : t -> t -> M t.
Extract Inlined Constant union => "Lifted_constant_state.union".
(* lifted_constant_state.mli:35  val fold : t -> init:'a -> f:('a -> LC.t -> 'a) -> 'a *)
Parameter fold : forall {A : Type}, t -> A -> (A -> Lifted_constant.t -> M A) -> M A.
Extract Inlined Constant fold => "Lifted_constant_state.fold".
(* lifted_constant_state.mli:37  val all_defined_symbols : t -> Symbol.Set.t *)
Parameter all_defined_symbols : t -> M Symbol.Set_.t.
Extract Inlined Constant all_defined_symbols => "Lifted_constant_state.all_defined_symbols".
(* lifted_constant_state.mli:39  type sort_result = private { innermost_first : LC.t array } *)
Record sort_result : Type := { innermost_first : array Lifted_constant.t }.
(* lifted_constant_state.mli:41  val sort : t -> sort_result *)
Parameter sort : t -> M sort_result.
Extract Inlined Constant sort => "Lifted_constant_state.sort".
