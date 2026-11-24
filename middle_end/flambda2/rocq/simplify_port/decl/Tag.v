(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2018 OCamlPro SAS                                    *)
(*   Copyright 2014--2018 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Tag], after its interface
   middle_end/flambda2/kinds/tag.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Target_ocaml_int Target_system Targetint_32_64.

(* container_types_intf.ml:297  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Tag.t".
Module T.
  (* container_types_intf.ml:299  module T : Thing with type t = t *)
  Definition t : Type := Tag.t.
  Extract Inlined Constant t => "Tag.T.t".
End T.
(* container_types_intf.ml:301  include Thing with type t := T.t *)
Parameter print : Format.formatter -> Tag.T.t -> M unit.
Extract Inlined Constant print => "Tag.print".
(* tag.mli:21  type tag = t *)
Definition tag : Type := t.
Extract Inlined Constant tag => "Tag.tag".
(* tag.mli:28  val to_int : t -> int *)
Parameter to_int : t -> M int.
Extract Inlined Constant to_int => "Tag.to_int".
(* tag.mli:30  val to_targetint_31_63 : Target_system.Machine_width.t -> t -> Target_ocaml_int.t *)
Parameter to_targetint_31_63 : Target_system.Machine_width.t -> t -> M Target_ocaml_int.t.
Extract Inlined Constant to_targetint_31_63 => "Tag.to_targetint_31_63".
(* tag.mli:43  val double_array_tag : t *)
Parameter double_array_tag : t.
Extract Inlined Constant double_array_tag => "Tag.double_array_tag".
Module Scannable.
  (* tag.mli:64  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Tag.Scannable.t".
  (* tag.mli:72  val of_tag : tag -> t option *)
  Parameter of_tag : Tag.tag -> M (option t).
  Extract Inlined Constant of_tag => "Tag.Scannable.of_tag".
  (* tag.mli:76  val to_targetint : Target_system.Machine_width.t -> t -> Targetint_32_64.t *)
  Parameter to_targetint : Target_system.Machine_width.t -> t -> M Targetint_32_64.t.
  Extract Inlined Constant to_targetint => "Tag.Scannable.to_targetint".
  (* tag.mli:78  val to_tag : t -> tag *)
  Parameter to_tag : t -> M Tag.tag.
  Extract Inlined Constant to_tag => "Tag.Scannable.to_tag".
  (* tag.mli:80  val zero : t *)
  Parameter zero : t.
  Extract Inlined Constant zero => "Tag.Scannable.zero".
  Module T.
    (* tag.mli:84  include Container_types.S with type t := t *)
    Definition t : Type := Tag.Scannable.t.
    Extract Inlined Constant t => "Tag.Scannable.T.t".
  End T.
  (* tag.mli:84  include Container_types.S with type t := t *)
  Parameter equal : Tag.Scannable.T.t -> Tag.Scannable.T.t -> M bool.
  Extract Inlined Constant equal => "Tag.Scannable.equal".
  Module Map.
    (* tag.mli:84  include Container_types.S with type t := t *)
    Definition key : Type := Tag.Scannable.t.
    Extract Inlined Constant key => "Tag.Scannable.Map.key".
    (* tag.mli:84  include Container_types.S with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Tag.Scannable.Map.t".
    (* tag.mli:84  include Container_types.S with type t := t *)
    Parameter empty : forall {A : Type}, t A.
    Extract Inlined Constant empty => "Tag.Scannable.Map.empty".
    (* tag.mli:84  include Container_types.S with type t := t *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    Extract Inlined Constant is_empty => "Tag.Scannable.Map.is_empty".
    (* tag.mli:84  include Container_types.S with type t := t *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold => "Tag.Scannable.Map.fold".
    (* tag.mli:84  include Container_types.S with type t := t *)
    Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
    Extract Inlined Constant filter_map => "Tag.Scannable.Map.filter_map".
    (* tag.mli:84  include Container_types.S with type t := t *)
    Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
    Extract Inlined Constant map => "Tag.Scannable.Map.map".
    (* tag.mli:84  include Container_types.S with type t := t *)
    Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
    Extract Inlined Constant mapi => "Tag.Scannable.Map.mapi".
    (* tag.mli:84  include Container_types.S with type t := t *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print => "Tag.Scannable.Map.print".
    (* tag.mli:84  include Container_types.S with type t := t *)
    Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant get_singleton => "Tag.Scannable.Map.get_singleton".
  End Map.
End Scannable.
