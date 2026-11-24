(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018--2020 OCamlPro SAS                                    *)
(*   Copyright 2018--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Bound_parameter], after its interface
   middle_end/flambda2/bound_identifiers/bound_parameter.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_debug_uid Flambda_kind Format Int_ids Name Variable_.

(* bound_parameter.mli:18  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Bound_parameter.t".
(* bound_parameter.mli:21  val create : Variable.t -> Flambda_kind.With_subkind.t -> Flambda_debug_uid.t -> t *)
Parameter create : Variable_.t -> Flambda_kind.With_subkind.t -> Flambda_debug_uid.t -> M t.
Extract Inlined Constant create => "Bound_parameter.create".
(* bound_parameter.mli:25  val var : t -> Variable.t *)
Parameter var : t -> M Variable_.t.
Extract Inlined Constant var => "Bound_parameter.var".
(* bound_parameter.mli:27  val var_and_uid : t -> Variable.t * Flambda_debug_uid.t *)
Parameter var_and_uid : t -> M (Variable_.t * Flambda_debug_uid.t).
Extract Inlined Constant var_and_uid => "Bound_parameter.var_and_uid".
(* bound_parameter.mli:29  val name : t -> Name.t *)
Parameter name : t -> M Name.t.
Extract Inlined Constant name => "Bound_parameter.name".
(* bound_parameter.mli:32  val simple : t -> Int_ids.Simple.t *)
Parameter simple : t -> M Int_ids.Simple.t.
Extract Inlined Constant simple => "Bound_parameter.simple".
(* bound_parameter.mli:35  val kind : t -> Flambda_kind.With_subkind.t *)
Parameter kind : t -> M Flambda_kind.With_subkind.t.
Extract Inlined Constant kind => "Bound_parameter.kind".
Module T.
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Definition t : Type := Bound_parameter.t.
  Extract Inlined Constant t => "Bound_parameter.T.t".
End T.
(* bound_parameter.mli:46  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Bound_parameter.T.t -> M unit.
Extract Inlined Constant print => "Bound_parameter.print".
Module Set_.
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Definition elt : Type := Bound_parameter.t.
  Extract Inlined Constant elt => "Bound_parameter.Set.elt".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Bound_parameter.Set.t".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Bound_parameter.Set.mem".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Bound_parameter.Set.union".
End Set_.
Module Map.
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Definition key : Type := Bound_parameter.t.
  Extract Inlined Constant key => "Bound_parameter.Map.key".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Bound_parameter.Map.t".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Bound_parameter.Map.empty".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Bound_parameter.Map.add".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Bound_parameter.Map.fold".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
  Extract Inlined Constant bindings => "Bound_parameter.Map.bindings".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  Extract Inlined Constant find_opt => "Bound_parameter.Map.find_opt".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
  Extract Inlined Constant of_list => "Bound_parameter.Map.of_list".
  (* bound_parameter.mli:46  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Bound_parameter.Map.print".
End Map.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Bound_parameter. End Bound_parameter.
