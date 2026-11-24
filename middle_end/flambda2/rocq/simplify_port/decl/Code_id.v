(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Code_id], after its interface
   middle_end/flambda2/identifiers/code_id.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Compilation_unit Debuginfo Format Int_ids Or_null.

(* int_ids.mli:247  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Code_id.t.
Extract Inlined Constant t => "Code_id.t".
(* module T = Int_ids.Code_id.T: declared again here under this name. *)
Module T.
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Definition t : Type := Int_ids.Code_id.T.t.
  Extract Inlined Constant t => "Code_id.T.t".
End T.
(* int_ids.mli:251  include Container_types.S with type t := t *)
Parameter equal : Code_id.T.t -> Code_id.T.t -> M bool.
Extract Inlined Constant equal => "Code_id.equal".
(* int_ids.mli:251  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Code_id.T.t -> M unit.
Extract Inlined Constant print => "Code_id.print".
(* module Set = Int_ids.Code_id.Set: declared again here under this name. *)
Module Set_.
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Definition elt : Type := Int_ids.Code_id.Set_.elt.
  Extract Inlined Constant elt => "Code_id.Set.elt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Definition t : Type := Int_ids.Code_id.Set_.t.
  Extract Inlined Constant t => "Code_id.Set.t".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Code_id.Set.empty".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter is_empty : t -> M bool.
  Extract Inlined Constant is_empty => "Code_id.Set.is_empty".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Code_id.Set.mem".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Code_id.Set.add".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter singleton : elt -> M t.
  Extract Inlined Constant singleton => "Code_id.Set.singleton".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Code_id.Set.union".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter disjoint : t -> t -> M bool.
  Extract Inlined Constant disjoint => "Code_id.Set.disjoint".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter diff : t -> t -> M t.
  Extract Inlined Constant diff => "Code_id.Set.diff".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter iter : (elt -> M unit) -> t -> M unit.
  Extract Inlined Constant iter => "Code_id.Set.iter".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter for_all : (elt -> M bool) -> t -> M bool.
  Extract Inlined Constant for_all => "Code_id.Set.for_all".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Code_id.Set.print".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter get_singleton : t -> M (option elt).
  Extract Inlined Constant get_singleton => "Code_id.Set.get_singleton".
End Set_.
(* module Map = Int_ids.Code_id.Map: declared again here under this name. *)
Module Map.
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Definition key : Type := Int_ids.Code_id.Map.key.
  Extract Inlined Constant key => "Code_id.Map.key".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Definition t (A : Type) : Type := Int_ids.Code_id.Map.t A.
  Extract Constant t "'a1" => "('a1) Code_id.Map.t".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Code_id.Map.empty".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter mem : forall {A : Type}, key -> t A -> M bool.
  Extract Inlined Constant mem => "Code_id.Map.mem".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Code_id.Map.add".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Code_id.Map.update".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Code_id.Map.fold".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Code_id.Map.find".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  Extract Inlined Constant find_or_null => "Code_id.Map.find_or_null".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
  Extract Inlined Constant of_list => "Code_id.Map.of_list".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Code_id.Map.print".
End Map.
(* int_ids.mli:257  val create : name:string -> debug:Debuginfo.t -> Compilation_unit.t -> t *)
Parameter create : string -> Debuginfo.t -> Compilation_unit.t -> M t.
Extract Inlined Constant create => "Code_id.create".
(* int_ids.mli:259  val get_compilation_unit : t -> Compilation_unit.t *)
Parameter get_compilation_unit : t -> M Compilation_unit.t.
Extract Inlined Constant get_compilation_unit => "Code_id.get_compilation_unit".
(* int_ids.mli:261  val in_compilation_unit : t -> Compilation_unit.t -> bool *)
Parameter in_compilation_unit : t -> Compilation_unit.t -> M bool.
Extract Inlined Constant in_compilation_unit => "Code_id.in_compilation_unit".
(* int_ids.mli:263  val is_imported : t -> bool *)
Parameter is_imported : t -> M bool.
Extract Inlined Constant is_imported => "Code_id.is_imported".
(* int_ids.mli:267  val name : t -> string *)
Parameter name : t -> M string.
Extract Inlined Constant name => "Code_id.name".
(* int_ids.mli:271  val rename : t -> t *)
Parameter rename : t -> M t.
Extract Inlined Constant rename => "Code_id.rename".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Code_id. End Code_id.
