(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2020 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Code_id_or_symbol], after its interface
   middle_end/flambda2/identifiers/code_id_or_symbol.mli
   (Git blob 558bd17d8009d6b347150e40c4b7010b4569fe97). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Int_ids.

(* int_ids.mli:281  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Code_id_or_symbol.t.
Extract Inlined Constant t => "Code_id_or_symbol.t".
(* module Set = Int_ids.Code_id_or_symbol.Set: declared again here under this name. *)
Module Set_.
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Definition elt : Type := Int_ids.Code_id_or_symbol.Set_.elt.
  Extract Inlined Constant elt => "Code_id_or_symbol.Set.elt".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Definition t : Type := Int_ids.Code_id_or_symbol.Set_.t.
  Extract Inlined Constant t => "Code_id_or_symbol.Set.t".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Code_id_or_symbol.Set.empty".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Code_id_or_symbol.Set.mem".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Code_id_or_symbol.Set.add".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Code_id_or_symbol.Set.union".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Code_id_or_symbol.Set.fold".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Parameter filter : (elt -> M bool) -> t -> M t.
  Extract Inlined Constant filter => "Code_id_or_symbol.Set.filter".
End Set_.
(* module Map = Int_ids.Code_id_or_symbol.Map: declared again here under this name. *)
Module Map.
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Definition key : Type := Int_ids.Code_id_or_symbol.Map.key.
  Extract Inlined Constant key => "Code_id_or_symbol.Map.key".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Definition t (A : Type) : Type := Int_ids.Code_id_or_symbol.Map.t A.
  Extract Constant t "'a1" => "('a1) Code_id_or_symbol.Map.t".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Code_id_or_symbol.Map.empty".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Code_id_or_symbol.Map.add".
  (* int_ids.mli:283  include Container_types.S with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Code_id_or_symbol.Map.find".
End Map.
(* module Lmap = Int_ids.Code_id_or_symbol.Lmap: declared again here under this name. *)
Module Lmap.
  (* int_ids.mli:285  module Lmap : Lmap.S with type key = t *)
  Definition key : Type := Int_ids.Code_id_or_symbol.Lmap.key.
  Extract Inlined Constant key => "Code_id_or_symbol.Lmap.key".
  (* lmap.mli:48  type +'a t *)
  Definition t (A : Type) : Type := Int_ids.Code_id_or_symbol.Lmap.t A.
  Extract Constant t "'a1" => "('a1) Code_id_or_symbol.Lmap.t".
  (* lmap.mli:50  val empty : 'a t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Code_id_or_symbol.Lmap.empty".
  (* lmap.mli:55  val add : key -> 'a -> 'a t -> 'a t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Code_id_or_symbol.Lmap.add".
  (* lmap.mli:67  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Code_id_or_symbol.Lmap.fold".
  (* lmap.mli:81  val bindings : 'a t -> (key * 'a) list *)
  Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
  Extract Inlined Constant bindings => "Code_id_or_symbol.Lmap.bindings".
  (* lmap.mli:96  val map : ('a -> 'b) -> 'a t -> 'b t *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Code_id_or_symbol.Lmap.map".
End Lmap.
(* int_ids.mli:293  val set_of_code_id_set : Code_id.Set.t -> Set.t *)
Parameter set_of_code_id_set : Int_ids.Code_id.Set_.t -> M Code_id_or_symbol.Set_.t.
Extract Inlined Constant set_of_code_id_set => "Code_id_or_symbol.set_of_code_id_set".
(* int_ids.mli:295  val set_of_symbol_set : Symbol.Set.t -> Set.t *)
Parameter set_of_symbol_set : Int_ids.Symbol.Set_.t -> M Code_id_or_symbol.Set_.t.
Extract Inlined Constant set_of_symbol_set => "Code_id_or_symbol.set_of_symbol_set".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Code_id_or_symbol. End Code_id_or_symbol.
