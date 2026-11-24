(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Symbol], after its interface
   middle_end/flambda2/identifiers/symbol.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Compilation_unit Format Int_ids Linkage_name.

(* int_ids.mli:145  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Symbol.t.
Extract Inlined Constant t => "Symbol.t".
(* module T = Int_ids.Symbol.T: declared again here under this name. *)
Module T.
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Symbol.T.t.
  Extract Inlined Constant t => "Symbol.T.t".
End T.
(* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
Parameter equal : Symbol.T.t -> Symbol.T.t -> M bool.
Extract Inlined Constant equal => "Symbol.equal".
(* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
Parameter hash : Symbol.T.t -> M int.
Extract Inlined Constant hash => "Symbol.hash".
(* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
Parameter print : Format.formatter -> Symbol.T.t -> M unit.
Extract Inlined Constant print => "Symbol.print".
(* module Set = Int_ids.Symbol.Set: declared again here under this name. *)
Module Set_.
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Definition elt : Type := Int_ids.Symbol.Set_.elt.
  Extract Inlined Constant elt => "Symbol.Set.elt".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Symbol.Set_.t.
  Extract Inlined Constant t => "Symbol.Set.t".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Symbol.Set.empty".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Symbol.Set.union".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Symbol.Set.fold".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter cardinal : t -> M int.
  Extract Inlined Constant cardinal => "Symbol.Set.cardinal".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter of_list : list elt -> M t.
  Extract Inlined Constant of_list => "Symbol.Set.of_list".
End Set_.
(* module Map = Int_ids.Symbol.Map: declared again here under this name. *)
Module Map.
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Definition key : Type := Int_ids.Symbol.Map.key.
  Extract Inlined Constant key => "Symbol.Map.key".
  (* module Set = Int_ids.Symbol.Map.Set: declared again here under this name. *)
  Module Set_.
    (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
    Definition t : Type := Int_ids.Symbol.Map.Set_.t.
    Extract Inlined Constant t => "Symbol.Map.Set.t".
  End Set_.
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Definition t (A : Type) : Type := Int_ids.Symbol.Map.t A.
  Extract Constant t "'a1" => "('a1) Symbol.Map.t".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Symbol.Map.empty".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Symbol.Map.add".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Symbol.Map.singleton".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Symbol.Map.fold".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Symbol.Map.find".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
  Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Symbol.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
  (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
  Parameter keys : forall {A : Type}, t A -> M Symbol.Map.Set_.t.
  Extract Inlined Constant keys => "Symbol.Map.keys".
End Map.
(* int_ids.mli:164  val linkage_name : t -> Linkage_name.t *)
Parameter linkage_name : t -> M Linkage_name.t.
Extract Inlined Constant linkage_name => "Symbol.linkage_name".
(* symbol.mli:28  val manufacture : Compilation_unit.t -> string -> t *)
Parameter manufacture : Compilation_unit.t -> string -> M t.
Extract Inlined Constant manufacture => "Symbol.manufacture".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Symbol. End Symbol.
