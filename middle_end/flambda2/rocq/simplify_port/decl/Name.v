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
   Simplify uses of the compiler's module [Name], after its interface
   middle_end/flambda2/identifiers/name.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Int_ids Symbol Variable_.

(* int_ids.mli:176  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Name.t.
Extract Inlined Constant t => "Name.t".
(* module T = Int_ids.Name.T: declared again here under this name. *)
Module T.
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Name.T.t.
  Extract Inlined Constant t => "Name.T.t".
End T.
(* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
Parameter equal : Name.T.t -> Name.T.t -> M bool.
Extract Inlined Constant equal => "Name.equal".
(* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
Parameter print : Format.formatter -> Name.T.t -> M unit.
Extract Inlined Constant print => "Name.print".
(* module Set = Int_ids.Name.Set: declared again here under this name. *)
Module Set_.
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Definition elt : Type := Int_ids.Name.Set_.elt.
  Extract Inlined Constant elt => "Name.Set.elt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Name.Set_.t.
  Extract Inlined Constant t => "Name.Set.t".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Name.Set.empty".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Name.Set.mem".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Name.Set.add".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter singleton : elt -> M t.
  Extract Inlined Constant singleton => "Name.Set.singleton".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Name.Set.union".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter disjoint : t -> t -> M bool.
  Extract Inlined Constant disjoint => "Name.Set.disjoint".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff : t -> t -> M t.
  Extract Inlined Constant diff => "Name.Set.diff".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter iter : (elt -> M unit) -> t -> M unit.
  Extract Inlined Constant iter => "Name.Set.iter".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter of_list : list elt -> M t.
  Extract Inlined Constant of_list => "Name.Set.of_list".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Name.Set.print".
End Set_.
(* module Map = Int_ids.Name.Map: declared again here under this name. *)
Module Map.
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Definition key : Type := Int_ids.Name.Map.key.
  Extract Inlined Constant key => "Name.Map.key".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Definition t (A : Type) : Type := Int_ids.Name.Map.t A.
  Extract Constant t "'a1" => "('a1) Name.Map.t".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Name.Map.empty".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Name.Map.update".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Name.Map.singleton".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Name.Map.fold".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Name.Map.find".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Name.Map.print".
End Map.
(* int_ids.mli:180  val var : Variable.t -> t *)
Parameter var : Int_ids.Variable_.t -> M t.
Extract Inlined Constant var => "Name.var".
(* int_ids.mli:186  val symbol : Symbol.t -> t *)
Parameter symbol : Int_ids.Symbol.t -> M t.
Extract Inlined Constant symbol => "Name.symbol".
(* int_ids.mli:188  val pattern_match : t -> var:(Variable.t -> 'a) -> symbol:(Symbol.t -> 'a) -> 'a *)
Parameter pattern_match : forall {A : Type}, t -> (Int_ids.Variable_.t -> M A) -> (Int_ids.Symbol.t -> M A) -> M A.
Extract Inlined Constant pattern_match => "Name.pattern_match".
(* name.mli:24  val set_of_var_set : Variable.Set.t -> Set.t *)
Parameter set_of_var_set : Variable_.Set_.t -> M Name.Set_.t.
Extract Inlined Constant set_of_var_set => "Name.set_of_var_set".
(* name.mli:26  val set_of_symbol_set : Symbol.Set.t -> Set.t *)
Parameter set_of_symbol_set : Symbol.Set_.t -> M Name.Set_.t.
Extract Inlined Constant set_of_symbol_set => "Name.set_of_symbol_set".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Name. End Name.
