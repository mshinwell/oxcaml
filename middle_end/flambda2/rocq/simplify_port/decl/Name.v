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
   (Git blob 4a40548bbd28edf9b1748782b14e67dd06dfaaa5). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Int_ids Or_null Seq Symbol Variable_.

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
  Parameter is_empty : t -> M bool.
  Extract Inlined Constant is_empty => "Name.Set.is_empty".
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
  Parameter remove : elt -> t -> M t.
  Extract Inlined Constant remove => "Name.Set.remove".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Name.Set.union".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_sharing : t -> t -> M t.
  Extract Inlined Constant union_sharing => "Name.Set.union_sharing".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_shared : t -> t -> M t.
  Extract Inlined Constant union_shared => "Name.Set.union_shared".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter inter : t -> t -> M t.
  Extract Inlined Constant inter => "Name.Set.inter".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter disjoint : t -> t -> M bool.
  Extract Inlined Constant disjoint => "Name.Set.disjoint".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff : t -> t -> M t.
  Extract Inlined Constant diff => "Name.Set.diff".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff_sharing : t -> t -> M t.
  Extract Inlined Constant diff_sharing => "Name.Set.diff_sharing".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff_shared : t -> t -> M t.
  Extract Inlined Constant diff_shared => "Name.Set.diff_shared".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter compare : t -> t -> M int.
  Extract Inlined Constant compare => "Name.Set.compare".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Name.Set.equal".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter subset : t -> t -> M bool.
  Extract Inlined Constant subset => "Name.Set.subset".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter iter : (elt -> M unit) -> t -> M unit.
  Extract Inlined Constant iter => "Name.Set.iter".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter map : (elt -> M elt) -> t -> M t.
  Extract Inlined Constant map => "Name.Set.map".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Name.Set.fold".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter for_all : (elt -> M bool) -> t -> M bool.
  Extract Inlined Constant for_all => "Name.Set.for_all".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter exists_ : (elt -> M bool) -> t -> M bool.
  Extract Inlined Constant exists_ => "Name.Set.exists".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter filter : (elt -> M bool) -> t -> M t.
  Extract Inlined Constant filter => "Name.Set.filter".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
  Extract Inlined Constant filter_map => "Name.Set.filter_map".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter partition : (elt -> M bool) -> t -> M (t * t).
  Extract Inlined Constant partition => "Name.Set.partition".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter cardinal : t -> M int.
  Extract Inlined Constant cardinal => "Name.Set.cardinal".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter elements : t -> M (list elt).
  Extract Inlined Constant elements => "Name.Set.elements".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter min_elt : t -> M elt.
  Extract Inlined Constant min_elt => "Name.Set.min_elt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter min_elt_opt : t -> M (option elt).
  Extract Inlined Constant min_elt_opt => "Name.Set.min_elt_opt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter max_elt : t -> M elt.
  Extract Inlined Constant max_elt => "Name.Set.max_elt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter max_elt_opt : t -> M (option elt).
  Extract Inlined Constant max_elt_opt => "Name.Set.max_elt_opt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter choose : t -> M elt.
  Extract Inlined Constant choose => "Name.Set.choose".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter choose_opt : t -> M (option elt).
  Extract Inlined Constant choose_opt => "Name.Set.choose_opt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter split : elt -> t -> M (tuple3 t bool t).
  Extract Inlined Constant split => "Name.Set.split".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter find : elt -> t -> M elt.
  Extract Inlined Constant find => "Name.Set.find".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter of_list : list elt -> M t.
  Extract Inlined Constant of_list => "Name.Set.of_list".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter to_seq : t -> Seq.t elt.
  Extract Inlined Constant to_seq => "Name.Set.to_seq".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Name.Set.print".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter to_string : t -> M string.
  Extract Inlined Constant to_string => "Name.Set.to_string".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_list : list t -> M t.
  Extract Inlined Constant union_list => "Name.Set.union_list".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter get_singleton : t -> M (option elt).
  Extract Inlined Constant get_singleton => "Name.Set.get_singleton".
End Set_.
(* module Map = Int_ids.Name.Map: declared again here under this name. *)
Module Map.
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Definition key : Type := Int_ids.Name.Map.key.
  Extract Inlined Constant key => "Name.Map.key".
  (* module Set = Int_ids.Name.Map.Set: declared again here under this name. *)
  Module Set_.
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Definition elt : Type := Int_ids.Name.Map.Set_.elt.
    Extract Inlined Constant elt => "Name.Map.Set.elt".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Definition t : Type := Int_ids.Name.Map.Set_.t.
    Extract Inlined Constant t => "Name.Map.Set.t".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Name.Map.Set.empty".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Name.Map.Set.is_empty".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Name.Map.Set.mem".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Name.Map.Set.add".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Name.Map.Set.singleton".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Name.Map.Set.remove".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Name.Map.Set.union".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Name.Map.Set.union_sharing".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Name.Map.Set.union_shared".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Name.Map.Set.inter".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Name.Map.Set.disjoint".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Name.Map.Set.diff".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Name.Map.Set.diff_sharing".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Name.Map.Set.diff_shared".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Name.Map.Set.compare".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Name.Map.Set.equal".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Name.Map.Set.subset".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Name.Map.Set.iter".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Name.Map.Set.map".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Name.Map.Set.fold".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Name.Map.Set.for_all".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Name.Map.Set.exists".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Name.Map.Set.filter".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Name.Map.Set.filter_map".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Name.Map.Set.partition".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Name.Map.Set.cardinal".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Name.Map.Set.elements".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Name.Map.Set.min_elt".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Name.Map.Set.min_elt_opt".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Name.Map.Set.max_elt".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Name.Map.Set.max_elt_opt".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Name.Map.Set.choose".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Name.Map.Set.choose_opt".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Name.Map.Set.split".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Name.Map.Set.find".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Name.Map.Set.of_list".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Name.Map.Set.to_seq".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Name.Map.Set.print".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Name.Map.Set.to_string".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Name.Map.Set.union_list".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Name.Map.Set.get_singleton".
  End Set_.
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Definition t (A : Type) : Type := Int_ids.Name.Map.t A.
  Extract Constant t "'a1" => "('a1) Name.Map.t".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Name.Map.empty".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter is_empty : forall {A : Type}, t A -> M bool.
  Extract Inlined Constant is_empty => "Name.Map.is_empty".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter mem : forall {A : Type}, key -> t A -> M bool.
  Extract Inlined Constant mem => "Name.Map.mem".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Name.Map.add".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Name.Map.update".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Name.Map.singleton".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter remove : forall {A : Type}, key -> t A -> M (t A).
  Extract Inlined Constant remove => "Name.Map.remove".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
  Extract Inlined Constant merge => "Name.Map.merge".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union => "Name.Map.union".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_sharing => "Name.Map.union_sharing".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_shared => "Name.Map.union_shared".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total => "Name.Map.union_total".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total_shared => "Name.Map.union_total_shared".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
  Extract Inlined Constant union_left_biased => "Name.Map.union_left_biased".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
  Extract Inlined Constant union_right_biased => "Name.Map.union_right_biased".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant update_many => "Name.Map.update_many".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
  Extract Inlined Constant compare => "Name.Map.compare".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
  Extract Inlined Constant equal => "Name.Map.equal".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
  Extract Inlined Constant iter => "Name.Map.iter".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Name.Map.fold".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant for_all => "Name.Map.for_all".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant exists_ => "Name.Map.exists".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
  Extract Inlined Constant filter => "Name.Map.filter".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
  Extract Inlined Constant filter_map => "Name.Map.filter_map".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant filter_map_sharing => "Name.Map.filter_map_sharing".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
  Extract Inlined Constant partition => "Name.Map.partition".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter cardinal : forall {A : Type}, t A -> M int.
  Extract Inlined Constant cardinal => "Name.Map.cardinal".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
  Extract Inlined Constant bindings => "Name.Map.bindings".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter min_binding : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant min_binding => "Name.Map.min_binding".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant min_binding_opt => "Name.Map.min_binding_opt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter max_binding : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant max_binding => "Name.Map.max_binding".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant max_binding_opt => "Name.Map.max_binding_opt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter choose : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant choose => "Name.Map.choose".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant choose_opt => "Name.Map.choose_opt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
  Extract Inlined Constant split => "Name.Map.split".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Name.Map.find".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  Extract Inlined Constant find_opt => "Name.Map.find_opt".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  Extract Inlined Constant find_or_null => "Name.Map.find_or_null".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Name.Map.map".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
  Extract Inlined Constant mapi => "Name.Map.mapi".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
  Extract Inlined Constant to_seq => "Name.Map.to_seq".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print_debug => "Name.Map.print_debug".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
  Extract Inlined Constant of_list => "Name.Map.of_list".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
  Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Name.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
  Extract Inlined Constant map_keys => "Name.Map.map_keys".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter keys : forall {A : Type}, t A -> M Name.Map.Set_.t.
  Extract Inlined Constant keys => "Name.Map.keys".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter data : forall {A : Type}, t A -> M (list A).
  Extract Inlined Constant data => "Name.Map.data".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter of_set : forall {A : Type}, (key -> M A) -> Name.Map.Set_.t -> M (t A).
  Extract Inlined Constant of_set => "Name.Map.of_set".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Name.Map.print".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
  Extract Inlined Constant subset_domain => "Name.Map.subset_domain".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
  Extract Inlined Constant diff_domains => "Name.Map.diff_domains".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
  Extract Inlined Constant inter => "Name.Map.inter".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant diff => "Name.Map.diff".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant diff_sharing => "Name.Map.diff_sharing".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant diff_shared => "Name.Map.diff_shared".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
  Extract Inlined Constant inter_domain_is_non_empty => "Name.Map.inter_domain_is_non_empty".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant get_singleton => "Name.Map.get_singleton".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
  Extract Inlined Constant replace => "Name.Map.replace".
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
  Extract Inlined Constant map_sharing => "Name.Map.map_sharing".
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
