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
From SimplifyPort.decl Require Compilation_unit Debuginfo Format Int_ids Or_null Seq.

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
  Parameter remove : elt -> t -> M t.
  Extract Inlined Constant remove => "Code_id.Set.remove".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Code_id.Set.union".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union_sharing : t -> t -> M t.
  Extract Inlined Constant union_sharing => "Code_id.Set.union_sharing".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union_shared : t -> t -> M t.
  Extract Inlined Constant union_shared => "Code_id.Set.union_shared".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter inter : t -> t -> M t.
  Extract Inlined Constant inter => "Code_id.Set.inter".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter disjoint : t -> t -> M bool.
  Extract Inlined Constant disjoint => "Code_id.Set.disjoint".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter diff : t -> t -> M t.
  Extract Inlined Constant diff => "Code_id.Set.diff".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter diff_sharing : t -> t -> M t.
  Extract Inlined Constant diff_sharing => "Code_id.Set.diff_sharing".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter diff_shared : t -> t -> M t.
  Extract Inlined Constant diff_shared => "Code_id.Set.diff_shared".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter compare : t -> t -> M int.
  Extract Inlined Constant compare => "Code_id.Set.compare".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Code_id.Set.equal".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter subset : t -> t -> M bool.
  Extract Inlined Constant subset => "Code_id.Set.subset".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter iter : (elt -> M unit) -> t -> M unit.
  Extract Inlined Constant iter => "Code_id.Set.iter".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter map : (elt -> M elt) -> t -> M t.
  Extract Inlined Constant map => "Code_id.Set.map".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Code_id.Set.fold".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter for_all : (elt -> M bool) -> t -> M bool.
  Extract Inlined Constant for_all => "Code_id.Set.for_all".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter exists_ : (elt -> M bool) -> t -> M bool.
  Extract Inlined Constant exists_ => "Code_id.Set.exists".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter filter : (elt -> M bool) -> t -> M t.
  Extract Inlined Constant filter => "Code_id.Set.filter".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
  Extract Inlined Constant filter_map => "Code_id.Set.filter_map".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter partition : (elt -> M bool) -> t -> M (t * t).
  Extract Inlined Constant partition => "Code_id.Set.partition".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter cardinal : t -> M int.
  Extract Inlined Constant cardinal => "Code_id.Set.cardinal".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter elements : t -> M (list elt).
  Extract Inlined Constant elements => "Code_id.Set.elements".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter min_elt : t -> M elt.
  Extract Inlined Constant min_elt => "Code_id.Set.min_elt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter min_elt_opt : t -> M (option elt).
  Extract Inlined Constant min_elt_opt => "Code_id.Set.min_elt_opt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter max_elt : t -> M elt.
  Extract Inlined Constant max_elt => "Code_id.Set.max_elt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter max_elt_opt : t -> M (option elt).
  Extract Inlined Constant max_elt_opt => "Code_id.Set.max_elt_opt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter choose : t -> M elt.
  Extract Inlined Constant choose => "Code_id.Set.choose".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter choose_opt : t -> M (option elt).
  Extract Inlined Constant choose_opt => "Code_id.Set.choose_opt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter split : elt -> t -> M (tuple3 t bool t).
  Extract Inlined Constant split => "Code_id.Set.split".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter find : elt -> t -> M elt.
  Extract Inlined Constant find => "Code_id.Set.find".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter of_list : list elt -> M t.
  Extract Inlined Constant of_list => "Code_id.Set.of_list".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter to_seq : t -> Seq.t elt.
  Extract Inlined Constant to_seq => "Code_id.Set.to_seq".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Code_id.Set.print".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter to_string : t -> M string.
  Extract Inlined Constant to_string => "Code_id.Set.to_string".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union_list : list t -> M t.
  Extract Inlined Constant union_list => "Code_id.Set.union_list".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter get_singleton : t -> M (option elt).
  Extract Inlined Constant get_singleton => "Code_id.Set.get_singleton".
End Set_.
(* module Map = Int_ids.Code_id.Map: declared again here under this name. *)
Module Map.
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Definition key : Type := Int_ids.Code_id.Map.key.
  Extract Inlined Constant key => "Code_id.Map.key".
  (* module Set = Int_ids.Code_id.Map.Set: declared again here under this name. *)
  Module Set_.
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Definition elt : Type := Int_ids.Code_id.Map.Set_.elt.
    Extract Inlined Constant elt => "Code_id.Map.Set.elt".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Definition t : Type := Int_ids.Code_id.Map.Set_.t.
    Extract Inlined Constant t => "Code_id.Map.Set.t".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Code_id.Map.Set.empty".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Code_id.Map.Set.is_empty".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Code_id.Map.Set.mem".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Code_id.Map.Set.add".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Code_id.Map.Set.singleton".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Code_id.Map.Set.remove".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Code_id.Map.Set.union".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Code_id.Map.Set.union_sharing".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Code_id.Map.Set.union_shared".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Code_id.Map.Set.inter".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Code_id.Map.Set.disjoint".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Code_id.Map.Set.diff".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Code_id.Map.Set.diff_sharing".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Code_id.Map.Set.diff_shared".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Code_id.Map.Set.compare".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Code_id.Map.Set.equal".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Code_id.Map.Set.subset".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Code_id.Map.Set.iter".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Code_id.Map.Set.map".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Code_id.Map.Set.fold".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Code_id.Map.Set.for_all".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Code_id.Map.Set.exists".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Code_id.Map.Set.filter".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Code_id.Map.Set.filter_map".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Code_id.Map.Set.partition".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Code_id.Map.Set.cardinal".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Code_id.Map.Set.elements".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Code_id.Map.Set.min_elt".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Code_id.Map.Set.min_elt_opt".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Code_id.Map.Set.max_elt".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Code_id.Map.Set.max_elt_opt".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Code_id.Map.Set.choose".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Code_id.Map.Set.choose_opt".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Code_id.Map.Set.split".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Code_id.Map.Set.find".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Code_id.Map.Set.of_list".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Code_id.Map.Set.to_seq".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Code_id.Map.Set.print".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Code_id.Map.Set.to_string".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Code_id.Map.Set.union_list".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Code_id.Map.Set.get_singleton".
  End Set_.
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Definition t (A : Type) : Type := Int_ids.Code_id.Map.t A.
  Extract Constant t "'a1" => "('a1) Code_id.Map.t".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Code_id.Map.empty".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter is_empty : forall {A : Type}, t A -> M bool.
  Extract Inlined Constant is_empty => "Code_id.Map.is_empty".
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
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Code_id.Map.singleton".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter remove : forall {A : Type}, key -> t A -> M (t A).
  Extract Inlined Constant remove => "Code_id.Map.remove".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
  Extract Inlined Constant merge => "Code_id.Map.merge".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union => "Code_id.Map.union".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_sharing => "Code_id.Map.union_sharing".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_shared => "Code_id.Map.union_shared".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total => "Code_id.Map.union_total".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total_shared => "Code_id.Map.union_total_shared".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
  Extract Inlined Constant union_left_biased => "Code_id.Map.union_left_biased".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
  Extract Inlined Constant union_right_biased => "Code_id.Map.union_right_biased".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant update_many => "Code_id.Map.update_many".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
  Extract Inlined Constant compare => "Code_id.Map.compare".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
  Extract Inlined Constant equal => "Code_id.Map.equal".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
  Extract Inlined Constant iter => "Code_id.Map.iter".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Code_id.Map.fold".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant for_all => "Code_id.Map.for_all".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant exists_ => "Code_id.Map.exists".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
  Extract Inlined Constant filter => "Code_id.Map.filter".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
  Extract Inlined Constant filter_map => "Code_id.Map.filter_map".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant filter_map_sharing => "Code_id.Map.filter_map_sharing".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
  Extract Inlined Constant partition => "Code_id.Map.partition".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter cardinal : forall {A : Type}, t A -> M int.
  Extract Inlined Constant cardinal => "Code_id.Map.cardinal".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
  Extract Inlined Constant bindings => "Code_id.Map.bindings".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter min_binding : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant min_binding => "Code_id.Map.min_binding".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant min_binding_opt => "Code_id.Map.min_binding_opt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter max_binding : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant max_binding => "Code_id.Map.max_binding".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant max_binding_opt => "Code_id.Map.max_binding_opt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter choose : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant choose => "Code_id.Map.choose".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant choose_opt => "Code_id.Map.choose_opt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
  Extract Inlined Constant split => "Code_id.Map.split".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Code_id.Map.find".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  Extract Inlined Constant find_opt => "Code_id.Map.find_opt".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  Extract Inlined Constant find_or_null => "Code_id.Map.find_or_null".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Code_id.Map.map".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
  Extract Inlined Constant mapi => "Code_id.Map.mapi".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
  Extract Inlined Constant to_seq => "Code_id.Map.to_seq".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print_debug => "Code_id.Map.print_debug".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
  Extract Inlined Constant of_list => "Code_id.Map.of_list".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
  Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Code_id.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
  Extract Inlined Constant map_keys => "Code_id.Map.map_keys".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter keys : forall {A : Type}, t A -> M Code_id.Map.Set_.t.
  Extract Inlined Constant keys => "Code_id.Map.keys".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter data : forall {A : Type}, t A -> M (list A).
  Extract Inlined Constant data => "Code_id.Map.data".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter of_set : forall {A : Type}, (key -> M A) -> Code_id.Map.Set_.t -> M (t A).
  Extract Inlined Constant of_set => "Code_id.Map.of_set".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Code_id.Map.print".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
  Extract Inlined Constant subset_domain => "Code_id.Map.subset_domain".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
  Extract Inlined Constant diff_domains => "Code_id.Map.diff_domains".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
  Extract Inlined Constant inter => "Code_id.Map.inter".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant diff => "Code_id.Map.diff".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant diff_sharing => "Code_id.Map.diff_sharing".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant diff_shared => "Code_id.Map.diff_shared".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
  Extract Inlined Constant inter_domain_is_non_empty => "Code_id.Map.inter_domain_is_non_empty".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant get_singleton => "Code_id.Map.get_singleton".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
  Extract Inlined Constant replace => "Code_id.Map.replace".
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
  Extract Inlined Constant map_sharing => "Code_id.Map.map_sharing".
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
