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
   Simplify uses of the compiler's module [Target_ocaml_int], after its interface
   middle_end/flambda2/numbers/target_ocaml_int.mli
   (Git blob aa955093363fa4d8fc60eab59354979077beb6db). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Or_null Seq Stdlib_ Target_system Targetint_32_64.

(* target_ocaml_int.mli:21  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Target_ocaml_int.t".
Module T.
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Definition t : Type := Target_ocaml_int.t.
  Extract Inlined Constant t => "Target_ocaml_int.T.t".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Target_ocaml_int.T.equal".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter hash : t -> M int.
  Extract Inlined Constant hash => "Target_ocaml_int.T.hash".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter compare : t -> t -> M int.
  Extract Inlined Constant compare => "Target_ocaml_int.T.compare".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Target_ocaml_int.T.print".
End T.
(* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
Parameter equal : Target_ocaml_int.T.t -> Target_ocaml_int.T.t -> M bool.
Extract Inlined Constant equal => "Target_ocaml_int.equal".
(* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
Parameter hash : Target_ocaml_int.T.t -> M int.
Extract Inlined Constant hash => "Target_ocaml_int.hash".
(* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
Parameter compare : Target_ocaml_int.T.t -> Target_ocaml_int.T.t -> M int.
Extract Inlined Constant compare => "Target_ocaml_int.compare".
(* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Target_ocaml_int.T.t -> M unit.
Extract Inlined Constant print => "Target_ocaml_int.print".
Module Set_.
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Definition elt : Type := Target_ocaml_int.t.
  Extract Inlined Constant elt => "Target_ocaml_int.Set.elt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Target_ocaml_int.Set.t".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Target_ocaml_int.Set.empty".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter is_empty : t -> M bool.
  Extract Inlined Constant is_empty => "Target_ocaml_int.Set.is_empty".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Target_ocaml_int.Set.mem".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Target_ocaml_int.Set.add".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter singleton : elt -> M t.
  Extract Inlined Constant singleton => "Target_ocaml_int.Set.singleton".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter remove : elt -> t -> M t.
  Extract Inlined Constant remove => "Target_ocaml_int.Set.remove".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Target_ocaml_int.Set.union".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union_sharing : t -> t -> M t.
  Extract Inlined Constant union_sharing => "Target_ocaml_int.Set.union_sharing".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union_shared : t -> t -> M t.
  Extract Inlined Constant union_shared => "Target_ocaml_int.Set.union_shared".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter inter : t -> t -> M t.
  Extract Inlined Constant inter => "Target_ocaml_int.Set.inter".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter disjoint : t -> t -> M bool.
  Extract Inlined Constant disjoint => "Target_ocaml_int.Set.disjoint".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter diff : t -> t -> M t.
  Extract Inlined Constant diff => "Target_ocaml_int.Set.diff".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter diff_sharing : t -> t -> M t.
  Extract Inlined Constant diff_sharing => "Target_ocaml_int.Set.diff_sharing".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter diff_shared : t -> t -> M t.
  Extract Inlined Constant diff_shared => "Target_ocaml_int.Set.diff_shared".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter compare : t -> t -> M int.
  Extract Inlined Constant compare => "Target_ocaml_int.Set.compare".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Target_ocaml_int.Set.equal".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter subset : t -> t -> M bool.
  Extract Inlined Constant subset => "Target_ocaml_int.Set.subset".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter iter : (elt -> M unit) -> t -> M unit.
  Extract Inlined Constant iter => "Target_ocaml_int.Set.iter".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter map : (elt -> M elt) -> t -> M t.
  Extract Inlined Constant map => "Target_ocaml_int.Set.map".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Target_ocaml_int.Set.fold".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter for_all : (elt -> M bool) -> t -> M bool.
  Extract Inlined Constant for_all => "Target_ocaml_int.Set.for_all".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter exists_ : (elt -> M bool) -> t -> M bool.
  Extract Inlined Constant exists_ => "Target_ocaml_int.Set.exists".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter filter : (elt -> M bool) -> t -> M t.
  Extract Inlined Constant filter => "Target_ocaml_int.Set.filter".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
  Extract Inlined Constant filter_map => "Target_ocaml_int.Set.filter_map".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter partition : (elt -> M bool) -> t -> M (t * t).
  Extract Inlined Constant partition => "Target_ocaml_int.Set.partition".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter cardinal : t -> M int.
  Extract Inlined Constant cardinal => "Target_ocaml_int.Set.cardinal".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter elements : t -> M (list elt).
  Extract Inlined Constant elements => "Target_ocaml_int.Set.elements".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter min_elt : t -> M elt.
  Extract Inlined Constant min_elt => "Target_ocaml_int.Set.min_elt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter min_elt_opt : t -> M (option elt).
  Extract Inlined Constant min_elt_opt => "Target_ocaml_int.Set.min_elt_opt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter max_elt : t -> M elt.
  Extract Inlined Constant max_elt => "Target_ocaml_int.Set.max_elt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter max_elt_opt : t -> M (option elt).
  Extract Inlined Constant max_elt_opt => "Target_ocaml_int.Set.max_elt_opt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter choose : t -> M elt.
  Extract Inlined Constant choose => "Target_ocaml_int.Set.choose".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter choose_opt : t -> M (option elt).
  Extract Inlined Constant choose_opt => "Target_ocaml_int.Set.choose_opt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter split : elt -> t -> M (tuple3 t bool t).
  Extract Inlined Constant split => "Target_ocaml_int.Set.split".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter find : elt -> t -> M elt.
  Extract Inlined Constant find => "Target_ocaml_int.Set.find".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter of_list : list elt -> M t.
  Extract Inlined Constant of_list => "Target_ocaml_int.Set.of_list".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter to_seq : t -> Seq.t elt.
  Extract Inlined Constant to_seq => "Target_ocaml_int.Set.to_seq".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Target_ocaml_int.Set.print".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter to_string : t -> M string.
  Extract Inlined Constant to_string => "Target_ocaml_int.Set.to_string".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union_list : list t -> M t.
  Extract Inlined Constant union_list => "Target_ocaml_int.Set.union_list".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter get_singleton : t -> M (option elt).
  Extract Inlined Constant get_singleton => "Target_ocaml_int.Set.get_singleton".
End Set_.
Module Map.
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Definition key : Type := Target_ocaml_int.t.
  Extract Inlined Constant key => "Target_ocaml_int.Map.key".
  Module Set_.
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Definition elt : Type := Target_ocaml_int.t.
    Extract Inlined Constant elt => "Target_ocaml_int.Map.Set.elt".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Definition t : Type := Target_ocaml_int.Set_.t.
    Extract Inlined Constant t => "Target_ocaml_int.Map.Set.t".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Target_ocaml_int.Map.Set.empty".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Target_ocaml_int.Map.Set.is_empty".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Target_ocaml_int.Map.Set.mem".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Target_ocaml_int.Map.Set.add".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Target_ocaml_int.Map.Set.singleton".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Target_ocaml_int.Map.Set.remove".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Target_ocaml_int.Map.Set.union".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Target_ocaml_int.Map.Set.union_sharing".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Target_ocaml_int.Map.Set.union_shared".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Target_ocaml_int.Map.Set.inter".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Target_ocaml_int.Map.Set.disjoint".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Target_ocaml_int.Map.Set.diff".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Target_ocaml_int.Map.Set.diff_sharing".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Target_ocaml_int.Map.Set.diff_shared".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Target_ocaml_int.Map.Set.compare".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Target_ocaml_int.Map.Set.equal".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Target_ocaml_int.Map.Set.subset".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Target_ocaml_int.Map.Set.iter".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Target_ocaml_int.Map.Set.map".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Target_ocaml_int.Map.Set.fold".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Target_ocaml_int.Map.Set.for_all".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Target_ocaml_int.Map.Set.exists".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Target_ocaml_int.Map.Set.filter".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Target_ocaml_int.Map.Set.filter_map".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Target_ocaml_int.Map.Set.partition".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Target_ocaml_int.Map.Set.cardinal".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Target_ocaml_int.Map.Set.elements".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Target_ocaml_int.Map.Set.min_elt".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Target_ocaml_int.Map.Set.min_elt_opt".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Target_ocaml_int.Map.Set.max_elt".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Target_ocaml_int.Map.Set.max_elt_opt".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Target_ocaml_int.Map.Set.choose".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Target_ocaml_int.Map.Set.choose_opt".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Target_ocaml_int.Map.Set.split".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Target_ocaml_int.Map.Set.find".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Target_ocaml_int.Map.Set.of_list".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Target_ocaml_int.Map.Set.to_seq".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Target_ocaml_int.Map.Set.print".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Target_ocaml_int.Map.Set.to_string".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Target_ocaml_int.Map.Set.union_list".
    (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Target_ocaml_int.Map.Set.get_singleton".
  End Set_.
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Target_ocaml_int.Map.t".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Target_ocaml_int.Map.empty".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter is_empty : forall {A : Type}, t A -> M bool.
  Extract Inlined Constant is_empty => "Target_ocaml_int.Map.is_empty".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter mem : forall {A : Type}, key -> t A -> M bool.
  Extract Inlined Constant mem => "Target_ocaml_int.Map.mem".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Target_ocaml_int.Map.add".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Target_ocaml_int.Map.update".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Target_ocaml_int.Map.singleton".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter remove : forall {A : Type}, key -> t A -> M (t A).
  Extract Inlined Constant remove => "Target_ocaml_int.Map.remove".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
  Extract Inlined Constant merge => "Target_ocaml_int.Map.merge".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union => "Target_ocaml_int.Map.union".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_sharing => "Target_ocaml_int.Map.union_sharing".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_shared => "Target_ocaml_int.Map.union_shared".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total => "Target_ocaml_int.Map.union_total".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total_shared => "Target_ocaml_int.Map.union_total_shared".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
  Extract Inlined Constant union_left_biased => "Target_ocaml_int.Map.union_left_biased".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
  Extract Inlined Constant union_right_biased => "Target_ocaml_int.Map.union_right_biased".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant update_many => "Target_ocaml_int.Map.update_many".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
  Extract Inlined Constant compare => "Target_ocaml_int.Map.compare".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
  Extract Inlined Constant equal => "Target_ocaml_int.Map.equal".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
  Extract Inlined Constant iter => "Target_ocaml_int.Map.iter".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Target_ocaml_int.Map.fold".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant for_all => "Target_ocaml_int.Map.for_all".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant exists_ => "Target_ocaml_int.Map.exists".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
  Extract Inlined Constant filter => "Target_ocaml_int.Map.filter".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
  Extract Inlined Constant filter_map => "Target_ocaml_int.Map.filter_map".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant filter_map_sharing => "Target_ocaml_int.Map.filter_map_sharing".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
  Extract Inlined Constant partition => "Target_ocaml_int.Map.partition".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter cardinal : forall {A : Type}, t A -> M int.
  Extract Inlined Constant cardinal => "Target_ocaml_int.Map.cardinal".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
  Extract Inlined Constant bindings => "Target_ocaml_int.Map.bindings".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter min_binding : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant min_binding => "Target_ocaml_int.Map.min_binding".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant min_binding_opt => "Target_ocaml_int.Map.min_binding_opt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter max_binding : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant max_binding => "Target_ocaml_int.Map.max_binding".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant max_binding_opt => "Target_ocaml_int.Map.max_binding_opt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter choose : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant choose => "Target_ocaml_int.Map.choose".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant choose_opt => "Target_ocaml_int.Map.choose_opt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
  Extract Inlined Constant split => "Target_ocaml_int.Map.split".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Target_ocaml_int.Map.find".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  Extract Inlined Constant find_opt => "Target_ocaml_int.Map.find_opt".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  Extract Inlined Constant find_or_null => "Target_ocaml_int.Map.find_or_null".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Target_ocaml_int.Map.map".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
  Extract Inlined Constant mapi => "Target_ocaml_int.Map.mapi".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
  Extract Inlined Constant to_seq => "Target_ocaml_int.Map.to_seq".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print_debug => "Target_ocaml_int.Map.print_debug".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
  Extract Inlined Constant of_list => "Target_ocaml_int.Map.of_list".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
  Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Target_ocaml_int.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
  Extract Inlined Constant map_keys => "Target_ocaml_int.Map.map_keys".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter keys : forall {A : Type}, t A -> M Target_ocaml_int.Map.Set_.t.
  Extract Inlined Constant keys => "Target_ocaml_int.Map.keys".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter data : forall {A : Type}, t A -> M (list A).
  Extract Inlined Constant data => "Target_ocaml_int.Map.data".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter of_set : forall {A : Type}, (key -> M A) -> Target_ocaml_int.Map.Set_.t -> M (t A).
  Extract Inlined Constant of_set => "Target_ocaml_int.Map.of_set".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Target_ocaml_int.Map.print".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
  Extract Inlined Constant subset_domain => "Target_ocaml_int.Map.subset_domain".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
  Extract Inlined Constant diff_domains => "Target_ocaml_int.Map.diff_domains".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
  Extract Inlined Constant inter => "Target_ocaml_int.Map.inter".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant diff => "Target_ocaml_int.Map.diff".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant diff_sharing => "Target_ocaml_int.Map.diff_sharing".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant diff_shared => "Target_ocaml_int.Map.diff_shared".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
  Extract Inlined Constant inter_domain_is_non_empty => "Target_ocaml_int.Map.inter_domain_is_non_empty".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant get_singleton => "Target_ocaml_int.Map.get_singleton".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
  Extract Inlined Constant replace => "Target_ocaml_int.Map.replace".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
  Extract Inlined Constant map_sharing => "Target_ocaml_int.Map.map_sharing".
End Map.
(* target_ocaml_int.mli:25  val machine_width : t -> Target_system.Machine_width.t *)
Parameter machine_width : t -> M Target_system.Machine_width.t.
Extract Inlined Constant machine_width => "Target_ocaml_int.machine_width".
(* target_ocaml_int.mli:34  val minus_one : Target_system.Machine_width.t -> t *)
Parameter minus_one : Target_system.Machine_width.t -> M t.
Extract Inlined Constant minus_one => "Target_ocaml_int.minus_one".
(* target_ocaml_int.mli:37  val zero : Target_system.Machine_width.t -> t *)
Parameter zero : Target_system.Machine_width.t -> M t.
Extract Inlined Constant zero => "Target_ocaml_int.zero".
(* target_ocaml_int.mli:40  val one : Target_system.Machine_width.t -> t *)
Parameter one : Target_system.Machine_width.t -> M t.
Extract Inlined Constant one => "Target_ocaml_int.one".
(* target_ocaml_int.mli:49  val zero_one_and_minus_one : Target_system.Machine_width.t -> Set.t *)
Parameter zero_one_and_minus_one : Target_system.Machine_width.t -> M Target_ocaml_int.Set_.t.
Extract Inlined Constant zero_one_and_minus_one => "Target_ocaml_int.zero_one_and_minus_one".
(* target_ocaml_int.mli:52  val bool : Target_system.Machine_width.t -> bool -> t *)
Parameter bool_ : Target_system.Machine_width.t -> bool -> M t.
Extract Inlined Constant bool_ => "Target_ocaml_int.bool".
(* target_ocaml_int.mli:54  val bool_true : Target_system.Machine_width.t -> t *)
Parameter bool_true : Target_system.Machine_width.t -> M t.
Extract Inlined Constant bool_true => "Target_ocaml_int.bool_true".
(* target_ocaml_int.mli:56  val bool_false : Target_system.Machine_width.t -> t *)
Parameter bool_false : Target_system.Machine_width.t -> M t.
Extract Inlined Constant bool_false => "Target_ocaml_int.bool_false".
(* target_ocaml_int.mli:58  val all_bools : Target_system.Machine_width.t -> Set.t *)
Parameter all_bools : Target_system.Machine_width.t -> M Target_ocaml_int.Set_.t.
Extract Inlined Constant all_bools => "Target_ocaml_int.all_bools".
(* target_ocaml_int.mli:63  val ( >= ) : t -> t -> bool *)
Parameter op_gt_eq : t -> t -> M bool.
Extract Inlined Constant op_gt_eq => "Target_ocaml_int.( >= )".
(* target_ocaml_int.mli:65  val ( < ) : t -> t -> bool *)
Parameter op_lt : t -> t -> M bool.
Extract Inlined Constant op_lt => "Target_ocaml_int.( < )".
(* target_ocaml_int.mli:77  val of_int : Target_system.Machine_width.t -> int -> t *)
Parameter of_int : Target_system.Machine_width.t -> int -> M t.
Extract Inlined Constant of_int => "Target_ocaml_int.of_int".
(* target_ocaml_int.mli:81  val of_int_option : Target_system.Machine_width.t -> int -> t option *)
Parameter of_int_option : Target_system.Machine_width.t -> int -> M (option t).
Extract Inlined Constant of_int_option => "Target_ocaml_int.of_int_option".
(* target_ocaml_int.mli:86  val to_int : t -> int *)
Parameter to_int : t -> M int.
Extract Inlined Constant to_int => "Target_ocaml_int.to_int".
(* target_ocaml_int.mli:90  val to_int_option : t -> int option *)
Parameter to_int_option : t -> M (option int).
Extract Inlined Constant to_int_option => "Target_ocaml_int.to_int_option".
(* target_ocaml_int.mli:100  val of_int32 : Target_system.Machine_width.t -> int32 -> t *)
Parameter of_int32 : Target_system.Machine_width.t -> Stdlib_.int32 -> M t.
Extract Inlined Constant of_int32 => "Target_ocaml_int.of_int32".
(* target_ocaml_int.mli:105  val to_int32 : t -> int32 *)
Parameter to_int32 : t -> M Stdlib_.int32.
Extract Inlined Constant to_int32 => "Target_ocaml_int.to_int32".
(* target_ocaml_int.mli:109  val of_int64 : Target_system.Machine_width.t -> int64 -> t *)
Parameter of_int64 : Target_system.Machine_width.t -> Stdlib_.int64 -> M t.
Extract Inlined Constant of_int64 => "Target_ocaml_int.of_int64".
(* target_ocaml_int.mli:112  val to_int64 : t -> int64 *)
Parameter to_int64 : t -> M Stdlib_.int64.
Extract Inlined Constant to_int64 => "Target_ocaml_int.to_int64".
(* target_ocaml_int.mli:116  val of_targetint : Target_system.Machine_width.t -> Targetint_32_64.t -> t *)
Parameter of_targetint : Target_system.Machine_width.t -> Targetint_32_64.t -> M t.
Extract Inlined Constant of_targetint => "Target_ocaml_int.of_targetint".
(* target_ocaml_int.mli:120  val to_targetint : Target_system.Machine_width.t -> t -> Targetint_32_64.t *)
Parameter to_targetint : Target_system.Machine_width.t -> t -> M Targetint_32_64.t.
Extract Inlined Constant to_targetint => "Target_ocaml_int.to_targetint".
(* target_ocaml_int.mli:126  val of_float : Target_system.Machine_width.t -> float -> t *)
Parameter of_float : Target_system.Machine_width.t -> Stdlib_.float_ -> M t.
Extract Inlined Constant of_float => "Target_ocaml_int.of_float".
(* target_ocaml_int.mli:129  val to_float : t -> float *)
Parameter to_float : t -> M Stdlib_.float_.
Extract Inlined Constant to_float => "Target_ocaml_int.to_float".
(* target_ocaml_int.mli:132  val neg : t -> t *)
Parameter neg : t -> M t.
Extract Inlined Constant neg => "Target_ocaml_int.neg".
(* target_ocaml_int.mli:137  val get_least_significant_16_bits_then_byte_swap : t -> t *)
Parameter get_least_significant_16_bits_then_byte_swap : t -> M t.
Extract Inlined Constant get_least_significant_16_bits_then_byte_swap => "Target_ocaml_int.get_least_significant_16_bits_then_byte_swap".
(* target_ocaml_int.mli:140  val add : t -> t -> t *)
Parameter add : t -> t -> M t.
Extract Inlined Constant add => "Target_ocaml_int.add".
(* target_ocaml_int.mli:143  val sub : t -> t -> t *)
Parameter sub : t -> t -> M t.
Extract Inlined Constant sub => "Target_ocaml_int.sub".
(* target_ocaml_int.mli:146  val mul : t -> t -> t *)
Parameter mul : t -> t -> M t.
Extract Inlined Constant mul => "Target_ocaml_int.mul".
(* target_ocaml_int.mli:151  val div : t -> t -> t *)
Parameter div : t -> t -> M t.
Extract Inlined Constant div => "Target_ocaml_int.div".
(* target_ocaml_int.mli:153  val unsigned_div : t -> t -> t *)
Parameter unsigned_div : t -> t -> M t.
Extract Inlined Constant unsigned_div => "Target_ocaml_int.unsigned_div".
(* target_ocaml_int.mli:155  val mod_ : t -> t -> t *)
Parameter mod_ : t -> t -> M t.
Extract Inlined Constant mod_ => "Target_ocaml_int.mod_".
(* target_ocaml_int.mli:157  val unsigned_mod : t -> t -> t *)
Parameter unsigned_mod : t -> t -> M t.
Extract Inlined Constant unsigned_mod => "Target_ocaml_int.unsigned_mod".
(* target_ocaml_int.mli:166  val xor : t -> t -> t *)
Parameter xor : t -> t -> M t.
Extract Inlined Constant xor => "Target_ocaml_int.xor".
(* target_ocaml_int.mli:171  val shift_left : t -> int -> t *)
Parameter shift_left : t -> int -> M t.
Extract Inlined Constant shift_left => "Target_ocaml_int.shift_left".
(* target_ocaml_int.mli:176  val shift_right : t -> int -> t *)
Parameter shift_right : t -> int -> M t.
Extract Inlined Constant shift_right => "Target_ocaml_int.shift_right".
(* target_ocaml_int.mli:182  val shift_right_logical : t -> int -> t *)
Parameter shift_right_logical : t -> int -> M t.
Extract Inlined Constant shift_right_logical => "Target_ocaml_int.shift_right_logical".
(* target_ocaml_int.mli:190  val is_non_negative : t -> bool *)
Parameter is_non_negative : t -> M bool.
Extract Inlined Constant is_non_negative => "Target_ocaml_int.is_non_negative".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Target_ocaml_int. End Target_ocaml_int.
