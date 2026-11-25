(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* CR mshinwell: The inherited Int32/Int64 declarations use the building OCaml's
   standard-library names and types (stdlib/int32.mli and stdlib/int64.mli
   counterparts). The donor rule keeps the notice of
   middle_end/flambda2/numbers/numeric_types.mli. Are additional
   standard-library credits needed for this portion? *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Numeric_types], after its interface
   middle_end/flambda2/numbers/numeric_types.mli
   (Git blob ca9677bd0e80001eff868aed4c75a06b9105e11d). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Int32 Int64 Or_null Seq Stdlib_.

Module Int.
  (* numeric_types.mli:23  include Container_types.S_plus_stdlib with type t = int *)
  Definition t : Type := int.
  Extract Inlined Constant t => "Numeric_types.Int.t".
  Module Map.
    (* container_types_intf.ml:329  module Map : Map_plus_stdlib with type key = t and module Set = Set *)
    Definition key : Type := Numeric_types.Int.t.
    Extract Inlined Constant key => "Numeric_types.Int.Map.key".
    (* container_types_intf.ml:136  type +!'a t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Numeric_types.Int.Map.t".
    (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
    Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
    Extract Inlined Constant find_or_null => "Numeric_types.Int.Map.find_or_null".
    (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Numeric_types.Int.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
    (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
    Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
    Extract Inlined Constant map_keys => "Numeric_types.Int.Map.map_keys".
    (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int.Map.print".
    (* container_types_intf.ml:317  include Stdlib.Map.S with type key := key and type 'a t := 'a t *)
    Parameter empty : forall {A : Type}, t A.
    Extract Inlined Constant empty => "Numeric_types.Int.Map.empty".
    (* container_types_intf.ml:317  include Stdlib.Map.S with type key := key and type 'a t := 'a t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    Extract Inlined Constant add => "Numeric_types.Int.Map.add".
    (* container_types_intf.ml:317  include Stdlib.Map.S with type key := key and type 'a t := 'a t *)
    Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
    Extract Inlined Constant bindings => "Numeric_types.Int.Map.bindings".
    (* container_types_intf.ml:317  include Stdlib.Map.S with type key := key and type 'a t := 'a t *)
    Parameter max_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant max_binding => "Numeric_types.Int.Map.max_binding".
    (* container_types_intf.ml:317  include Stdlib.Map.S with type key := key and type 'a t := 'a t *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    Extract Inlined Constant find => "Numeric_types.Int.Map.find".
    (* container_types_intf.ml:317  include Stdlib.Map.S with type key := key and type 'a t := 'a t *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    Extract Inlined Constant find_opt => "Numeric_types.Int.Map.find_opt".
    (* container_types_intf.ml:317  include Stdlib.Map.S with type key := key and type 'a t := 'a t *)
    Parameter fold : forall {A Acc : Type}, (key -> A -> Acc -> M Acc) -> t A -> Acc -> M Acc.
    Extract Inlined Constant fold => "Numeric_types.Int.Map.fold".
    (* container_types_intf.ml:317  include Stdlib.Map.S with type key := key and type 'a t := 'a t *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Int.Map.is_empty".
    (* container_types_intf.ml:317  include Stdlib.Map.S with type key := key and type 'a t := 'a t *)
    Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
    Extract Inlined Constant of_list => "Numeric_types.Int.Map.of_list".
  End Map.
End Int.
Module Int8.
  (* numeric_types.mli:32  type t = private int *)
  Parameter t : Type.
  Extract Inlined Constant t => "Numeric_types.Int8.t".
  (* numeric_types.mli:34  val zero : t *)
  Parameter zero : t.
  Extract Inlined Constant zero => "Numeric_types.Int8.zero".
  (* numeric_types.mli:36  val one : t *)
  Parameter one : t.
  Extract Inlined Constant one => "Numeric_types.Int8.one".
  (* numeric_types.mli:38  val of_int : int -> t *)
  Parameter of_int : int -> M t.
  Extract Inlined Constant of_int => "Numeric_types.Int8.of_int".
  (* numeric_types.mli:44  val to_int : t -> int *)
  Parameter to_int : t -> M int.
  Extract Inlined Constant to_int => "Numeric_types.Int8.to_int".
  (* numeric_types.mli:46  val unsigned_to_int : t -> int *)
  Parameter unsigned_to_int : t -> M int.
  Extract Inlined Constant unsigned_to_int => "Numeric_types.Int8.unsigned_to_int".
  (* numeric_types.mli:48  val to_float : t -> float *)
  Parameter to_float : t -> M Stdlib_.float_.
  Extract Inlined Constant to_float => "Numeric_types.Int8.to_float".
  (* numeric_types.mli:50  val of_float : float -> t *)
  Parameter of_float : Stdlib_.float_ -> M t.
  Extract Inlined Constant of_float => "Numeric_types.Int8.of_float".
  Module T.
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Definition t : Type := Numeric_types.Int8.t.
    Extract Inlined Constant t => "Numeric_types.Int8.T.t".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int8.T.equal".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter hash : t -> M int.
    Extract Inlined Constant hash => "Numeric_types.Int8.T.hash".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int8.T.compare".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int8.T.print".
  End T.
  (* numeric_types.mli:52  include Container_types.S with type t := t *)
  Parameter equal : Numeric_types.Int8.T.t -> Numeric_types.Int8.T.t -> M bool.
  Extract Inlined Constant equal => "Numeric_types.Int8.equal".
  (* numeric_types.mli:52  include Container_types.S with type t := t *)
  Parameter hash : Numeric_types.Int8.T.t -> M int.
  Extract Inlined Constant hash => "Numeric_types.Int8.hash".
  (* numeric_types.mli:52  include Container_types.S with type t := t *)
  Parameter compare : Numeric_types.Int8.T.t -> Numeric_types.Int8.T.t -> M int.
  Extract Inlined Constant compare => "Numeric_types.Int8.compare".
  (* numeric_types.mli:52  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> Numeric_types.Int8.T.t -> M unit.
  Extract Inlined Constant print => "Numeric_types.Int8.print".
  Module Set_.
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Definition elt : Type := Numeric_types.Int8.t.
    Extract Inlined Constant elt => "Numeric_types.Int8.Set.elt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Numeric_types.Int8.Set.t".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Numeric_types.Int8.Set.empty".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Int8.Set.is_empty".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Int8.Set.mem".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Int8.Set.add".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Numeric_types.Int8.Set.singleton".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Numeric_types.Int8.Set.remove".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Numeric_types.Int8.Set.union".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Numeric_types.Int8.Set.union_sharing".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Numeric_types.Int8.Set.union_shared".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Numeric_types.Int8.Set.inter".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Numeric_types.Int8.Set.disjoint".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Numeric_types.Int8.Set.diff".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Numeric_types.Int8.Set.diff_sharing".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Numeric_types.Int8.Set.diff_shared".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int8.Set.compare".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int8.Set.equal".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Numeric_types.Int8.Set.subset".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Int8.Set.iter".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Numeric_types.Int8.Set.map".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Numeric_types.Int8.Set.fold".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Int8.Set.for_all".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Int8.Set.exists".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Numeric_types.Int8.Set.filter".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Numeric_types.Int8.Set.filter_map".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Numeric_types.Int8.Set.partition".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Int8.Set.cardinal".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Numeric_types.Int8.Set.elements".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Numeric_types.Int8.Set.min_elt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Numeric_types.Int8.Set.min_elt_opt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Numeric_types.Int8.Set.max_elt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Numeric_types.Int8.Set.max_elt_opt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Numeric_types.Int8.Set.choose".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Numeric_types.Int8.Set.choose_opt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Numeric_types.Int8.Set.split".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Numeric_types.Int8.Set.find".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Numeric_types.Int8.Set.of_list".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Numeric_types.Int8.Set.to_seq".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int8.Set.print".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Numeric_types.Int8.Set.to_string".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Numeric_types.Int8.Set.union_list".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Numeric_types.Int8.Set.get_singleton".
  End Set_.
  Module Map.
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Definition key : Type := Numeric_types.Int8.t.
    Extract Inlined Constant key => "Numeric_types.Int8.Map.key".
    Module Set_.
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Definition elt : Type := Numeric_types.Int8.t.
      Extract Inlined Constant elt => "Numeric_types.Int8.Map.Set.elt".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Definition t : Type := Numeric_types.Int8.Set_.t.
      Extract Inlined Constant t => "Numeric_types.Int8.Map.Set.t".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Numeric_types.Int8.Map.Set.empty".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Int8.Map.Set.is_empty".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Int8.Map.Set.mem".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Numeric_types.Int8.Map.Set.add".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Numeric_types.Int8.Map.Set.singleton".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Numeric_types.Int8.Map.Set.remove".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Numeric_types.Int8.Map.Set.union".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Numeric_types.Int8.Map.Set.union_sharing".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Numeric_types.Int8.Map.Set.union_shared".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Numeric_types.Int8.Map.Set.inter".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Numeric_types.Int8.Map.Set.disjoint".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Numeric_types.Int8.Map.Set.diff".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Numeric_types.Int8.Map.Set.diff_sharing".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Numeric_types.Int8.Map.Set.diff_shared".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Int8.Map.Set.compare".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Int8.Map.Set.equal".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Numeric_types.Int8.Map.Set.subset".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Int8.Map.Set.iter".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Numeric_types.Int8.Map.Set.map".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Int8.Map.Set.fold".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Int8.Map.Set.for_all".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Int8.Map.Set.exists".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Numeric_types.Int8.Map.Set.filter".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Numeric_types.Int8.Map.Set.filter_map".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Numeric_types.Int8.Map.Set.partition".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Int8.Map.Set.cardinal".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Numeric_types.Int8.Map.Set.elements".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Numeric_types.Int8.Map.Set.min_elt".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Numeric_types.Int8.Map.Set.min_elt_opt".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Numeric_types.Int8.Map.Set.max_elt".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Numeric_types.Int8.Map.Set.max_elt_opt".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Numeric_types.Int8.Map.Set.choose".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Numeric_types.Int8.Map.Set.choose_opt".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Numeric_types.Int8.Map.Set.split".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Numeric_types.Int8.Map.Set.find".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Numeric_types.Int8.Map.Set.of_list".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Numeric_types.Int8.Map.Set.to_seq".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Int8.Map.Set.print".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Numeric_types.Int8.Map.Set.to_string".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Numeric_types.Int8.Map.Set.union_list".
      (* numeric_types.mli:52  include Container_types.S with type t := t *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Numeric_types.Int8.Map.Set.get_singleton".
    End Set_.
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Numeric_types.Int8.Map.t".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter empty : forall {A : Type}, t A.
    Extract Inlined Constant empty => "Numeric_types.Int8.Map.empty".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Int8.Map.is_empty".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter mem : forall {A : Type}, key -> t A -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Int8.Map.mem".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    Extract Inlined Constant add => "Numeric_types.Int8.Map.add".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant update => "Numeric_types.Int8.Map.update".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter singleton : forall {A : Type}, key -> A -> M (t A).
    Extract Inlined Constant singleton => "Numeric_types.Int8.Map.singleton".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter remove : forall {A : Type}, key -> t A -> M (t A).
    Extract Inlined Constant remove => "Numeric_types.Int8.Map.remove".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
    Extract Inlined Constant merge => "Numeric_types.Int8.Map.merge".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union => "Numeric_types.Int8.Map.union".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_sharing => "Numeric_types.Int8.Map.union_sharing".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_shared => "Numeric_types.Int8.Map.union_shared".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total => "Numeric_types.Int8.Map.union_total".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total_shared => "Numeric_types.Int8.Map.union_total_shared".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_left_biased => "Numeric_types.Int8.Map.union_left_biased".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_right_biased => "Numeric_types.Int8.Map.union_right_biased".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant update_many => "Numeric_types.Int8.Map.update_many".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int8.Map.compare".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int8.Map.equal".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Int8.Map.iter".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold => "Numeric_types.Int8.Map.fold".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Int8.Map.for_all".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Int8.Map.exists".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
    Extract Inlined Constant filter => "Numeric_types.Int8.Map.filter".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
    Extract Inlined Constant filter_map => "Numeric_types.Int8.Map.filter_map".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant filter_map_sharing => "Numeric_types.Int8.Map.filter_map_sharing".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
    Extract Inlined Constant partition => "Numeric_types.Int8.Map.partition".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter cardinal : forall {A : Type}, t A -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Int8.Map.cardinal".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
    Extract Inlined Constant bindings => "Numeric_types.Int8.Map.bindings".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter min_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant min_binding => "Numeric_types.Int8.Map.min_binding".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant min_binding_opt => "Numeric_types.Int8.Map.min_binding_opt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter max_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant max_binding => "Numeric_types.Int8.Map.max_binding".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant max_binding_opt => "Numeric_types.Int8.Map.max_binding_opt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter choose : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant choose => "Numeric_types.Int8.Map.choose".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant choose_opt => "Numeric_types.Int8.Map.choose_opt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
    Extract Inlined Constant split => "Numeric_types.Int8.Map.split".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    Extract Inlined Constant find => "Numeric_types.Int8.Map.find".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    Extract Inlined Constant find_opt => "Numeric_types.Int8.Map.find_opt".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
    Extract Inlined Constant find_or_null => "Numeric_types.Int8.Map.find_or_null".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
    Extract Inlined Constant map => "Numeric_types.Int8.Map.map".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
    Extract Inlined Constant mapi => "Numeric_types.Int8.Map.mapi".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
    Extract Inlined Constant to_seq => "Numeric_types.Int8.Map.to_seq".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print_debug => "Numeric_types.Int8.Map.print_debug".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
    Extract Inlined Constant of_list => "Numeric_types.Int8.Map.of_list".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Numeric_types.Int8.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
    Extract Inlined Constant map_keys => "Numeric_types.Int8.Map.map_keys".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter keys : forall {A : Type}, t A -> M Numeric_types.Int8.Map.Set_.t.
    Extract Inlined Constant keys => "Numeric_types.Int8.Map.keys".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter data : forall {A : Type}, t A -> M (list A).
    Extract Inlined Constant data => "Numeric_types.Int8.Map.data".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Int8.Map.Set_.t -> M (t A).
    Extract Inlined Constant of_set => "Numeric_types.Int8.Map.of_set".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int8.Map.print".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
    Extract Inlined Constant subset_domain => "Numeric_types.Int8.Map.subset_domain".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
    Extract Inlined Constant diff_domains => "Numeric_types.Int8.Map.diff_domains".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
    Extract Inlined Constant inter => "Numeric_types.Int8.Map.inter".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff => "Numeric_types.Int8.Map.diff".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff_sharing => "Numeric_types.Int8.Map.diff_sharing".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant diff_shared => "Numeric_types.Int8.Map.diff_shared".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
    Extract Inlined Constant inter_domain_is_non_empty => "Numeric_types.Int8.Map.inter_domain_is_non_empty".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant get_singleton => "Numeric_types.Int8.Map.get_singleton".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant replace => "Numeric_types.Int8.Map.replace".
    (* numeric_types.mli:52  include Container_types.S with type t := t *)
    Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant map_sharing => "Numeric_types.Int8.Map.map_sharing".
  End Map.
End Int8.
Module Int16.
  (* numeric_types.mli:56  type t = private int *)
  Parameter t : Type.
  Extract Inlined Constant t => "Numeric_types.Int16.t".
  (* numeric_types.mli:58  val zero : t *)
  Parameter zero : t.
  Extract Inlined Constant zero => "Numeric_types.Int16.zero".
  (* numeric_types.mli:60  val one : t *)
  Parameter one : t.
  Extract Inlined Constant one => "Numeric_types.Int16.one".
  (* numeric_types.mli:62  val of_int : int -> t *)
  Parameter of_int : int -> M t.
  Extract Inlined Constant of_int => "Numeric_types.Int16.of_int".
  (* numeric_types.mli:68  val to_int : t -> int *)
  Parameter to_int : t -> M int.
  Extract Inlined Constant to_int => "Numeric_types.Int16.to_int".
  (* numeric_types.mli:70  val unsigned_to_int : t -> int *)
  Parameter unsigned_to_int : t -> M int.
  Extract Inlined Constant unsigned_to_int => "Numeric_types.Int16.unsigned_to_int".
  (* numeric_types.mli:72  val to_float : t -> float *)
  Parameter to_float : t -> M Stdlib_.float_.
  Extract Inlined Constant to_float => "Numeric_types.Int16.to_float".
  (* numeric_types.mli:74  val of_float : float -> t *)
  Parameter of_float : Stdlib_.float_ -> M t.
  Extract Inlined Constant of_float => "Numeric_types.Int16.of_float".
  Module T.
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Definition t : Type := Numeric_types.Int16.t.
    Extract Inlined Constant t => "Numeric_types.Int16.T.t".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int16.T.equal".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter hash : t -> M int.
    Extract Inlined Constant hash => "Numeric_types.Int16.T.hash".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int16.T.compare".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int16.T.print".
  End T.
  (* numeric_types.mli:76  include Container_types.S with type t := t *)
  Parameter equal : Numeric_types.Int16.T.t -> Numeric_types.Int16.T.t -> M bool.
  Extract Inlined Constant equal => "Numeric_types.Int16.equal".
  (* numeric_types.mli:76  include Container_types.S with type t := t *)
  Parameter hash : Numeric_types.Int16.T.t -> M int.
  Extract Inlined Constant hash => "Numeric_types.Int16.hash".
  (* numeric_types.mli:76  include Container_types.S with type t := t *)
  Parameter compare : Numeric_types.Int16.T.t -> Numeric_types.Int16.T.t -> M int.
  Extract Inlined Constant compare => "Numeric_types.Int16.compare".
  (* numeric_types.mli:76  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> Numeric_types.Int16.T.t -> M unit.
  Extract Inlined Constant print => "Numeric_types.Int16.print".
  Module Set_.
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Definition elt : Type := Numeric_types.Int16.t.
    Extract Inlined Constant elt => "Numeric_types.Int16.Set.elt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Numeric_types.Int16.Set.t".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Numeric_types.Int16.Set.empty".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Int16.Set.is_empty".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Int16.Set.mem".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Int16.Set.add".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Numeric_types.Int16.Set.singleton".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Numeric_types.Int16.Set.remove".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Numeric_types.Int16.Set.union".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Numeric_types.Int16.Set.union_sharing".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Numeric_types.Int16.Set.union_shared".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Numeric_types.Int16.Set.inter".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Numeric_types.Int16.Set.disjoint".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Numeric_types.Int16.Set.diff".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Numeric_types.Int16.Set.diff_sharing".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Numeric_types.Int16.Set.diff_shared".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int16.Set.compare".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int16.Set.equal".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Numeric_types.Int16.Set.subset".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Int16.Set.iter".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Numeric_types.Int16.Set.map".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Numeric_types.Int16.Set.fold".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Int16.Set.for_all".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Int16.Set.exists".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Numeric_types.Int16.Set.filter".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Numeric_types.Int16.Set.filter_map".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Numeric_types.Int16.Set.partition".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Int16.Set.cardinal".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Numeric_types.Int16.Set.elements".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Numeric_types.Int16.Set.min_elt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Numeric_types.Int16.Set.min_elt_opt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Numeric_types.Int16.Set.max_elt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Numeric_types.Int16.Set.max_elt_opt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Numeric_types.Int16.Set.choose".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Numeric_types.Int16.Set.choose_opt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Numeric_types.Int16.Set.split".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Numeric_types.Int16.Set.find".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Numeric_types.Int16.Set.of_list".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Numeric_types.Int16.Set.to_seq".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int16.Set.print".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Numeric_types.Int16.Set.to_string".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Numeric_types.Int16.Set.union_list".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Numeric_types.Int16.Set.get_singleton".
  End Set_.
  Module Map.
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Definition key : Type := Numeric_types.Int16.t.
    Extract Inlined Constant key => "Numeric_types.Int16.Map.key".
    Module Set_.
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Definition elt : Type := Numeric_types.Int16.t.
      Extract Inlined Constant elt => "Numeric_types.Int16.Map.Set.elt".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Definition t : Type := Numeric_types.Int16.Set_.t.
      Extract Inlined Constant t => "Numeric_types.Int16.Map.Set.t".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Numeric_types.Int16.Map.Set.empty".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Int16.Map.Set.is_empty".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Int16.Map.Set.mem".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Numeric_types.Int16.Map.Set.add".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Numeric_types.Int16.Map.Set.singleton".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Numeric_types.Int16.Map.Set.remove".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Numeric_types.Int16.Map.Set.union".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Numeric_types.Int16.Map.Set.union_sharing".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Numeric_types.Int16.Map.Set.union_shared".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Numeric_types.Int16.Map.Set.inter".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Numeric_types.Int16.Map.Set.disjoint".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Numeric_types.Int16.Map.Set.diff".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Numeric_types.Int16.Map.Set.diff_sharing".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Numeric_types.Int16.Map.Set.diff_shared".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Int16.Map.Set.compare".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Int16.Map.Set.equal".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Numeric_types.Int16.Map.Set.subset".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Int16.Map.Set.iter".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Numeric_types.Int16.Map.Set.map".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Int16.Map.Set.fold".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Int16.Map.Set.for_all".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Int16.Map.Set.exists".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Numeric_types.Int16.Map.Set.filter".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Numeric_types.Int16.Map.Set.filter_map".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Numeric_types.Int16.Map.Set.partition".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Int16.Map.Set.cardinal".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Numeric_types.Int16.Map.Set.elements".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Numeric_types.Int16.Map.Set.min_elt".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Numeric_types.Int16.Map.Set.min_elt_opt".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Numeric_types.Int16.Map.Set.max_elt".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Numeric_types.Int16.Map.Set.max_elt_opt".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Numeric_types.Int16.Map.Set.choose".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Numeric_types.Int16.Map.Set.choose_opt".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Numeric_types.Int16.Map.Set.split".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Numeric_types.Int16.Map.Set.find".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Numeric_types.Int16.Map.Set.of_list".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Numeric_types.Int16.Map.Set.to_seq".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Int16.Map.Set.print".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Numeric_types.Int16.Map.Set.to_string".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Numeric_types.Int16.Map.Set.union_list".
      (* numeric_types.mli:76  include Container_types.S with type t := t *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Numeric_types.Int16.Map.Set.get_singleton".
    End Set_.
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Numeric_types.Int16.Map.t".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter empty : forall {A : Type}, t A.
    Extract Inlined Constant empty => "Numeric_types.Int16.Map.empty".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Int16.Map.is_empty".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter mem : forall {A : Type}, key -> t A -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Int16.Map.mem".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    Extract Inlined Constant add => "Numeric_types.Int16.Map.add".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant update => "Numeric_types.Int16.Map.update".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter singleton : forall {A : Type}, key -> A -> M (t A).
    Extract Inlined Constant singleton => "Numeric_types.Int16.Map.singleton".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter remove : forall {A : Type}, key -> t A -> M (t A).
    Extract Inlined Constant remove => "Numeric_types.Int16.Map.remove".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
    Extract Inlined Constant merge => "Numeric_types.Int16.Map.merge".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union => "Numeric_types.Int16.Map.union".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_sharing => "Numeric_types.Int16.Map.union_sharing".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_shared => "Numeric_types.Int16.Map.union_shared".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total => "Numeric_types.Int16.Map.union_total".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total_shared => "Numeric_types.Int16.Map.union_total_shared".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_left_biased => "Numeric_types.Int16.Map.union_left_biased".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_right_biased => "Numeric_types.Int16.Map.union_right_biased".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant update_many => "Numeric_types.Int16.Map.update_many".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int16.Map.compare".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int16.Map.equal".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Int16.Map.iter".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold => "Numeric_types.Int16.Map.fold".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Int16.Map.for_all".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Int16.Map.exists".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
    Extract Inlined Constant filter => "Numeric_types.Int16.Map.filter".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
    Extract Inlined Constant filter_map => "Numeric_types.Int16.Map.filter_map".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant filter_map_sharing => "Numeric_types.Int16.Map.filter_map_sharing".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
    Extract Inlined Constant partition => "Numeric_types.Int16.Map.partition".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter cardinal : forall {A : Type}, t A -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Int16.Map.cardinal".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
    Extract Inlined Constant bindings => "Numeric_types.Int16.Map.bindings".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter min_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant min_binding => "Numeric_types.Int16.Map.min_binding".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant min_binding_opt => "Numeric_types.Int16.Map.min_binding_opt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter max_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant max_binding => "Numeric_types.Int16.Map.max_binding".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant max_binding_opt => "Numeric_types.Int16.Map.max_binding_opt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter choose : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant choose => "Numeric_types.Int16.Map.choose".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant choose_opt => "Numeric_types.Int16.Map.choose_opt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
    Extract Inlined Constant split => "Numeric_types.Int16.Map.split".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    Extract Inlined Constant find => "Numeric_types.Int16.Map.find".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    Extract Inlined Constant find_opt => "Numeric_types.Int16.Map.find_opt".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
    Extract Inlined Constant find_or_null => "Numeric_types.Int16.Map.find_or_null".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
    Extract Inlined Constant map => "Numeric_types.Int16.Map.map".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
    Extract Inlined Constant mapi => "Numeric_types.Int16.Map.mapi".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
    Extract Inlined Constant to_seq => "Numeric_types.Int16.Map.to_seq".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print_debug => "Numeric_types.Int16.Map.print_debug".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
    Extract Inlined Constant of_list => "Numeric_types.Int16.Map.of_list".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Numeric_types.Int16.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
    Extract Inlined Constant map_keys => "Numeric_types.Int16.Map.map_keys".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter keys : forall {A : Type}, t A -> M Numeric_types.Int16.Map.Set_.t.
    Extract Inlined Constant keys => "Numeric_types.Int16.Map.keys".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter data : forall {A : Type}, t A -> M (list A).
    Extract Inlined Constant data => "Numeric_types.Int16.Map.data".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Int16.Map.Set_.t -> M (t A).
    Extract Inlined Constant of_set => "Numeric_types.Int16.Map.of_set".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int16.Map.print".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
    Extract Inlined Constant subset_domain => "Numeric_types.Int16.Map.subset_domain".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
    Extract Inlined Constant diff_domains => "Numeric_types.Int16.Map.diff_domains".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
    Extract Inlined Constant inter => "Numeric_types.Int16.Map.inter".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff => "Numeric_types.Int16.Map.diff".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff_sharing => "Numeric_types.Int16.Map.diff_sharing".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant diff_shared => "Numeric_types.Int16.Map.diff_shared".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
    Extract Inlined Constant inter_domain_is_non_empty => "Numeric_types.Int16.Map.inter_domain_is_non_empty".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant get_singleton => "Numeric_types.Int16.Map.get_singleton".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant replace => "Numeric_types.Int16.Map.replace".
    (* numeric_types.mli:76  include Container_types.S with type t := t *)
    Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant map_sharing => "Numeric_types.Int16.Map.map_sharing".
  End Map.
End Int16.
Module Int32.
  (* stdlib/int32.mli  val zero : int32 *)
  Parameter zero : Stdlib_.int32.
  Extract Inlined Constant zero => "Numeric_types.Int32.zero".
  (* stdlib/int32.mli  val one : int32 *)
  Parameter one : Stdlib_.int32.
  Extract Inlined Constant one => "Numeric_types.Int32.one".
  (* stdlib/int32.mli  val minus_one : int32 *)
  Parameter minus_one : Stdlib_.int32.
  Extract Inlined Constant minus_one => "Numeric_types.Int32.minus_one".
  (* stdlib/int32.mli  val div : int32 -> int32 -> int32 *)
  Parameter div : Stdlib_.int32 -> Stdlib_.int32 -> M Stdlib_.int32.
  Extract Inlined Constant div => "Numeric_types.Int32.div".
  (* stdlib/int32.mli  val unsigned_div : int32 -> int32 -> int32 *)
  Parameter unsigned_div : Stdlib_.int32 -> Stdlib_.int32 -> M Stdlib_.int32.
  Extract Inlined Constant unsigned_div => "Numeric_types.Int32.unsigned_div".
  (* stdlib/int32.mli  val rem : int32 -> int32 -> int32 *)
  Parameter rem : Stdlib_.int32 -> Stdlib_.int32 -> M Stdlib_.int32.
  Extract Inlined Constant rem => "Numeric_types.Int32.rem".
  (* stdlib/int32.mli  val unsigned_rem : int32 -> int32 -> int32 *)
  Parameter unsigned_rem : Stdlib_.int32 -> Stdlib_.int32 -> M Stdlib_.int32.
  Extract Inlined Constant unsigned_rem => "Numeric_types.Int32.unsigned_rem".
  (* stdlib/int32.mli  val logand : int32 -> int32 -> int32 *)
  Parameter logand : Stdlib_.int32 -> Stdlib_.int32 -> M Stdlib_.int32.
  Extract Inlined Constant logand => "Numeric_types.Int32.logand".
  (* stdlib/int32.mli  val logor : int32 -> int32 -> int32 *)
  Parameter logor : Stdlib_.int32 -> Stdlib_.int32 -> M Stdlib_.int32.
  Extract Inlined Constant logor => "Numeric_types.Int32.logor".
  (* stdlib/int32.mli  val logxor : int32 -> int32 -> int32 *)
  Parameter logxor : Stdlib_.int32 -> Stdlib_.int32 -> M Stdlib_.int32.
  Extract Inlined Constant logxor => "Numeric_types.Int32.logxor".
  (* stdlib/int32.mli  val lognot : int32 -> int32 *)
  Parameter lognot : Stdlib_.int32 -> M Stdlib_.int32.
  Extract Inlined Constant lognot => "Numeric_types.Int32.lognot".
  (* stdlib/int32.mli  val shift_left : int32 -> int -> int32 *)
  Parameter shift_left : Stdlib_.int32 -> int -> M Stdlib_.int32.
  Extract Inlined Constant shift_left => "Numeric_types.Int32.shift_left".
  (* stdlib/int32.mli  val shift_right : int32 -> int -> int32 *)
  Parameter shift_right : Stdlib_.int32 -> int -> M Stdlib_.int32.
  Extract Inlined Constant shift_right => "Numeric_types.Int32.shift_right".
  (* stdlib/int32.mli  val shift_right_logical : int32 -> int -> int32 *)
  Parameter shift_right_logical : Stdlib_.int32 -> int -> M Stdlib_.int32.
  Extract Inlined Constant shift_right_logical => "Numeric_types.Int32.shift_right_logical".
  (* stdlib/int32.mli  val of_int : int -> int32 *)
  Parameter of_int : int -> M Stdlib_.int32.
  Extract Inlined Constant of_int => "Numeric_types.Int32.of_int".
  (* stdlib/int32.mli  val to_int : int32 -> int *)
  Parameter to_int : Stdlib_.int32 -> M int.
  Extract Inlined Constant to_int => "Numeric_types.Int32.to_int".
  (* stdlib/int32.mli  val of_float : float -> int32 *)
  Parameter of_float : Stdlib_.float_ -> M Stdlib_.int32.
  Extract Inlined Constant of_float => "Numeric_types.Int32.of_float".
  (* stdlib/int32.mli  val to_float : int32 -> float *)
  Parameter to_float : Stdlib_.int32 -> M Stdlib_.float_.
  Extract Inlined Constant to_float => "Numeric_types.Int32.to_float".
  (* stdlib/int32.mli  type t *)
  Definition t : Type := Stdlib_.int32.
  Extract Inlined Constant t => "Numeric_types.Int32.t".
  Module T.
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Definition t : Type := decl.Int32.t.
    Extract Inlined Constant t => "Numeric_types.Int32.T.t".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int32.T.equal".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter hash : t -> M int.
    Extract Inlined Constant hash => "Numeric_types.Int32.T.hash".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int32.T.compare".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int32.T.print".
  End T.
  (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
  Parameter equal : Numeric_types.Int32.T.t -> Numeric_types.Int32.T.t -> M bool.
  Extract Inlined Constant equal => "Numeric_types.Int32.equal".
  (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
  Parameter hash : Numeric_types.Int32.T.t -> M int.
  Extract Inlined Constant hash => "Numeric_types.Int32.hash".
  (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
  Parameter compare : Numeric_types.Int32.T.t -> Numeric_types.Int32.T.t -> M int.
  Extract Inlined Constant compare => "Numeric_types.Int32.compare".
  (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
  Parameter print : Format.formatter -> Numeric_types.Int32.T.t -> M unit.
  Extract Inlined Constant print => "Numeric_types.Int32.print".
  Module Set_.
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Definition elt : Type := decl.Int32.t.
    Extract Inlined Constant elt => "Numeric_types.Int32.Set.elt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Numeric_types.Int32.Set.t".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Numeric_types.Int32.Set.empty".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Int32.Set.is_empty".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Int32.Set.mem".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Int32.Set.add".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Numeric_types.Int32.Set.singleton".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Numeric_types.Int32.Set.remove".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Numeric_types.Int32.Set.union".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Numeric_types.Int32.Set.union_sharing".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Numeric_types.Int32.Set.union_shared".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Numeric_types.Int32.Set.inter".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Numeric_types.Int32.Set.disjoint".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Numeric_types.Int32.Set.diff".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Numeric_types.Int32.Set.diff_sharing".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Numeric_types.Int32.Set.diff_shared".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int32.Set.compare".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int32.Set.equal".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Numeric_types.Int32.Set.subset".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Int32.Set.iter".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Numeric_types.Int32.Set.map".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Numeric_types.Int32.Set.fold".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Int32.Set.for_all".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Int32.Set.exists".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Numeric_types.Int32.Set.filter".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Numeric_types.Int32.Set.filter_map".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Numeric_types.Int32.Set.partition".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Int32.Set.cardinal".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Numeric_types.Int32.Set.elements".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Numeric_types.Int32.Set.min_elt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Numeric_types.Int32.Set.min_elt_opt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Numeric_types.Int32.Set.max_elt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Numeric_types.Int32.Set.max_elt_opt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Numeric_types.Int32.Set.choose".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Numeric_types.Int32.Set.choose_opt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Numeric_types.Int32.Set.split".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Numeric_types.Int32.Set.find".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Numeric_types.Int32.Set.of_list".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Numeric_types.Int32.Set.to_seq".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int32.Set.print".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Numeric_types.Int32.Set.to_string".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Numeric_types.Int32.Set.union_list".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Numeric_types.Int32.Set.get_singleton".
  End Set_.
  Module Map.
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Definition key : Type := decl.Int32.t.
    Extract Inlined Constant key => "Numeric_types.Int32.Map.key".
    Module Set_.
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Definition elt : Type := decl.Int32.t.
      Extract Inlined Constant elt => "Numeric_types.Int32.Map.Set.elt".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Definition t : Type := Numeric_types.Int32.Set_.t.
      Extract Inlined Constant t => "Numeric_types.Int32.Map.Set.t".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Numeric_types.Int32.Map.Set.empty".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Int32.Map.Set.is_empty".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Int32.Map.Set.mem".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Numeric_types.Int32.Map.Set.add".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Numeric_types.Int32.Map.Set.singleton".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Numeric_types.Int32.Map.Set.remove".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Numeric_types.Int32.Map.Set.union".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Numeric_types.Int32.Map.Set.union_sharing".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Numeric_types.Int32.Map.Set.union_shared".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Numeric_types.Int32.Map.Set.inter".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Numeric_types.Int32.Map.Set.disjoint".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Numeric_types.Int32.Map.Set.diff".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Numeric_types.Int32.Map.Set.diff_sharing".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Numeric_types.Int32.Map.Set.diff_shared".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Int32.Map.Set.compare".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Int32.Map.Set.equal".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Numeric_types.Int32.Map.Set.subset".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Int32.Map.Set.iter".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Numeric_types.Int32.Map.Set.map".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Int32.Map.Set.fold".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Int32.Map.Set.for_all".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Int32.Map.Set.exists".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Numeric_types.Int32.Map.Set.filter".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Numeric_types.Int32.Map.Set.filter_map".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Numeric_types.Int32.Map.Set.partition".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Int32.Map.Set.cardinal".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Numeric_types.Int32.Map.Set.elements".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Numeric_types.Int32.Map.Set.min_elt".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Numeric_types.Int32.Map.Set.min_elt_opt".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Numeric_types.Int32.Map.Set.max_elt".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Numeric_types.Int32.Map.Set.max_elt_opt".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Numeric_types.Int32.Map.Set.choose".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Numeric_types.Int32.Map.Set.choose_opt".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Numeric_types.Int32.Map.Set.split".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Numeric_types.Int32.Map.Set.find".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Numeric_types.Int32.Map.Set.of_list".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Numeric_types.Int32.Map.Set.to_seq".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Int32.Map.Set.print".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Numeric_types.Int32.Map.Set.to_string".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Numeric_types.Int32.Map.Set.union_list".
      (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Numeric_types.Int32.Map.Set.get_singleton".
    End Set_.
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Numeric_types.Int32.Map.t".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter empty : forall {A : Type}, t A.
    Extract Inlined Constant empty => "Numeric_types.Int32.Map.empty".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Int32.Map.is_empty".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter mem : forall {A : Type}, key -> t A -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Int32.Map.mem".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    Extract Inlined Constant add => "Numeric_types.Int32.Map.add".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant update => "Numeric_types.Int32.Map.update".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter singleton : forall {A : Type}, key -> A -> M (t A).
    Extract Inlined Constant singleton => "Numeric_types.Int32.Map.singleton".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter remove : forall {A : Type}, key -> t A -> M (t A).
    Extract Inlined Constant remove => "Numeric_types.Int32.Map.remove".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
    Extract Inlined Constant merge => "Numeric_types.Int32.Map.merge".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union => "Numeric_types.Int32.Map.union".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_sharing => "Numeric_types.Int32.Map.union_sharing".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_shared => "Numeric_types.Int32.Map.union_shared".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total => "Numeric_types.Int32.Map.union_total".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total_shared => "Numeric_types.Int32.Map.union_total_shared".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_left_biased => "Numeric_types.Int32.Map.union_left_biased".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_right_biased => "Numeric_types.Int32.Map.union_right_biased".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant update_many => "Numeric_types.Int32.Map.update_many".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int32.Map.compare".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int32.Map.equal".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Int32.Map.iter".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold => "Numeric_types.Int32.Map.fold".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Int32.Map.for_all".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Int32.Map.exists".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
    Extract Inlined Constant filter => "Numeric_types.Int32.Map.filter".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
    Extract Inlined Constant filter_map => "Numeric_types.Int32.Map.filter_map".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant filter_map_sharing => "Numeric_types.Int32.Map.filter_map_sharing".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
    Extract Inlined Constant partition => "Numeric_types.Int32.Map.partition".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter cardinal : forall {A : Type}, t A -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Int32.Map.cardinal".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
    Extract Inlined Constant bindings => "Numeric_types.Int32.Map.bindings".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter min_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant min_binding => "Numeric_types.Int32.Map.min_binding".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant min_binding_opt => "Numeric_types.Int32.Map.min_binding_opt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter max_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant max_binding => "Numeric_types.Int32.Map.max_binding".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant max_binding_opt => "Numeric_types.Int32.Map.max_binding_opt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter choose : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant choose => "Numeric_types.Int32.Map.choose".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant choose_opt => "Numeric_types.Int32.Map.choose_opt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
    Extract Inlined Constant split => "Numeric_types.Int32.Map.split".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    Extract Inlined Constant find => "Numeric_types.Int32.Map.find".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    Extract Inlined Constant find_opt => "Numeric_types.Int32.Map.find_opt".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
    Extract Inlined Constant find_or_null => "Numeric_types.Int32.Map.find_or_null".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
    Extract Inlined Constant map => "Numeric_types.Int32.Map.map".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
    Extract Inlined Constant mapi => "Numeric_types.Int32.Map.mapi".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
    Extract Inlined Constant to_seq => "Numeric_types.Int32.Map.to_seq".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print_debug => "Numeric_types.Int32.Map.print_debug".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
    Extract Inlined Constant of_list => "Numeric_types.Int32.Map.of_list".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Numeric_types.Int32.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
    Extract Inlined Constant map_keys => "Numeric_types.Int32.Map.map_keys".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter keys : forall {A : Type}, t A -> M Numeric_types.Int32.Map.Set_.t.
    Extract Inlined Constant keys => "Numeric_types.Int32.Map.keys".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter data : forall {A : Type}, t A -> M (list A).
    Extract Inlined Constant data => "Numeric_types.Int32.Map.data".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Int32.Map.Set_.t -> M (t A).
    Extract Inlined Constant of_set => "Numeric_types.Int32.Map.of_set".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int32.Map.print".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
    Extract Inlined Constant subset_domain => "Numeric_types.Int32.Map.subset_domain".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
    Extract Inlined Constant diff_domains => "Numeric_types.Int32.Map.diff_domains".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
    Extract Inlined Constant inter => "Numeric_types.Int32.Map.inter".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff => "Numeric_types.Int32.Map.diff".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff_sharing => "Numeric_types.Int32.Map.diff_sharing".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant diff_shared => "Numeric_types.Int32.Map.diff_shared".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
    Extract Inlined Constant inter_domain_is_non_empty => "Numeric_types.Int32.Map.inter_domain_is_non_empty".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant get_singleton => "Numeric_types.Int32.Map.get_singleton".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant replace => "Numeric_types.Int32.Map.replace".
    (* numeric_types.mli:84  include Container_types.S with type t := Int32.t *)
    Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant map_sharing => "Numeric_types.Int32.Map.map_sharing".
  End Map.
End Int32.
Module Int64.
  (* stdlib/int64.mli  val zero : int64 *)
  Parameter zero : Stdlib_.int64.
  Extract Inlined Constant zero => "Numeric_types.Int64.zero".
  (* stdlib/int64.mli  val one : int64 *)
  Parameter one : Stdlib_.int64.
  Extract Inlined Constant one => "Numeric_types.Int64.one".
  (* stdlib/int64.mli  val minus_one : int64 *)
  Parameter minus_one : Stdlib_.int64.
  Extract Inlined Constant minus_one => "Numeric_types.Int64.minus_one".
  (* stdlib/int64.mli  val add : int64 -> int64 -> int64 *)
  Parameter add : Stdlib_.int64 -> Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant add => "Numeric_types.Int64.add".
  (* stdlib/int64.mli  val mul : int64 -> int64 -> int64 *)
  Parameter mul : Stdlib_.int64 -> Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant mul => "Numeric_types.Int64.mul".
  (* stdlib/int64.mli  val div : int64 -> int64 -> int64 *)
  Parameter div : Stdlib_.int64 -> Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant div => "Numeric_types.Int64.div".
  (* stdlib/int64.mli  val unsigned_div : int64 -> int64 -> int64 *)
  Parameter unsigned_div : Stdlib_.int64 -> Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant unsigned_div => "Numeric_types.Int64.unsigned_div".
  (* stdlib/int64.mli  val rem : int64 -> int64 -> int64 *)
  Parameter rem : Stdlib_.int64 -> Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant rem => "Numeric_types.Int64.rem".
  (* stdlib/int64.mli  val unsigned_rem : int64 -> int64 -> int64 *)
  Parameter unsigned_rem : Stdlib_.int64 -> Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant unsigned_rem => "Numeric_types.Int64.unsigned_rem".
  (* stdlib/int64.mli  val logand : int64 -> int64 -> int64 *)
  Parameter logand : Stdlib_.int64 -> Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant logand => "Numeric_types.Int64.logand".
  (* stdlib/int64.mli  val logor : int64 -> int64 -> int64 *)
  Parameter logor : Stdlib_.int64 -> Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant logor => "Numeric_types.Int64.logor".
  (* stdlib/int64.mli  val logxor : int64 -> int64 -> int64 *)
  Parameter logxor : Stdlib_.int64 -> Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant logxor => "Numeric_types.Int64.logxor".
  (* stdlib/int64.mli  val lognot : int64 -> int64 *)
  Parameter lognot : Stdlib_.int64 -> M Stdlib_.int64.
  Extract Inlined Constant lognot => "Numeric_types.Int64.lognot".
  (* stdlib/int64.mli  val shift_left : int64 -> int -> int64 *)
  Parameter shift_left : Stdlib_.int64 -> int -> M Stdlib_.int64.
  Extract Inlined Constant shift_left => "Numeric_types.Int64.shift_left".
  (* stdlib/int64.mli  val shift_right : int64 -> int -> int64 *)
  Parameter shift_right : Stdlib_.int64 -> int -> M Stdlib_.int64.
  Extract Inlined Constant shift_right => "Numeric_types.Int64.shift_right".
  (* stdlib/int64.mli  val shift_right_logical : int64 -> int -> int64 *)
  Parameter shift_right_logical : Stdlib_.int64 -> int -> M Stdlib_.int64.
  Extract Inlined Constant shift_right_logical => "Numeric_types.Int64.shift_right_logical".
  (* stdlib/int64.mli  val of_int : int -> int64 *)
  Parameter of_int : int -> M Stdlib_.int64.
  Extract Inlined Constant of_int => "Numeric_types.Int64.of_int".
  (* stdlib/int64.mli  val to_int : int64 -> int *)
  Parameter to_int : Stdlib_.int64 -> M int.
  Extract Inlined Constant to_int => "Numeric_types.Int64.to_int".
  (* stdlib/int64.mli  val of_float : float -> int64 *)
  Parameter of_float : Stdlib_.float_ -> M Stdlib_.int64.
  Extract Inlined Constant of_float => "Numeric_types.Int64.of_float".
  (* stdlib/int64.mli  val to_float : int64 -> float *)
  Parameter to_float : Stdlib_.int64 -> M Stdlib_.float_.
  Extract Inlined Constant to_float => "Numeric_types.Int64.to_float".
  (* stdlib/int64.mli  val of_int32 : int32 -> int64 *)
  Parameter of_int32 : Stdlib_.int32 -> M Stdlib_.int64.
  Extract Inlined Constant of_int32 => "Numeric_types.Int64.of_int32".
  (* stdlib/int64.mli  val to_int32 : int64 -> int32 *)
  Parameter to_int32 : Stdlib_.int64 -> M Stdlib_.int32.
  Extract Inlined Constant to_int32 => "Numeric_types.Int64.to_int32".
  (* stdlib/int64.mli  type t *)
  Definition t : Type := Stdlib_.int64.
  Extract Inlined Constant t => "Numeric_types.Int64.t".
  Module T.
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Definition t : Type := decl.Int64.t.
    Extract Inlined Constant t => "Numeric_types.Int64.T.t".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int64.T.equal".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter hash : t -> M int.
    Extract Inlined Constant hash => "Numeric_types.Int64.T.hash".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int64.T.compare".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int64.T.print".
  End T.
  (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
  Parameter equal : Numeric_types.Int64.T.t -> Numeric_types.Int64.T.t -> M bool.
  Extract Inlined Constant equal => "Numeric_types.Int64.equal".
  (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
  Parameter hash : Numeric_types.Int64.T.t -> M int.
  Extract Inlined Constant hash => "Numeric_types.Int64.hash".
  (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
  Parameter compare : Numeric_types.Int64.T.t -> Numeric_types.Int64.T.t -> M int.
  Extract Inlined Constant compare => "Numeric_types.Int64.compare".
  (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
  Parameter print : Format.formatter -> Numeric_types.Int64.T.t -> M unit.
  Extract Inlined Constant print => "Numeric_types.Int64.print".
  Module Set_.
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Definition elt : Type := decl.Int64.t.
    Extract Inlined Constant elt => "Numeric_types.Int64.Set.elt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Numeric_types.Int64.Set.t".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Numeric_types.Int64.Set.empty".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Int64.Set.is_empty".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Int64.Set.mem".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Int64.Set.add".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Numeric_types.Int64.Set.singleton".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Numeric_types.Int64.Set.remove".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Numeric_types.Int64.Set.union".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Numeric_types.Int64.Set.union_sharing".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Numeric_types.Int64.Set.union_shared".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Numeric_types.Int64.Set.inter".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Numeric_types.Int64.Set.disjoint".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Numeric_types.Int64.Set.diff".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Numeric_types.Int64.Set.diff_sharing".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Numeric_types.Int64.Set.diff_shared".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int64.Set.compare".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int64.Set.equal".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Numeric_types.Int64.Set.subset".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Int64.Set.iter".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Numeric_types.Int64.Set.map".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Numeric_types.Int64.Set.fold".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Int64.Set.for_all".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Int64.Set.exists".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Numeric_types.Int64.Set.filter".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Numeric_types.Int64.Set.filter_map".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Numeric_types.Int64.Set.partition".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Int64.Set.cardinal".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Numeric_types.Int64.Set.elements".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Numeric_types.Int64.Set.min_elt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Numeric_types.Int64.Set.min_elt_opt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Numeric_types.Int64.Set.max_elt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Numeric_types.Int64.Set.max_elt_opt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Numeric_types.Int64.Set.choose".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Numeric_types.Int64.Set.choose_opt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Numeric_types.Int64.Set.split".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Numeric_types.Int64.Set.find".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Numeric_types.Int64.Set.of_list".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Numeric_types.Int64.Set.to_seq".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int64.Set.print".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Numeric_types.Int64.Set.to_string".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Numeric_types.Int64.Set.union_list".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Numeric_types.Int64.Set.get_singleton".
  End Set_.
  Module Map.
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Definition key : Type := decl.Int64.t.
    Extract Inlined Constant key => "Numeric_types.Int64.Map.key".
    Module Set_.
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Definition elt : Type := decl.Int64.t.
      Extract Inlined Constant elt => "Numeric_types.Int64.Map.Set.elt".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Definition t : Type := Numeric_types.Int64.Set_.t.
      Extract Inlined Constant t => "Numeric_types.Int64.Map.Set.t".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Numeric_types.Int64.Map.Set.empty".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Int64.Map.Set.is_empty".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Int64.Map.Set.mem".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Numeric_types.Int64.Map.Set.add".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Numeric_types.Int64.Map.Set.singleton".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Numeric_types.Int64.Map.Set.remove".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Numeric_types.Int64.Map.Set.union".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Numeric_types.Int64.Map.Set.union_sharing".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Numeric_types.Int64.Map.Set.union_shared".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Numeric_types.Int64.Map.Set.inter".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Numeric_types.Int64.Map.Set.disjoint".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Numeric_types.Int64.Map.Set.diff".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Numeric_types.Int64.Map.Set.diff_sharing".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Numeric_types.Int64.Map.Set.diff_shared".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Int64.Map.Set.compare".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Int64.Map.Set.equal".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Numeric_types.Int64.Map.Set.subset".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Int64.Map.Set.iter".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Numeric_types.Int64.Map.Set.map".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Int64.Map.Set.fold".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Int64.Map.Set.for_all".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Int64.Map.Set.exists".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Numeric_types.Int64.Map.Set.filter".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Numeric_types.Int64.Map.Set.filter_map".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Numeric_types.Int64.Map.Set.partition".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Int64.Map.Set.cardinal".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Numeric_types.Int64.Map.Set.elements".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Numeric_types.Int64.Map.Set.min_elt".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Numeric_types.Int64.Map.Set.min_elt_opt".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Numeric_types.Int64.Map.Set.max_elt".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Numeric_types.Int64.Map.Set.max_elt_opt".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Numeric_types.Int64.Map.Set.choose".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Numeric_types.Int64.Map.Set.choose_opt".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Numeric_types.Int64.Map.Set.split".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Numeric_types.Int64.Map.Set.find".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Numeric_types.Int64.Map.Set.of_list".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Numeric_types.Int64.Map.Set.to_seq".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Int64.Map.Set.print".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Numeric_types.Int64.Map.Set.to_string".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Numeric_types.Int64.Map.Set.union_list".
      (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Numeric_types.Int64.Map.Set.get_singleton".
    End Set_.
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Numeric_types.Int64.Map.t".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter empty : forall {A : Type}, t A.
    Extract Inlined Constant empty => "Numeric_types.Int64.Map.empty".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Int64.Map.is_empty".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter mem : forall {A : Type}, key -> t A -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Int64.Map.mem".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    Extract Inlined Constant add => "Numeric_types.Int64.Map.add".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant update => "Numeric_types.Int64.Map.update".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter singleton : forall {A : Type}, key -> A -> M (t A).
    Extract Inlined Constant singleton => "Numeric_types.Int64.Map.singleton".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter remove : forall {A : Type}, key -> t A -> M (t A).
    Extract Inlined Constant remove => "Numeric_types.Int64.Map.remove".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
    Extract Inlined Constant merge => "Numeric_types.Int64.Map.merge".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union => "Numeric_types.Int64.Map.union".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_sharing => "Numeric_types.Int64.Map.union_sharing".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_shared => "Numeric_types.Int64.Map.union_shared".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total => "Numeric_types.Int64.Map.union_total".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total_shared => "Numeric_types.Int64.Map.union_total_shared".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_left_biased => "Numeric_types.Int64.Map.union_left_biased".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_right_biased => "Numeric_types.Int64.Map.union_right_biased".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant update_many => "Numeric_types.Int64.Map.update_many".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
    Extract Inlined Constant compare => "Numeric_types.Int64.Map.compare".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Int64.Map.equal".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Int64.Map.iter".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold => "Numeric_types.Int64.Map.fold".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Int64.Map.for_all".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Int64.Map.exists".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
    Extract Inlined Constant filter => "Numeric_types.Int64.Map.filter".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
    Extract Inlined Constant filter_map => "Numeric_types.Int64.Map.filter_map".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant filter_map_sharing => "Numeric_types.Int64.Map.filter_map_sharing".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
    Extract Inlined Constant partition => "Numeric_types.Int64.Map.partition".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter cardinal : forall {A : Type}, t A -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Int64.Map.cardinal".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
    Extract Inlined Constant bindings => "Numeric_types.Int64.Map.bindings".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter min_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant min_binding => "Numeric_types.Int64.Map.min_binding".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant min_binding_opt => "Numeric_types.Int64.Map.min_binding_opt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter max_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant max_binding => "Numeric_types.Int64.Map.max_binding".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant max_binding_opt => "Numeric_types.Int64.Map.max_binding_opt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter choose : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant choose => "Numeric_types.Int64.Map.choose".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant choose_opt => "Numeric_types.Int64.Map.choose_opt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
    Extract Inlined Constant split => "Numeric_types.Int64.Map.split".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    Extract Inlined Constant find => "Numeric_types.Int64.Map.find".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    Extract Inlined Constant find_opt => "Numeric_types.Int64.Map.find_opt".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
    Extract Inlined Constant find_or_null => "Numeric_types.Int64.Map.find_or_null".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
    Extract Inlined Constant map => "Numeric_types.Int64.Map.map".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
    Extract Inlined Constant mapi => "Numeric_types.Int64.Map.mapi".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
    Extract Inlined Constant to_seq => "Numeric_types.Int64.Map.to_seq".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print_debug => "Numeric_types.Int64.Map.print_debug".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
    Extract Inlined Constant of_list => "Numeric_types.Int64.Map.of_list".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Numeric_types.Int64.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
    Extract Inlined Constant map_keys => "Numeric_types.Int64.Map.map_keys".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter keys : forall {A : Type}, t A -> M Numeric_types.Int64.Map.Set_.t.
    Extract Inlined Constant keys => "Numeric_types.Int64.Map.keys".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter data : forall {A : Type}, t A -> M (list A).
    Extract Inlined Constant data => "Numeric_types.Int64.Map.data".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Int64.Map.Set_.t -> M (t A).
    Extract Inlined Constant of_set => "Numeric_types.Int64.Map.of_set".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print => "Numeric_types.Int64.Map.print".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
    Extract Inlined Constant subset_domain => "Numeric_types.Int64.Map.subset_domain".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
    Extract Inlined Constant diff_domains => "Numeric_types.Int64.Map.diff_domains".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
    Extract Inlined Constant inter => "Numeric_types.Int64.Map.inter".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff => "Numeric_types.Int64.Map.diff".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff_sharing => "Numeric_types.Int64.Map.diff_sharing".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant diff_shared => "Numeric_types.Int64.Map.diff_shared".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
    Extract Inlined Constant inter_domain_is_non_empty => "Numeric_types.Int64.Map.inter_domain_is_non_empty".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant get_singleton => "Numeric_types.Int64.Map.get_singleton".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant replace => "Numeric_types.Int64.Map.replace".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant map_sharing => "Numeric_types.Int64.Map.map_sharing".
  End Map.
End Int64.
(* The module type Numeric_types.Float_by_bit_pattern: all that it names. No directive: in a functor, Rocq prints what the parameter has by its name here. *)
Module Type Float_by_bit_pattern_.
  (* numeric_types.mli:139  type bits *)
  Parameter bits : Type.
  (* container_types_intf.ml:297  type t *)
  Parameter t : Type.
  Module T.
    (* container_types_intf.ml:299  module T : Thing with type t = t *)
    Definition t : Type := Numeric_types.Float_by_bit_pattern_.t.
    (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
    Parameter equal : t -> t -> M bool.
    (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
    Parameter hash : t -> M int.
    (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
    Parameter compare : t -> t -> M int.
    (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
  End T.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter equal : Numeric_types.Float_by_bit_pattern_.T.t -> Numeric_types.Float_by_bit_pattern_.T.t -> M bool.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter hash : Numeric_types.Float_by_bit_pattern_.T.t -> M int.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter compare : Numeric_types.Float_by_bit_pattern_.T.t -> Numeric_types.Float_by_bit_pattern_.T.t -> M int.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter print : Format.formatter -> Numeric_types.Float_by_bit_pattern_.T.t -> M unit.
  Module Set_.
    (* container_types_intf.ml:303  module Set : Set with type elt = t *)
    Definition elt : Type := Numeric_types.Float_by_bit_pattern_.t.
    (* container_types_intf.ml:38  type t *)
    Parameter t : Type.
    (* container_types_intf.ml:40  val empty : t *)
    Parameter empty : t.
    (* container_types_intf.ml:42  val is_empty : t -> bool *)
    Parameter is_empty : t -> M bool.
    (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
    Parameter mem : elt -> t -> M bool.
    (* container_types_intf.ml:46  val add : elt -> t -> t *)
    Parameter add : elt -> t -> M t.
    (* container_types_intf.ml:48  val singleton : elt -> t *)
    Parameter singleton : elt -> M t.
    (* container_types_intf.ml:50  val remove : elt -> t -> t *)
    Parameter remove : elt -> t -> M t.
    (* container_types_intf.ml:52  val union : t -> t -> t *)
    Parameter union : t -> t -> M t.
    (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
    Parameter union_sharing : t -> t -> M t.
    (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
    Parameter union_shared : t -> t -> M t.
    (* container_types_intf.ml:62  val inter : t -> t -> t *)
    Parameter inter : t -> t -> M t.
    (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
    Parameter disjoint : t -> t -> M bool.
    (* container_types_intf.ml:66  val diff : t -> t -> t *)
    Parameter diff : t -> t -> M t.
    (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
    Parameter diff_sharing : t -> t -> M t.
    (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
    Parameter diff_shared : t -> t -> M t.
    (* container_types_intf.ml:76  val compare : t -> t -> int *)
    Parameter compare : t -> t -> M int.
    (* container_types_intf.ml:78  val equal : t -> t -> bool *)
    Parameter equal : t -> t -> M bool.
    (* container_types_intf.ml:80  val subset : t -> t -> bool *)
    Parameter subset : t -> t -> M bool.
    (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    (* container_types_intf.ml:98  val cardinal : t -> int *)
    Parameter cardinal : t -> M int.
    (* container_types_intf.ml:100  val elements : t -> elt list *)
    Parameter elements : t -> M (list elt).
    (* container_types_intf.ml:102  val min_elt : t -> elt *)
    Parameter min_elt : t -> M elt.
    (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
    Parameter min_elt_opt : t -> M (option elt).
    (* container_types_intf.ml:106  val max_elt : t -> elt *)
    Parameter max_elt : t -> M elt.
    (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
    Parameter max_elt_opt : t -> M (option elt).
    (* container_types_intf.ml:110  val choose : t -> elt *)
    Parameter choose : t -> M elt.
    (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
    Parameter choose_opt : t -> M (option elt).
    (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    (* container_types_intf.ml:116  val find : elt -> t -> elt *)
    Parameter find : elt -> t -> M elt.
    (* container_types_intf.ml:118  val of_list : elt list -> t *)
    Parameter of_list : list elt -> M t.
    (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
    Parameter to_seq : t -> Seq.t elt.
    (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
    (* container_types_intf.ml:124  val to_string : t -> string *)
    Parameter to_string : t -> M string.
    (* container_types_intf.ml:126  val union_list : t list -> t *)
    Parameter union_list : list t -> M t.
    (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
    Parameter get_singleton : t -> M (option elt).
  End Set_.
  Module Map.
    (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
    Definition key : Type := Numeric_types.Float_by_bit_pattern_.t.
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Numeric_types.Float_by_bit_pattern_.t.
      (* container_types_intf.ml:38  type t *)
      Definition t : Type := Numeric_types.Float_by_bit_pattern_.Set_.t.
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
    End Set_.
    (* container_types_intf.ml:136  type +!'a t *)
    Parameter t : Type -> Type.
    (* container_types_intf.ml:138  val empty : 'a t *)
    Parameter empty : forall {A : Type}, t A.
    (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
    Parameter mem : forall {A : Type}, key -> t A -> M bool.
    (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
    Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
    (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
    Parameter singleton : forall {A : Type}, key -> A -> M (t A).
    (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
    Parameter remove : forall {A : Type}, key -> t A -> M (t A).
    (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
    Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
    (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
    Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
    Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
    Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
    (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
    Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
    (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
    (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
    Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
    (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
    Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
    (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
    Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
    (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
    Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
    Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
    Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
    (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
    Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
    (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
    Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
    (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
    Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
    (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
    Parameter cardinal : forall {A : Type}, t A -> M int.
    (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
    Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
    (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
    Parameter min_binding : forall {A : Type}, t A -> M (key * A).
    (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
    Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
    Parameter max_binding : forall {A : Type}, t A -> M (key * A).
    (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
    Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
    Parameter choose : forall {A : Type}, t A -> M (key * A).
    (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
    Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
    (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
    Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
    (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
    Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
    (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
    Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
    (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
    Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
    (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
    Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
    (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
    Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
    Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
    (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
    Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
    (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
    Parameter keys : forall {A : Type}, t A -> M Numeric_types.Float_by_bit_pattern_.Map.Set_.t.
    (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
    Parameter data : forall {A : Type}, t A -> M (list A).
    (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
    Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Float_by_bit_pattern_.Map.Set_.t -> M (t A).
    (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
    Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
    (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
    Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
    (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
    Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
    (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
    Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
    (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
    Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
    (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
    Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
    (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
    Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
  End Map.
  (* numeric_types.mli:145  val create : float -> t *)
  Parameter create : Stdlib_.float_ -> M t.
  (* numeric_types.mli:147  val of_bits : bits -> t *)
  Parameter of_bits : bits -> M t.
  (* numeric_types.mli:149  val to_bits : t -> bits *)
  Parameter to_bits : t -> M bits.
  (* numeric_types.mli:151  val of_int64 : int64 -> t *)
  Parameter of_int64 : Stdlib_.int64 -> M t.
  (* numeric_types.mli:153  val of_string : string -> t *)
  Parameter of_string : string -> M t.
  (* numeric_types.mli:155  val to_float : t -> float *)
  Parameter to_float : t -> M Stdlib_.float_.
  (* numeric_types.mli:157  val one : t *)
  Parameter one : t.
  (* numeric_types.mli:159  val zero : t *)
  Parameter zero : t.
  (* numeric_types.mli:161  val minus_one : t *)
  Parameter minus_one : t.
  (* numeric_types.mli:163  val is_either_zero : t -> bool *)
  Parameter is_either_zero : t -> M bool.
  (* numeric_types.mli:165  val is_any_nan : t -> bool *)
  Parameter is_any_nan : t -> M bool.
  Module IEEE_semantics.
    (* numeric_types.mli:167  module IEEE_semantics : IEEE_semantics with type t = t *)
    Definition t : Type := Numeric_types.Float_by_bit_pattern_.t.
    (* numeric_types.mli:110  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    (* numeric_types.mli:112  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    (* numeric_types.mli:114  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    (* numeric_types.mli:116  val div : t -> t -> t *)
    Parameter div : t -> t -> M t.
    (* numeric_types.mli:118  val mod_ : t -> t -> t *)
    Parameter mod_ : t -> t -> M t.
    (* numeric_types.mli:120  val neg : t -> t *)
    Parameter neg : t -> M t.
    (* numeric_types.mli:122  val abs : t -> t *)
    Parameter abs : t -> M t.
    (* numeric_types.mli:124  val compare : t -> t -> int *)
    Parameter compare : t -> t -> M int.
    (* numeric_types.mli:126  val equal : t -> t -> bool *)
    Parameter equal : t -> t -> M bool.
  End IEEE_semantics.
  Module Pair.
    (* numeric_types.mli:169  module Pair : Container_types.S with type t = t * t *)
    Definition t : Type := (Numeric_types.Float_by_bit_pattern_.t * Numeric_types.Float_by_bit_pattern_.t).
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Numeric_types.Float_by_bit_pattern_.Pair.t.
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Numeric_types.Float_by_bit_pattern_.Pair.T.t -> Numeric_types.Float_by_bit_pattern_.Pair.T.t -> M bool.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Numeric_types.Float_by_bit_pattern_.Pair.T.t -> M int.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Numeric_types.Float_by_bit_pattern_.Pair.T.t -> Numeric_types.Float_by_bit_pattern_.Pair.T.t -> M int.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Numeric_types.Float_by_bit_pattern_.Pair.T.t -> M unit.
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Numeric_types.Float_by_bit_pattern_.Pair.t.
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Numeric_types.Float_by_bit_pattern_.Pair.t.
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Numeric_types.Float_by_bit_pattern_.Pair.t.
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Numeric_types.Float_by_bit_pattern_.Pair.Set_.t.
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Numeric_types.Float_by_bit_pattern_.Pair.Map.Set_.t.
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Float_by_bit_pattern_.Pair.Map.Set_.t -> M (t A).
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
    End Map.
  End Pair.
  (* numeric_types.mli:171  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
  Parameter cross_product : Numeric_types.Float_by_bit_pattern_.Set_.t -> Numeric_types.Float_by_bit_pattern_.Set_.t -> M Numeric_types.Float_by_bit_pattern_.Pair.Set_.t.
End Float_by_bit_pattern_.
Module Float_by_bit_pattern.
  (* numeric_types.mli:174  module Float_by_bit_pattern : Float_by_bit_pattern with type bits = int64 *)
  Definition bits : Type := Stdlib_.int64.
  Extract Inlined Constant bits => "Numeric_types.Float_by_bit_pattern.bits".
  (* container_types_intf.ml:297  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.t".
  Module T.
    (* container_types_intf.ml:299  module T : Thing with type t = t *)
    Definition t : Type := Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.T.t".
    (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.T.equal".
    (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
    Parameter hash : t -> M int.
    Extract Inlined Constant hash => "Numeric_types.Float_by_bit_pattern.T.hash".
    (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.T.compare".
    (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.T.print".
  End T.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter equal : Numeric_types.Float_by_bit_pattern.T.t -> Numeric_types.Float_by_bit_pattern.T.t -> M bool.
  Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.equal".
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter hash : Numeric_types.Float_by_bit_pattern.T.t -> M int.
  Extract Inlined Constant hash => "Numeric_types.Float_by_bit_pattern.hash".
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter compare : Numeric_types.Float_by_bit_pattern.T.t -> Numeric_types.Float_by_bit_pattern.T.t -> M int.
  Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.compare".
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter print : Format.formatter -> Numeric_types.Float_by_bit_pattern.T.t -> M unit.
  Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.print".
  Module Set_.
    (* container_types_intf.ml:303  module Set : Set with type elt = t *)
    Definition elt : Type := Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant elt => "Numeric_types.Float_by_bit_pattern.Set.elt".
    (* container_types_intf.ml:38  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.Set.t".
    (* container_types_intf.ml:40  val empty : t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Numeric_types.Float_by_bit_pattern.Set.empty".
    (* container_types_intf.ml:42  val is_empty : t -> bool *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Float_by_bit_pattern.Set.is_empty".
    (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Float_by_bit_pattern.Set.mem".
    (* container_types_intf.ml:46  val add : elt -> t -> t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Float_by_bit_pattern.Set.add".
    (* container_types_intf.ml:48  val singleton : elt -> t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Numeric_types.Float_by_bit_pattern.Set.singleton".
    (* container_types_intf.ml:50  val remove : elt -> t -> t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Numeric_types.Float_by_bit_pattern.Set.remove".
    (* container_types_intf.ml:52  val union : t -> t -> t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Numeric_types.Float_by_bit_pattern.Set.union".
    (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Numeric_types.Float_by_bit_pattern.Set.union_sharing".
    (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Numeric_types.Float_by_bit_pattern.Set.union_shared".
    (* container_types_intf.ml:62  val inter : t -> t -> t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Numeric_types.Float_by_bit_pattern.Set.inter".
    (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Numeric_types.Float_by_bit_pattern.Set.disjoint".
    (* container_types_intf.ml:66  val diff : t -> t -> t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Numeric_types.Float_by_bit_pattern.Set.diff".
    (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Numeric_types.Float_by_bit_pattern.Set.diff_sharing".
    (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Numeric_types.Float_by_bit_pattern.Set.diff_shared".
    (* container_types_intf.ml:76  val compare : t -> t -> int *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.Set.compare".
    (* container_types_intf.ml:78  val equal : t -> t -> bool *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.Set.equal".
    (* container_types_intf.ml:80  val subset : t -> t -> bool *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Numeric_types.Float_by_bit_pattern.Set.subset".
    (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Float_by_bit_pattern.Set.iter".
    (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Numeric_types.Float_by_bit_pattern.Set.map".
    (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Numeric_types.Float_by_bit_pattern.Set.fold".
    (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Float_by_bit_pattern.Set.for_all".
    (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Float_by_bit_pattern.Set.exists".
    (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Numeric_types.Float_by_bit_pattern.Set.filter".
    (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Numeric_types.Float_by_bit_pattern.Set.filter_map".
    (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Numeric_types.Float_by_bit_pattern.Set.partition".
    (* container_types_intf.ml:98  val cardinal : t -> int *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Float_by_bit_pattern.Set.cardinal".
    (* container_types_intf.ml:100  val elements : t -> elt list *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Numeric_types.Float_by_bit_pattern.Set.elements".
    (* container_types_intf.ml:102  val min_elt : t -> elt *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Numeric_types.Float_by_bit_pattern.Set.min_elt".
    (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Numeric_types.Float_by_bit_pattern.Set.min_elt_opt".
    (* container_types_intf.ml:106  val max_elt : t -> elt *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Numeric_types.Float_by_bit_pattern.Set.max_elt".
    (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Numeric_types.Float_by_bit_pattern.Set.max_elt_opt".
    (* container_types_intf.ml:110  val choose : t -> elt *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Numeric_types.Float_by_bit_pattern.Set.choose".
    (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Numeric_types.Float_by_bit_pattern.Set.choose_opt".
    (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Numeric_types.Float_by_bit_pattern.Set.split".
    (* container_types_intf.ml:116  val find : elt -> t -> elt *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Numeric_types.Float_by_bit_pattern.Set.find".
    (* container_types_intf.ml:118  val of_list : elt list -> t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Numeric_types.Float_by_bit_pattern.Set.of_list".
    (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Numeric_types.Float_by_bit_pattern.Set.to_seq".
    (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.Set.print".
    (* container_types_intf.ml:124  val to_string : t -> string *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Numeric_types.Float_by_bit_pattern.Set.to_string".
    (* container_types_intf.ml:126  val union_list : t list -> t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Numeric_types.Float_by_bit_pattern.Set.union_list".
    (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Numeric_types.Float_by_bit_pattern.Set.get_singleton".
  End Set_.
  Module Map.
    (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
    Definition key : Type := Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant key => "Numeric_types.Float_by_bit_pattern.Map.key".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Numeric_types.Float_by_bit_pattern.t.
      Extract Inlined Constant elt => "Numeric_types.Float_by_bit_pattern.Map.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Definition t : Type := Numeric_types.Float_by_bit_pattern.Set_.t.
      Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.Map.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Numeric_types.Float_by_bit_pattern.Map.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Float_by_bit_pattern.Map.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Float_by_bit_pattern.Map.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Numeric_types.Float_by_bit_pattern.Map.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Numeric_types.Float_by_bit_pattern.Map.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Numeric_types.Float_by_bit_pattern.Map.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Numeric_types.Float_by_bit_pattern.Map.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Numeric_types.Float_by_bit_pattern.Map.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Numeric_types.Float_by_bit_pattern.Map.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Numeric_types.Float_by_bit_pattern.Map.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Numeric_types.Float_by_bit_pattern.Map.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Numeric_types.Float_by_bit_pattern.Map.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Numeric_types.Float_by_bit_pattern.Map.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Numeric_types.Float_by_bit_pattern.Map.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.Map.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.Map.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Numeric_types.Float_by_bit_pattern.Map.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Float_by_bit_pattern.Map.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Numeric_types.Float_by_bit_pattern.Map.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Float_by_bit_pattern.Map.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Float_by_bit_pattern.Map.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Float_by_bit_pattern.Map.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Numeric_types.Float_by_bit_pattern.Map.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Numeric_types.Float_by_bit_pattern.Map.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Numeric_types.Float_by_bit_pattern.Map.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Float_by_bit_pattern.Map.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Numeric_types.Float_by_bit_pattern.Map.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Numeric_types.Float_by_bit_pattern.Map.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Numeric_types.Float_by_bit_pattern.Map.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Numeric_types.Float_by_bit_pattern.Map.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Numeric_types.Float_by_bit_pattern.Map.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Numeric_types.Float_by_bit_pattern.Map.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Numeric_types.Float_by_bit_pattern.Map.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Numeric_types.Float_by_bit_pattern.Map.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Numeric_types.Float_by_bit_pattern.Map.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Numeric_types.Float_by_bit_pattern.Map.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Numeric_types.Float_by_bit_pattern.Map.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.Map.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Numeric_types.Float_by_bit_pattern.Map.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Numeric_types.Float_by_bit_pattern.Map.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Numeric_types.Float_by_bit_pattern.Map.Set.get_singleton".
    End Set_.
    (* container_types_intf.ml:136  type +!'a t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Numeric_types.Float_by_bit_pattern.Map.t".
    (* container_types_intf.ml:138  val empty : 'a t *)
    Parameter empty : forall {A : Type}, t A.
    Extract Inlined Constant empty => "Numeric_types.Float_by_bit_pattern.Map.empty".
    (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Float_by_bit_pattern.Map.is_empty".
    (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
    Parameter mem : forall {A : Type}, key -> t A -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Float_by_bit_pattern.Map.mem".
    (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    Extract Inlined Constant add => "Numeric_types.Float_by_bit_pattern.Map.add".
    (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
    Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant update => "Numeric_types.Float_by_bit_pattern.Map.update".
    (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
    Parameter singleton : forall {A : Type}, key -> A -> M (t A).
    Extract Inlined Constant singleton => "Numeric_types.Float_by_bit_pattern.Map.singleton".
    (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
    Parameter remove : forall {A : Type}, key -> t A -> M (t A).
    Extract Inlined Constant remove => "Numeric_types.Float_by_bit_pattern.Map.remove".
    (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
    Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
    Extract Inlined Constant merge => "Numeric_types.Float_by_bit_pattern.Map.merge".
    (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union => "Numeric_types.Float_by_bit_pattern.Map.union".
    (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_sharing => "Numeric_types.Float_by_bit_pattern.Map.union_sharing".
    (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_shared => "Numeric_types.Float_by_bit_pattern.Map.union_shared".
    (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
    Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total => "Numeric_types.Float_by_bit_pattern.Map.union_total".
    (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
    Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total_shared => "Numeric_types.Float_by_bit_pattern.Map.union_total_shared".
    (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
    Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_left_biased => "Numeric_types.Float_by_bit_pattern.Map.union_left_biased".
    (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
    Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_right_biased => "Numeric_types.Float_by_bit_pattern.Map.union_right_biased".
    (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant update_many => "Numeric_types.Float_by_bit_pattern.Map.update_many".
    (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
    Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.Map.compare".
    (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
    Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.Map.equal".
    (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
    Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Float_by_bit_pattern.Map.iter".
    (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold => "Numeric_types.Float_by_bit_pattern.Map.fold".
    (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
    Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Float_by_bit_pattern.Map.for_all".
    (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
    Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Float_by_bit_pattern.Map.exists".
    (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
    Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
    Extract Inlined Constant filter => "Numeric_types.Float_by_bit_pattern.Map.filter".
    (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
    Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
    Extract Inlined Constant filter_map => "Numeric_types.Float_by_bit_pattern.Map.filter_map".
    (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
    Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant filter_map_sharing => "Numeric_types.Float_by_bit_pattern.Map.filter_map_sharing".
    (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
    Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
    Extract Inlined Constant partition => "Numeric_types.Float_by_bit_pattern.Map.partition".
    (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
    Parameter cardinal : forall {A : Type}, t A -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Float_by_bit_pattern.Map.cardinal".
    (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
    Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
    Extract Inlined Constant bindings => "Numeric_types.Float_by_bit_pattern.Map.bindings".
    (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
    Parameter min_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant min_binding => "Numeric_types.Float_by_bit_pattern.Map.min_binding".
    (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
    Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant min_binding_opt => "Numeric_types.Float_by_bit_pattern.Map.min_binding_opt".
    (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
    Parameter max_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant max_binding => "Numeric_types.Float_by_bit_pattern.Map.max_binding".
    (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
    Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant max_binding_opt => "Numeric_types.Float_by_bit_pattern.Map.max_binding_opt".
    (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
    Parameter choose : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant choose => "Numeric_types.Float_by_bit_pattern.Map.choose".
    (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
    Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant choose_opt => "Numeric_types.Float_by_bit_pattern.Map.choose_opt".
    (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
    Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
    Extract Inlined Constant split => "Numeric_types.Float_by_bit_pattern.Map.split".
    (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    Extract Inlined Constant find => "Numeric_types.Float_by_bit_pattern.Map.find".
    (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    Extract Inlined Constant find_opt => "Numeric_types.Float_by_bit_pattern.Map.find_opt".
    (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
    Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
    Extract Inlined Constant find_or_null => "Numeric_types.Float_by_bit_pattern.Map.find_or_null".
    (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
    Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
    Extract Inlined Constant map => "Numeric_types.Float_by_bit_pattern.Map.map".
    (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
    Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
    Extract Inlined Constant mapi => "Numeric_types.Float_by_bit_pattern.Map.mapi".
    (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
    Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
    Extract Inlined Constant to_seq => "Numeric_types.Float_by_bit_pattern.Map.to_seq".
    (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
    Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print_debug => "Numeric_types.Float_by_bit_pattern.Map.print_debug".
    (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
    Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
    Extract Inlined Constant of_list => "Numeric_types.Float_by_bit_pattern.Map.of_list".
    (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Numeric_types.Float_by_bit_pattern.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
    (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
    Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
    Extract Inlined Constant map_keys => "Numeric_types.Float_by_bit_pattern.Map.map_keys".
    (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
    Parameter keys : forall {A : Type}, t A -> M Numeric_types.Float_by_bit_pattern.Map.Set_.t.
    Extract Inlined Constant keys => "Numeric_types.Float_by_bit_pattern.Map.keys".
    (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
    Parameter data : forall {A : Type}, t A -> M (list A).
    Extract Inlined Constant data => "Numeric_types.Float_by_bit_pattern.Map.data".
    (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
    Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Float_by_bit_pattern.Map.Set_.t -> M (t A).
    Extract Inlined Constant of_set => "Numeric_types.Float_by_bit_pattern.Map.of_set".
    (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.Map.print".
    (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
    Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
    Extract Inlined Constant subset_domain => "Numeric_types.Float_by_bit_pattern.Map.subset_domain".
    (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
    Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
    Extract Inlined Constant diff_domains => "Numeric_types.Float_by_bit_pattern.Map.diff_domains".
    (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
    Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
    Extract Inlined Constant inter => "Numeric_types.Float_by_bit_pattern.Map.inter".
    (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff => "Numeric_types.Float_by_bit_pattern.Map.diff".
    (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff_sharing => "Numeric_types.Float_by_bit_pattern.Map.diff_sharing".
    (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant diff_shared => "Numeric_types.Float_by_bit_pattern.Map.diff_shared".
    (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
    Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
    Extract Inlined Constant inter_domain_is_non_empty => "Numeric_types.Float_by_bit_pattern.Map.inter_domain_is_non_empty".
    (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
    Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant get_singleton => "Numeric_types.Float_by_bit_pattern.Map.get_singleton".
    (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
    Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant replace => "Numeric_types.Float_by_bit_pattern.Map.replace".
    (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
    Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant map_sharing => "Numeric_types.Float_by_bit_pattern.Map.map_sharing".
  End Map.
  (* numeric_types.mli:145  val create : float -> t *)
  Parameter create : Stdlib_.float_ -> M t.
  Extract Inlined Constant create => "Numeric_types.Float_by_bit_pattern.create".
  (* numeric_types.mli:147  val of_bits : bits -> t *)
  Parameter of_bits : bits -> M t.
  Extract Inlined Constant of_bits => "Numeric_types.Float_by_bit_pattern.of_bits".
  (* numeric_types.mli:149  val to_bits : t -> bits *)
  Parameter to_bits : t -> M bits.
  Extract Inlined Constant to_bits => "Numeric_types.Float_by_bit_pattern.to_bits".
  (* numeric_types.mli:151  val of_int64 : int64 -> t *)
  Parameter of_int64 : Stdlib_.int64 -> M t.
  Extract Inlined Constant of_int64 => "Numeric_types.Float_by_bit_pattern.of_int64".
  (* numeric_types.mli:153  val of_string : string -> t *)
  Parameter of_string : string -> M t.
  Extract Inlined Constant of_string => "Numeric_types.Float_by_bit_pattern.of_string".
  (* numeric_types.mli:155  val to_float : t -> float *)
  Parameter to_float : t -> M Stdlib_.float_.
  Extract Inlined Constant to_float => "Numeric_types.Float_by_bit_pattern.to_float".
  (* numeric_types.mli:157  val one : t *)
  Parameter one : t.
  Extract Inlined Constant one => "Numeric_types.Float_by_bit_pattern.one".
  (* numeric_types.mli:159  val zero : t *)
  Parameter zero : t.
  Extract Inlined Constant zero => "Numeric_types.Float_by_bit_pattern.zero".
  (* numeric_types.mli:161  val minus_one : t *)
  Parameter minus_one : t.
  Extract Inlined Constant minus_one => "Numeric_types.Float_by_bit_pattern.minus_one".
  (* numeric_types.mli:163  val is_either_zero : t -> bool *)
  Parameter is_either_zero : t -> M bool.
  Extract Inlined Constant is_either_zero => "Numeric_types.Float_by_bit_pattern.is_either_zero".
  (* numeric_types.mli:165  val is_any_nan : t -> bool *)
  Parameter is_any_nan : t -> M bool.
  Extract Inlined Constant is_any_nan => "Numeric_types.Float_by_bit_pattern.is_any_nan".
  Module IEEE_semantics.
    (* numeric_types.mli:167  module IEEE_semantics : IEEE_semantics with type t = t *)
    Definition t : Type := Numeric_types.Float_by_bit_pattern.t.
    Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.t".
    (* numeric_types.mli:110  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.add".
    (* numeric_types.mli:112  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.sub".
    (* numeric_types.mli:114  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.mul".
    (* numeric_types.mli:116  val div : t -> t -> t *)
    Parameter div : t -> t -> M t.
    Extract Inlined Constant div => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.div".
    (* numeric_types.mli:118  val mod_ : t -> t -> t *)
    Parameter mod_ : t -> t -> M t.
    Extract Inlined Constant mod_ => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.mod_".
    (* numeric_types.mli:120  val neg : t -> t *)
    Parameter neg : t -> M t.
    Extract Inlined Constant neg => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.neg".
    (* numeric_types.mli:122  val abs : t -> t *)
    Parameter abs : t -> M t.
    Extract Inlined Constant abs => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.abs".
    (* numeric_types.mli:124  val compare : t -> t -> int *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.compare".
    (* numeric_types.mli:126  val equal : t -> t -> bool *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.IEEE_semantics.equal".
  End IEEE_semantics.
  Module Pair.
    (* numeric_types.mli:169  module Pair : Container_types.S with type t = t * t *)
    Definition t : Type := (Numeric_types.Float_by_bit_pattern.t * Numeric_types.Float_by_bit_pattern.t).
    Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.Pair.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Numeric_types.Float_by_bit_pattern.Pair.t.
      Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.Pair.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.Pair.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Numeric_types.Float_by_bit_pattern.Pair.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.Pair.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.Pair.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Numeric_types.Float_by_bit_pattern.Pair.T.t -> Numeric_types.Float_by_bit_pattern.Pair.T.t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.Pair.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Numeric_types.Float_by_bit_pattern.Pair.T.t -> M int.
    Extract Inlined Constant hash => "Numeric_types.Float_by_bit_pattern.Pair.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Numeric_types.Float_by_bit_pattern.Pair.T.t -> Numeric_types.Float_by_bit_pattern.Pair.T.t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.Pair.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Numeric_types.Float_by_bit_pattern.Pair.T.t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.Pair.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Numeric_types.Float_by_bit_pattern.Pair.t.
      Extract Inlined Constant elt => "Numeric_types.Float_by_bit_pattern.Pair.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.Pair.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Numeric_types.Float_by_bit_pattern.Pair.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Float_by_bit_pattern.Pair.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Float_by_bit_pattern.Pair.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Numeric_types.Float_by_bit_pattern.Pair.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Numeric_types.Float_by_bit_pattern.Pair.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Numeric_types.Float_by_bit_pattern.Pair.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Numeric_types.Float_by_bit_pattern.Pair.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Numeric_types.Float_by_bit_pattern.Pair.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Numeric_types.Float_by_bit_pattern.Pair.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Numeric_types.Float_by_bit_pattern.Pair.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Numeric_types.Float_by_bit_pattern.Pair.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Numeric_types.Float_by_bit_pattern.Pair.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Numeric_types.Float_by_bit_pattern.Pair.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Numeric_types.Float_by_bit_pattern.Pair.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.Pair.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.Pair.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Numeric_types.Float_by_bit_pattern.Pair.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Float_by_bit_pattern.Pair.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Numeric_types.Float_by_bit_pattern.Pair.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Float_by_bit_pattern.Pair.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Float_by_bit_pattern.Pair.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Float_by_bit_pattern.Pair.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Numeric_types.Float_by_bit_pattern.Pair.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Numeric_types.Float_by_bit_pattern.Pair.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Numeric_types.Float_by_bit_pattern.Pair.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Float_by_bit_pattern.Pair.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Numeric_types.Float_by_bit_pattern.Pair.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Numeric_types.Float_by_bit_pattern.Pair.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Numeric_types.Float_by_bit_pattern.Pair.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Numeric_types.Float_by_bit_pattern.Pair.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Numeric_types.Float_by_bit_pattern.Pair.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Numeric_types.Float_by_bit_pattern.Pair.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Numeric_types.Float_by_bit_pattern.Pair.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Numeric_types.Float_by_bit_pattern.Pair.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Numeric_types.Float_by_bit_pattern.Pair.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Numeric_types.Float_by_bit_pattern.Pair.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Numeric_types.Float_by_bit_pattern.Pair.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.Pair.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Numeric_types.Float_by_bit_pattern.Pair.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Numeric_types.Float_by_bit_pattern.Pair.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Numeric_types.Float_by_bit_pattern.Pair.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Numeric_types.Float_by_bit_pattern.Pair.t.
      Extract Inlined Constant key => "Numeric_types.Float_by_bit_pattern.Pair.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Numeric_types.Float_by_bit_pattern.Pair.t.
        Extract Inlined Constant elt => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Numeric_types.Float_by_bit_pattern.Pair.Set_.t.
        Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Numeric_types.Float_by_bit_pattern.Pair.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Numeric_types.Float_by_bit_pattern.Pair.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Numeric_types.Float_by_bit_pattern.Pair.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Float_by_bit_pattern.Pair.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Float_by_bit_pattern.Pair.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Numeric_types.Float_by_bit_pattern.Pair.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Numeric_types.Float_by_bit_pattern.Pair.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Numeric_types.Float_by_bit_pattern.Pair.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Numeric_types.Float_by_bit_pattern.Pair.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Numeric_types.Float_by_bit_pattern.Pair.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Numeric_types.Float_by_bit_pattern.Pair.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Numeric_types.Float_by_bit_pattern.Pair.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Numeric_types.Float_by_bit_pattern.Pair.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Numeric_types.Float_by_bit_pattern.Pair.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Numeric_types.Float_by_bit_pattern.Pair.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Numeric_types.Float_by_bit_pattern.Pair.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Numeric_types.Float_by_bit_pattern.Pair.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Numeric_types.Float_by_bit_pattern.Pair.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.Pair.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.Pair.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Float_by_bit_pattern.Pair.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Numeric_types.Float_by_bit_pattern.Pair.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Float_by_bit_pattern.Pair.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Float_by_bit_pattern.Pair.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Numeric_types.Float_by_bit_pattern.Pair.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Numeric_types.Float_by_bit_pattern.Pair.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Numeric_types.Float_by_bit_pattern.Pair.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Numeric_types.Float_by_bit_pattern.Pair.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Float_by_bit_pattern.Pair.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Numeric_types.Float_by_bit_pattern.Pair.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Numeric_types.Float_by_bit_pattern.Pair.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Numeric_types.Float_by_bit_pattern.Pair.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Numeric_types.Float_by_bit_pattern.Pair.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Numeric_types.Float_by_bit_pattern.Pair.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Numeric_types.Float_by_bit_pattern.Pair.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Numeric_types.Float_by_bit_pattern.Pair.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Numeric_types.Float_by_bit_pattern.Pair.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Numeric_types.Float_by_bit_pattern.Pair.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Numeric_types.Float_by_bit_pattern.Pair.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Numeric_types.Float_by_bit_pattern.Pair.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Numeric_types.Float_by_bit_pattern.Pair.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Numeric_types.Float_by_bit_pattern.Pair.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Numeric_types.Float_by_bit_pattern.Pair.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Numeric_types.Float_by_bit_pattern.Pair.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Numeric_types.Float_by_bit_pattern.Pair.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Numeric_types.Float_by_bit_pattern.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Numeric_types.Float_by_bit_pattern.Pair.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Numeric_types.Float_by_bit_pattern.Pair.Map.Set_.t.
      Extract Inlined Constant keys => "Numeric_types.Float_by_bit_pattern.Pair.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Numeric_types.Float_by_bit_pattern.Pair.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Float_by_bit_pattern.Pair.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Numeric_types.Float_by_bit_pattern.Pair.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Numeric_types.Float_by_bit_pattern.Pair.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Numeric_types.Float_by_bit_pattern.Pair.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Numeric_types.Float_by_bit_pattern.Pair.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Numeric_types.Float_by_bit_pattern.Pair.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Numeric_types.Float_by_bit_pattern.Pair.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Numeric_types.Float_by_bit_pattern.Pair.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Numeric_types.Float_by_bit_pattern.Pair.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Numeric_types.Float_by_bit_pattern.Pair.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Numeric_types.Float_by_bit_pattern.Pair.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Numeric_types.Float_by_bit_pattern.Pair.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Numeric_types.Float_by_bit_pattern.Pair.Map.map_sharing".
    End Map.
  End Pair.
  (* numeric_types.mli:171  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
  Parameter cross_product : Numeric_types.Float_by_bit_pattern.Set_.t -> Numeric_types.Float_by_bit_pattern.Set_.t -> M Numeric_types.Float_by_bit_pattern.Pair.Set_.t.
  Extract Inlined Constant cross_product => "Numeric_types.Float_by_bit_pattern.cross_product".
End Float_by_bit_pattern.
Module Float32_by_bit_pattern.
  (* numeric_types.mli:176  module Float32_by_bit_pattern : Float_by_bit_pattern with type bits = int32 *)
  Definition bits : Type := Stdlib_.int32.
  Extract Inlined Constant bits => "Numeric_types.Float32_by_bit_pattern.bits".
  (* container_types_intf.ml:297  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.t".
  Module T.
    (* container_types_intf.ml:299  module T : Thing with type t = t *)
    Definition t : Type := Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.T.t".
    (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.T.equal".
    (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
    Parameter hash : t -> M int.
    Extract Inlined Constant hash => "Numeric_types.Float32_by_bit_pattern.T.hash".
    (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.T.compare".
    (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.T.print".
  End T.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter equal : Numeric_types.Float32_by_bit_pattern.T.t -> Numeric_types.Float32_by_bit_pattern.T.t -> M bool.
  Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.equal".
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter hash : Numeric_types.Float32_by_bit_pattern.T.t -> M int.
  Extract Inlined Constant hash => "Numeric_types.Float32_by_bit_pattern.hash".
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter compare : Numeric_types.Float32_by_bit_pattern.T.t -> Numeric_types.Float32_by_bit_pattern.T.t -> M int.
  Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.compare".
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter print : Format.formatter -> Numeric_types.Float32_by_bit_pattern.T.t -> M unit.
  Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.print".
  Module Set_.
    (* container_types_intf.ml:303  module Set : Set with type elt = t *)
    Definition elt : Type := Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant elt => "Numeric_types.Float32_by_bit_pattern.Set.elt".
    (* container_types_intf.ml:38  type t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.Set.t".
    (* container_types_intf.ml:40  val empty : t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Numeric_types.Float32_by_bit_pattern.Set.empty".
    (* container_types_intf.ml:42  val is_empty : t -> bool *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Float32_by_bit_pattern.Set.is_empty".
    (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Float32_by_bit_pattern.Set.mem".
    (* container_types_intf.ml:46  val add : elt -> t -> t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Float32_by_bit_pattern.Set.add".
    (* container_types_intf.ml:48  val singleton : elt -> t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Numeric_types.Float32_by_bit_pattern.Set.singleton".
    (* container_types_intf.ml:50  val remove : elt -> t -> t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Numeric_types.Float32_by_bit_pattern.Set.remove".
    (* container_types_intf.ml:52  val union : t -> t -> t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Numeric_types.Float32_by_bit_pattern.Set.union".
    (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Numeric_types.Float32_by_bit_pattern.Set.union_sharing".
    (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Numeric_types.Float32_by_bit_pattern.Set.union_shared".
    (* container_types_intf.ml:62  val inter : t -> t -> t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Numeric_types.Float32_by_bit_pattern.Set.inter".
    (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Numeric_types.Float32_by_bit_pattern.Set.disjoint".
    (* container_types_intf.ml:66  val diff : t -> t -> t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Numeric_types.Float32_by_bit_pattern.Set.diff".
    (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Numeric_types.Float32_by_bit_pattern.Set.diff_sharing".
    (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Numeric_types.Float32_by_bit_pattern.Set.diff_shared".
    (* container_types_intf.ml:76  val compare : t -> t -> int *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.Set.compare".
    (* container_types_intf.ml:78  val equal : t -> t -> bool *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.Set.equal".
    (* container_types_intf.ml:80  val subset : t -> t -> bool *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Numeric_types.Float32_by_bit_pattern.Set.subset".
    (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Float32_by_bit_pattern.Set.iter".
    (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Numeric_types.Float32_by_bit_pattern.Set.map".
    (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Numeric_types.Float32_by_bit_pattern.Set.fold".
    (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Float32_by_bit_pattern.Set.for_all".
    (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Float32_by_bit_pattern.Set.exists".
    (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Numeric_types.Float32_by_bit_pattern.Set.filter".
    (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Numeric_types.Float32_by_bit_pattern.Set.filter_map".
    (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Numeric_types.Float32_by_bit_pattern.Set.partition".
    (* container_types_intf.ml:98  val cardinal : t -> int *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Float32_by_bit_pattern.Set.cardinal".
    (* container_types_intf.ml:100  val elements : t -> elt list *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Numeric_types.Float32_by_bit_pattern.Set.elements".
    (* container_types_intf.ml:102  val min_elt : t -> elt *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Numeric_types.Float32_by_bit_pattern.Set.min_elt".
    (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Numeric_types.Float32_by_bit_pattern.Set.min_elt_opt".
    (* container_types_intf.ml:106  val max_elt : t -> elt *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Numeric_types.Float32_by_bit_pattern.Set.max_elt".
    (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Numeric_types.Float32_by_bit_pattern.Set.max_elt_opt".
    (* container_types_intf.ml:110  val choose : t -> elt *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Numeric_types.Float32_by_bit_pattern.Set.choose".
    (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Numeric_types.Float32_by_bit_pattern.Set.choose_opt".
    (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Numeric_types.Float32_by_bit_pattern.Set.split".
    (* container_types_intf.ml:116  val find : elt -> t -> elt *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Numeric_types.Float32_by_bit_pattern.Set.find".
    (* container_types_intf.ml:118  val of_list : elt list -> t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Numeric_types.Float32_by_bit_pattern.Set.of_list".
    (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Numeric_types.Float32_by_bit_pattern.Set.to_seq".
    (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.Set.print".
    (* container_types_intf.ml:124  val to_string : t -> string *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Numeric_types.Float32_by_bit_pattern.Set.to_string".
    (* container_types_intf.ml:126  val union_list : t list -> t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Numeric_types.Float32_by_bit_pattern.Set.union_list".
    (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Numeric_types.Float32_by_bit_pattern.Set.get_singleton".
  End Set_.
  Module Map.
    (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
    Definition key : Type := Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant key => "Numeric_types.Float32_by_bit_pattern.Map.key".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Numeric_types.Float32_by_bit_pattern.t.
      Extract Inlined Constant elt => "Numeric_types.Float32_by_bit_pattern.Map.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Definition t : Type := Numeric_types.Float32_by_bit_pattern.Set_.t.
      Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.Map.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Numeric_types.Float32_by_bit_pattern.Map.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Float32_by_bit_pattern.Map.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Float32_by_bit_pattern.Map.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Numeric_types.Float32_by_bit_pattern.Map.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Numeric_types.Float32_by_bit_pattern.Map.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Numeric_types.Float32_by_bit_pattern.Map.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Numeric_types.Float32_by_bit_pattern.Map.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Numeric_types.Float32_by_bit_pattern.Map.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Numeric_types.Float32_by_bit_pattern.Map.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Numeric_types.Float32_by_bit_pattern.Map.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Numeric_types.Float32_by_bit_pattern.Map.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Numeric_types.Float32_by_bit_pattern.Map.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Numeric_types.Float32_by_bit_pattern.Map.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Numeric_types.Float32_by_bit_pattern.Map.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.Map.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.Map.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Numeric_types.Float32_by_bit_pattern.Map.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Float32_by_bit_pattern.Map.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Numeric_types.Float32_by_bit_pattern.Map.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Float32_by_bit_pattern.Map.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Float32_by_bit_pattern.Map.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Float32_by_bit_pattern.Map.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Numeric_types.Float32_by_bit_pattern.Map.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Numeric_types.Float32_by_bit_pattern.Map.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Numeric_types.Float32_by_bit_pattern.Map.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Float32_by_bit_pattern.Map.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Numeric_types.Float32_by_bit_pattern.Map.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Numeric_types.Float32_by_bit_pattern.Map.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Numeric_types.Float32_by_bit_pattern.Map.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Numeric_types.Float32_by_bit_pattern.Map.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Numeric_types.Float32_by_bit_pattern.Map.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Numeric_types.Float32_by_bit_pattern.Map.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Numeric_types.Float32_by_bit_pattern.Map.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Numeric_types.Float32_by_bit_pattern.Map.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Numeric_types.Float32_by_bit_pattern.Map.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Numeric_types.Float32_by_bit_pattern.Map.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Numeric_types.Float32_by_bit_pattern.Map.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.Map.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Numeric_types.Float32_by_bit_pattern.Map.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Numeric_types.Float32_by_bit_pattern.Map.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Numeric_types.Float32_by_bit_pattern.Map.Set.get_singleton".
    End Set_.
    (* container_types_intf.ml:136  type +!'a t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Numeric_types.Float32_by_bit_pattern.Map.t".
    (* container_types_intf.ml:138  val empty : 'a t *)
    Parameter empty : forall {A : Type}, t A.
    Extract Inlined Constant empty => "Numeric_types.Float32_by_bit_pattern.Map.empty".
    (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
    Parameter is_empty : forall {A : Type}, t A -> M bool.
    Extract Inlined Constant is_empty => "Numeric_types.Float32_by_bit_pattern.Map.is_empty".
    (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
    Parameter mem : forall {A : Type}, key -> t A -> M bool.
    Extract Inlined Constant mem => "Numeric_types.Float32_by_bit_pattern.Map.mem".
    (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
    Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
    Extract Inlined Constant add => "Numeric_types.Float32_by_bit_pattern.Map.add".
    (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
    Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant update => "Numeric_types.Float32_by_bit_pattern.Map.update".
    (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
    Parameter singleton : forall {A : Type}, key -> A -> M (t A).
    Extract Inlined Constant singleton => "Numeric_types.Float32_by_bit_pattern.Map.singleton".
    (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
    Parameter remove : forall {A : Type}, key -> t A -> M (t A).
    Extract Inlined Constant remove => "Numeric_types.Float32_by_bit_pattern.Map.remove".
    (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
    Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
    Extract Inlined Constant merge => "Numeric_types.Float32_by_bit_pattern.Map.merge".
    (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union => "Numeric_types.Float32_by_bit_pattern.Map.union".
    (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_sharing => "Numeric_types.Float32_by_bit_pattern.Map.union_sharing".
    (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_shared => "Numeric_types.Float32_by_bit_pattern.Map.union_shared".
    (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
    Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total => "Numeric_types.Float32_by_bit_pattern.Map.union_total".
    (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
    Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
    Extract Inlined Constant union_total_shared => "Numeric_types.Float32_by_bit_pattern.Map.union_total_shared".
    (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
    Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_left_biased => "Numeric_types.Float32_by_bit_pattern.Map.union_left_biased".
    (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
    Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
    Extract Inlined Constant union_right_biased => "Numeric_types.Float32_by_bit_pattern.Map.union_right_biased".
    (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant update_many => "Numeric_types.Float32_by_bit_pattern.Map.update_many".
    (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
    Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.Map.compare".
    (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
    Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.Map.equal".
    (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
    Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
    Extract Inlined Constant iter => "Numeric_types.Float32_by_bit_pattern.Map.iter".
    (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
    Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
    Extract Inlined Constant fold => "Numeric_types.Float32_by_bit_pattern.Map.fold".
    (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
    Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant for_all => "Numeric_types.Float32_by_bit_pattern.Map.for_all".
    (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
    Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
    Extract Inlined Constant exists_ => "Numeric_types.Float32_by_bit_pattern.Map.exists".
    (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
    Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
    Extract Inlined Constant filter => "Numeric_types.Float32_by_bit_pattern.Map.filter".
    (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
    Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
    Extract Inlined Constant filter_map => "Numeric_types.Float32_by_bit_pattern.Map.filter_map".
    (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
    Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
    Extract Inlined Constant filter_map_sharing => "Numeric_types.Float32_by_bit_pattern.Map.filter_map_sharing".
    (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
    Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
    Extract Inlined Constant partition => "Numeric_types.Float32_by_bit_pattern.Map.partition".
    (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
    Parameter cardinal : forall {A : Type}, t A -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Float32_by_bit_pattern.Map.cardinal".
    (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
    Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
    Extract Inlined Constant bindings => "Numeric_types.Float32_by_bit_pattern.Map.bindings".
    (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
    Parameter min_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant min_binding => "Numeric_types.Float32_by_bit_pattern.Map.min_binding".
    (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
    Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant min_binding_opt => "Numeric_types.Float32_by_bit_pattern.Map.min_binding_opt".
    (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
    Parameter max_binding : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant max_binding => "Numeric_types.Float32_by_bit_pattern.Map.max_binding".
    (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
    Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant max_binding_opt => "Numeric_types.Float32_by_bit_pattern.Map.max_binding_opt".
    (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
    Parameter choose : forall {A : Type}, t A -> M (key * A).
    Extract Inlined Constant choose => "Numeric_types.Float32_by_bit_pattern.Map.choose".
    (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
    Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant choose_opt => "Numeric_types.Float32_by_bit_pattern.Map.choose_opt".
    (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
    Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
    Extract Inlined Constant split => "Numeric_types.Float32_by_bit_pattern.Map.split".
    (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
    Parameter find : forall {A : Type}, key -> t A -> M A.
    Extract Inlined Constant find => "Numeric_types.Float32_by_bit_pattern.Map.find".
    (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
    Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
    Extract Inlined Constant find_opt => "Numeric_types.Float32_by_bit_pattern.Map.find_opt".
    (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
    Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
    Extract Inlined Constant find_or_null => "Numeric_types.Float32_by_bit_pattern.Map.find_or_null".
    (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
    Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
    Extract Inlined Constant map => "Numeric_types.Float32_by_bit_pattern.Map.map".
    (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
    Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
    Extract Inlined Constant mapi => "Numeric_types.Float32_by_bit_pattern.Map.mapi".
    (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
    Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
    Extract Inlined Constant to_seq => "Numeric_types.Float32_by_bit_pattern.Map.to_seq".
    (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
    Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print_debug => "Numeric_types.Float32_by_bit_pattern.Map.print_debug".
    (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
    Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
    Extract Inlined Constant of_list => "Numeric_types.Float32_by_bit_pattern.Map.of_list".
    (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
    Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
    Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Numeric_types.Float32_by_bit_pattern.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
    (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
    Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
    Extract Inlined Constant map_keys => "Numeric_types.Float32_by_bit_pattern.Map.map_keys".
    (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
    Parameter keys : forall {A : Type}, t A -> M Numeric_types.Float32_by_bit_pattern.Map.Set_.t.
    Extract Inlined Constant keys => "Numeric_types.Float32_by_bit_pattern.Map.keys".
    (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
    Parameter data : forall {A : Type}, t A -> M (list A).
    Extract Inlined Constant data => "Numeric_types.Float32_by_bit_pattern.Map.data".
    (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
    Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Float32_by_bit_pattern.Map.Set_.t -> M (t A).
    Extract Inlined Constant of_set => "Numeric_types.Float32_by_bit_pattern.Map.of_set".
    (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
    Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
    Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.Map.print".
    (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
    Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
    Extract Inlined Constant subset_domain => "Numeric_types.Float32_by_bit_pattern.Map.subset_domain".
    (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
    Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
    Extract Inlined Constant diff_domains => "Numeric_types.Float32_by_bit_pattern.Map.diff_domains".
    (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
    Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
    Extract Inlined Constant inter => "Numeric_types.Float32_by_bit_pattern.Map.inter".
    (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff => "Numeric_types.Float32_by_bit_pattern.Map.diff".
    (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
    Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
    Extract Inlined Constant diff_sharing => "Numeric_types.Float32_by_bit_pattern.Map.diff_sharing".
    (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
    Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
    Extract Inlined Constant diff_shared => "Numeric_types.Float32_by_bit_pattern.Map.diff_shared".
    (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
    Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
    Extract Inlined Constant inter_domain_is_non_empty => "Numeric_types.Float32_by_bit_pattern.Map.inter_domain_is_non_empty".
    (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
    Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
    Extract Inlined Constant get_singleton => "Numeric_types.Float32_by_bit_pattern.Map.get_singleton".
    (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
    Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant replace => "Numeric_types.Float32_by_bit_pattern.Map.replace".
    (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
    Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
    Extract Inlined Constant map_sharing => "Numeric_types.Float32_by_bit_pattern.Map.map_sharing".
  End Map.
  (* numeric_types.mli:145  val create : float -> t *)
  Parameter create : Stdlib_.float_ -> M t.
  Extract Inlined Constant create => "Numeric_types.Float32_by_bit_pattern.create".
  (* numeric_types.mli:147  val of_bits : bits -> t *)
  Parameter of_bits : bits -> M t.
  Extract Inlined Constant of_bits => "Numeric_types.Float32_by_bit_pattern.of_bits".
  (* numeric_types.mli:149  val to_bits : t -> bits *)
  Parameter to_bits : t -> M bits.
  Extract Inlined Constant to_bits => "Numeric_types.Float32_by_bit_pattern.to_bits".
  (* numeric_types.mli:151  val of_int64 : int64 -> t *)
  Parameter of_int64 : Stdlib_.int64 -> M t.
  Extract Inlined Constant of_int64 => "Numeric_types.Float32_by_bit_pattern.of_int64".
  (* numeric_types.mli:153  val of_string : string -> t *)
  Parameter of_string : string -> M t.
  Extract Inlined Constant of_string => "Numeric_types.Float32_by_bit_pattern.of_string".
  (* numeric_types.mli:155  val to_float : t -> float *)
  Parameter to_float : t -> M Stdlib_.float_.
  Extract Inlined Constant to_float => "Numeric_types.Float32_by_bit_pattern.to_float".
  (* numeric_types.mli:157  val one : t *)
  Parameter one : t.
  Extract Inlined Constant one => "Numeric_types.Float32_by_bit_pattern.one".
  (* numeric_types.mli:159  val zero : t *)
  Parameter zero : t.
  Extract Inlined Constant zero => "Numeric_types.Float32_by_bit_pattern.zero".
  (* numeric_types.mli:161  val minus_one : t *)
  Parameter minus_one : t.
  Extract Inlined Constant minus_one => "Numeric_types.Float32_by_bit_pattern.minus_one".
  (* numeric_types.mli:163  val is_either_zero : t -> bool *)
  Parameter is_either_zero : t -> M bool.
  Extract Inlined Constant is_either_zero => "Numeric_types.Float32_by_bit_pattern.is_either_zero".
  (* numeric_types.mli:165  val is_any_nan : t -> bool *)
  Parameter is_any_nan : t -> M bool.
  Extract Inlined Constant is_any_nan => "Numeric_types.Float32_by_bit_pattern.is_any_nan".
  Module IEEE_semantics.
    (* numeric_types.mli:167  module IEEE_semantics : IEEE_semantics with type t = t *)
    Definition t : Type := Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.t".
    (* numeric_types.mli:110  val add : t -> t -> t *)
    Parameter add : t -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.add".
    (* numeric_types.mli:112  val sub : t -> t -> t *)
    Parameter sub : t -> t -> M t.
    Extract Inlined Constant sub => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.sub".
    (* numeric_types.mli:114  val mul : t -> t -> t *)
    Parameter mul : t -> t -> M t.
    Extract Inlined Constant mul => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.mul".
    (* numeric_types.mli:116  val div : t -> t -> t *)
    Parameter div : t -> t -> M t.
    Extract Inlined Constant div => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.div".
    (* numeric_types.mli:118  val mod_ : t -> t -> t *)
    Parameter mod_ : t -> t -> M t.
    Extract Inlined Constant mod_ => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.mod_".
    (* numeric_types.mli:120  val neg : t -> t *)
    Parameter neg : t -> M t.
    Extract Inlined Constant neg => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.neg".
    (* numeric_types.mli:122  val abs : t -> t *)
    Parameter abs : t -> M t.
    Extract Inlined Constant abs => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.abs".
    (* numeric_types.mli:124  val compare : t -> t -> int *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.compare".
    (* numeric_types.mli:126  val equal : t -> t -> bool *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.equal".
  End IEEE_semantics.
  Module Pair.
    (* numeric_types.mli:169  module Pair : Container_types.S with type t = t * t *)
    Definition t : Type := (Numeric_types.Float32_by_bit_pattern.t * Numeric_types.Float32_by_bit_pattern.t).
    Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.Pair.t".
    Module T.
      (* container_types_intf.ml:299  module T : Thing with type t = t *)
      Definition t : Type := Numeric_types.Float32_by_bit_pattern.Pair.t.
      Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.Pair.T.t".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.Pair.T.equal".
      (* container_types_intf.ml:28  include Hashtbl.HashedType with type t := t *)
      Parameter hash : t -> M int.
      Extract Inlined Constant hash => "Numeric_types.Float32_by_bit_pattern.Pair.T.hash".
      (* container_types_intf.ml:30  include Map.OrderedType with type t := t *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.Pair.T.compare".
      (* container_types_intf.ml:32  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.Pair.T.print".
    End T.
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter equal : Numeric_types.Float32_by_bit_pattern.Pair.T.t -> Numeric_types.Float32_by_bit_pattern.Pair.T.t -> M bool.
    Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.Pair.equal".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter hash : Numeric_types.Float32_by_bit_pattern.Pair.T.t -> M int.
    Extract Inlined Constant hash => "Numeric_types.Float32_by_bit_pattern.Pair.hash".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter compare : Numeric_types.Float32_by_bit_pattern.Pair.T.t -> Numeric_types.Float32_by_bit_pattern.Pair.T.t -> M int.
    Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.Pair.compare".
    (* container_types_intf.ml:301  include Thing with type t := T.t *)
    Parameter print : Format.formatter -> Numeric_types.Float32_by_bit_pattern.Pair.T.t -> M unit.
    Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.Pair.print".
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Numeric_types.Float32_by_bit_pattern.Pair.t.
      Extract Inlined Constant elt => "Numeric_types.Float32_by_bit_pattern.Pair.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.Pair.Set.t".
      (* container_types_intf.ml:40  val empty : t *)
      Parameter empty : t.
      Extract Inlined Constant empty => "Numeric_types.Float32_by_bit_pattern.Pair.Set.empty".
      (* container_types_intf.ml:42  val is_empty : t -> bool *)
      Parameter is_empty : t -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Float32_by_bit_pattern.Pair.Set.is_empty".
      (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
      Parameter mem : elt -> t -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Float32_by_bit_pattern.Pair.Set.mem".
      (* container_types_intf.ml:46  val add : elt -> t -> t *)
      Parameter add : elt -> t -> M t.
      Extract Inlined Constant add => "Numeric_types.Float32_by_bit_pattern.Pair.Set.add".
      (* container_types_intf.ml:48  val singleton : elt -> t *)
      Parameter singleton : elt -> M t.
      Extract Inlined Constant singleton => "Numeric_types.Float32_by_bit_pattern.Pair.Set.singleton".
      (* container_types_intf.ml:50  val remove : elt -> t -> t *)
      Parameter remove : elt -> t -> M t.
      Extract Inlined Constant remove => "Numeric_types.Float32_by_bit_pattern.Pair.Set.remove".
      (* container_types_intf.ml:52  val union : t -> t -> t *)
      Parameter union : t -> t -> M t.
      Extract Inlined Constant union => "Numeric_types.Float32_by_bit_pattern.Pair.Set.union".
      (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
      Parameter union_sharing : t -> t -> M t.
      Extract Inlined Constant union_sharing => "Numeric_types.Float32_by_bit_pattern.Pair.Set.union_sharing".
      (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
      Parameter union_shared : t -> t -> M t.
      Extract Inlined Constant union_shared => "Numeric_types.Float32_by_bit_pattern.Pair.Set.union_shared".
      (* container_types_intf.ml:62  val inter : t -> t -> t *)
      Parameter inter : t -> t -> M t.
      Extract Inlined Constant inter => "Numeric_types.Float32_by_bit_pattern.Pair.Set.inter".
      (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
      Parameter disjoint : t -> t -> M bool.
      Extract Inlined Constant disjoint => "Numeric_types.Float32_by_bit_pattern.Pair.Set.disjoint".
      (* container_types_intf.ml:66  val diff : t -> t -> t *)
      Parameter diff : t -> t -> M t.
      Extract Inlined Constant diff => "Numeric_types.Float32_by_bit_pattern.Pair.Set.diff".
      (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
      Parameter diff_sharing : t -> t -> M t.
      Extract Inlined Constant diff_sharing => "Numeric_types.Float32_by_bit_pattern.Pair.Set.diff_sharing".
      (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
      Parameter diff_shared : t -> t -> M t.
      Extract Inlined Constant diff_shared => "Numeric_types.Float32_by_bit_pattern.Pair.Set.diff_shared".
      (* container_types_intf.ml:76  val compare : t -> t -> int *)
      Parameter compare : t -> t -> M int.
      Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.Pair.Set.compare".
      (* container_types_intf.ml:78  val equal : t -> t -> bool *)
      Parameter equal : t -> t -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.Pair.Set.equal".
      (* container_types_intf.ml:80  val subset : t -> t -> bool *)
      Parameter subset : t -> t -> M bool.
      Extract Inlined Constant subset => "Numeric_types.Float32_by_bit_pattern.Pair.Set.subset".
      (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
      Parameter iter : (elt -> M unit) -> t -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Float32_by_bit_pattern.Pair.Set.iter".
      (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
      Parameter map : (elt -> M elt) -> t -> M t.
      Extract Inlined Constant map => "Numeric_types.Float32_by_bit_pattern.Pair.Set.map".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Float32_by_bit_pattern.Pair.Set.fold".
      (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
      Parameter for_all : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Float32_by_bit_pattern.Pair.Set.for_all".
      (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
      Parameter exists_ : (elt -> M bool) -> t -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Float32_by_bit_pattern.Pair.Set.exists".
      (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
      Parameter filter : (elt -> M bool) -> t -> M t.
      Extract Inlined Constant filter => "Numeric_types.Float32_by_bit_pattern.Pair.Set.filter".
      (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
      Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
      Extract Inlined Constant filter_map => "Numeric_types.Float32_by_bit_pattern.Pair.Set.filter_map".
      (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
      Parameter partition : (elt -> M bool) -> t -> M (t * t).
      Extract Inlined Constant partition => "Numeric_types.Float32_by_bit_pattern.Pair.Set.partition".
      (* container_types_intf.ml:98  val cardinal : t -> int *)
      Parameter cardinal : t -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Float32_by_bit_pattern.Pair.Set.cardinal".
      (* container_types_intf.ml:100  val elements : t -> elt list *)
      Parameter elements : t -> M (list elt).
      Extract Inlined Constant elements => "Numeric_types.Float32_by_bit_pattern.Pair.Set.elements".
      (* container_types_intf.ml:102  val min_elt : t -> elt *)
      Parameter min_elt : t -> M elt.
      Extract Inlined Constant min_elt => "Numeric_types.Float32_by_bit_pattern.Pair.Set.min_elt".
      (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
      Parameter min_elt_opt : t -> M (option elt).
      Extract Inlined Constant min_elt_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Set.min_elt_opt".
      (* container_types_intf.ml:106  val max_elt : t -> elt *)
      Parameter max_elt : t -> M elt.
      Extract Inlined Constant max_elt => "Numeric_types.Float32_by_bit_pattern.Pair.Set.max_elt".
      (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
      Parameter max_elt_opt : t -> M (option elt).
      Extract Inlined Constant max_elt_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Set.max_elt_opt".
      (* container_types_intf.ml:110  val choose : t -> elt *)
      Parameter choose : t -> M elt.
      Extract Inlined Constant choose => "Numeric_types.Float32_by_bit_pattern.Pair.Set.choose".
      (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
      Parameter choose_opt : t -> M (option elt).
      Extract Inlined Constant choose_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Set.choose_opt".
      (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
      Parameter split : elt -> t -> M (tuple3 t bool t).
      Extract Inlined Constant split => "Numeric_types.Float32_by_bit_pattern.Pair.Set.split".
      (* container_types_intf.ml:116  val find : elt -> t -> elt *)
      Parameter find : elt -> t -> M elt.
      Extract Inlined Constant find => "Numeric_types.Float32_by_bit_pattern.Pair.Set.find".
      (* container_types_intf.ml:118  val of_list : elt list -> t *)
      Parameter of_list : list elt -> M t.
      Extract Inlined Constant of_list => "Numeric_types.Float32_by_bit_pattern.Pair.Set.of_list".
      (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
      Parameter to_seq : t -> Seq.t elt.
      Extract Inlined Constant to_seq => "Numeric_types.Float32_by_bit_pattern.Pair.Set.to_seq".
      (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
      Parameter print : Format.formatter -> t -> M unit.
      Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.Pair.Set.print".
      (* container_types_intf.ml:124  val to_string : t -> string *)
      Parameter to_string : t -> M string.
      Extract Inlined Constant to_string => "Numeric_types.Float32_by_bit_pattern.Pair.Set.to_string".
      (* container_types_intf.ml:126  val union_list : t list -> t *)
      Parameter union_list : list t -> M t.
      Extract Inlined Constant union_list => "Numeric_types.Float32_by_bit_pattern.Pair.Set.union_list".
      (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
      Parameter get_singleton : t -> M (option elt).
      Extract Inlined Constant get_singleton => "Numeric_types.Float32_by_bit_pattern.Pair.Set.get_singleton".
    End Set_.
    Module Map.
      (* container_types_intf.ml:305  module Map : Map with type key = t and module Set = Set *)
      Definition key : Type := Numeric_types.Float32_by_bit_pattern.Pair.t.
      Extract Inlined Constant key => "Numeric_types.Float32_by_bit_pattern.Pair.Map.key".
      Module Set_.
        (* container_types_intf.ml:303  module Set : Set with type elt = t *)
        Definition elt : Type := Numeric_types.Float32_by_bit_pattern.Pair.t.
        Extract Inlined Constant elt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.elt".
        (* container_types_intf.ml:38  type t *)
        Definition t : Type := Numeric_types.Float32_by_bit_pattern.Pair.Set_.t.
        Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.t".
        (* container_types_intf.ml:40  val empty : t *)
        Parameter empty : t.
        Extract Inlined Constant empty => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.empty".
        (* container_types_intf.ml:42  val is_empty : t -> bool *)
        Parameter is_empty : t -> M bool.
        Extract Inlined Constant is_empty => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.is_empty".
        (* container_types_intf.ml:44  val mem : elt -> t -> bool *)
        Parameter mem : elt -> t -> M bool.
        Extract Inlined Constant mem => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.mem".
        (* container_types_intf.ml:46  val add : elt -> t -> t *)
        Parameter add : elt -> t -> M t.
        Extract Inlined Constant add => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.add".
        (* container_types_intf.ml:48  val singleton : elt -> t *)
        Parameter singleton : elt -> M t.
        Extract Inlined Constant singleton => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.singleton".
        (* container_types_intf.ml:50  val remove : elt -> t -> t *)
        Parameter remove : elt -> t -> M t.
        Extract Inlined Constant remove => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.remove".
        (* container_types_intf.ml:52  val union : t -> t -> t *)
        Parameter union : t -> t -> M t.
        Extract Inlined Constant union => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.union".
        (* container_types_intf.ml:56  val union_sharing : t -> t -> t *)
        Parameter union_sharing : t -> t -> M t.
        Extract Inlined Constant union_sharing => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.union_sharing".
        (* container_types_intf.ml:60  val union_shared : t -> t -> t *)
        Parameter union_shared : t -> t -> M t.
        Extract Inlined Constant union_shared => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.union_shared".
        (* container_types_intf.ml:62  val inter : t -> t -> t *)
        Parameter inter : t -> t -> M t.
        Extract Inlined Constant inter => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.inter".
        (* container_types_intf.ml:64  val disjoint : t -> t -> bool *)
        Parameter disjoint : t -> t -> M bool.
        Extract Inlined Constant disjoint => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.disjoint".
        (* container_types_intf.ml:66  val diff : t -> t -> t *)
        Parameter diff : t -> t -> M t.
        Extract Inlined Constant diff => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.diff".
        (* container_types_intf.ml:70  val diff_sharing : t -> t -> t *)
        Parameter diff_sharing : t -> t -> M t.
        Extract Inlined Constant diff_sharing => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.diff_sharing".
        (* container_types_intf.ml:74  val diff_shared : t -> t -> t *)
        Parameter diff_shared : t -> t -> M t.
        Extract Inlined Constant diff_shared => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.diff_shared".
        (* container_types_intf.ml:76  val compare : t -> t -> int *)
        Parameter compare : t -> t -> M int.
        Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.compare".
        (* container_types_intf.ml:78  val equal : t -> t -> bool *)
        Parameter equal : t -> t -> M bool.
        Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.equal".
        (* container_types_intf.ml:80  val subset : t -> t -> bool *)
        Parameter subset : t -> t -> M bool.
        Extract Inlined Constant subset => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.subset".
        (* container_types_intf.ml:82  val iter : (elt -> unit) -> t -> unit *)
        Parameter iter : (elt -> M unit) -> t -> M unit.
        Extract Inlined Constant iter => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.iter".
        (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
        Parameter map : (elt -> M elt) -> t -> M t.
        Extract Inlined Constant map => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.map".
        (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
        Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
        Extract Inlined Constant fold => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.fold".
        (* container_types_intf.ml:88  val for_all : (elt -> bool) -> t -> bool *)
        Parameter for_all : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant for_all => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.for_all".
        (* container_types_intf.ml:90  val exists : (elt -> bool) -> t -> bool *)
        Parameter exists_ : (elt -> M bool) -> t -> M bool.
        Extract Inlined Constant exists_ => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.exists".
        (* container_types_intf.ml:92  val filter : (elt -> bool) -> t -> t *)
        Parameter filter : (elt -> M bool) -> t -> M t.
        Extract Inlined Constant filter => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.filter".
        (* container_types_intf.ml:94  val filter_map : (elt -> elt option) -> t -> t *)
        Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
        Extract Inlined Constant filter_map => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.filter_map".
        (* container_types_intf.ml:96  val partition : (elt -> bool) -> t -> t * t *)
        Parameter partition : (elt -> M bool) -> t -> M (t * t).
        Extract Inlined Constant partition => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.partition".
        (* container_types_intf.ml:98  val cardinal : t -> int *)
        Parameter cardinal : t -> M int.
        Extract Inlined Constant cardinal => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.cardinal".
        (* container_types_intf.ml:100  val elements : t -> elt list *)
        Parameter elements : t -> M (list elt).
        Extract Inlined Constant elements => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.elements".
        (* container_types_intf.ml:102  val min_elt : t -> elt *)
        Parameter min_elt : t -> M elt.
        Extract Inlined Constant min_elt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.min_elt".
        (* container_types_intf.ml:104  val min_elt_opt : t -> elt option *)
        Parameter min_elt_opt : t -> M (option elt).
        Extract Inlined Constant min_elt_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.min_elt_opt".
        (* container_types_intf.ml:106  val max_elt : t -> elt *)
        Parameter max_elt : t -> M elt.
        Extract Inlined Constant max_elt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.max_elt".
        (* container_types_intf.ml:108  val max_elt_opt : t -> elt option *)
        Parameter max_elt_opt : t -> M (option elt).
        Extract Inlined Constant max_elt_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.max_elt_opt".
        (* container_types_intf.ml:110  val choose : t -> elt *)
        Parameter choose : t -> M elt.
        Extract Inlined Constant choose => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.choose".
        (* container_types_intf.ml:112  val choose_opt : t -> elt option *)
        Parameter choose_opt : t -> M (option elt).
        Extract Inlined Constant choose_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.choose_opt".
        (* container_types_intf.ml:114  val split : elt -> t -> t * bool * t *)
        Parameter split : elt -> t -> M (tuple3 t bool t).
        Extract Inlined Constant split => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.split".
        (* container_types_intf.ml:116  val find : elt -> t -> elt *)
        Parameter find : elt -> t -> M elt.
        Extract Inlined Constant find => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.find".
        (* container_types_intf.ml:118  val of_list : elt list -> t *)
        Parameter of_list : list elt -> M t.
        Extract Inlined Constant of_list => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.of_list".
        (* container_types_intf.ml:120  val to_seq : t -> elt Seq.t *)
        Parameter to_seq : t -> Seq.t elt.
        Extract Inlined Constant to_seq => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.to_seq".
        (* container_types_intf.ml:122  val print : Format.formatter -> t -> unit *)
        Parameter print : Format.formatter -> t -> M unit.
        Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.print".
        (* container_types_intf.ml:124  val to_string : t -> string *)
        Parameter to_string : t -> M string.
        Extract Inlined Constant to_string => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.to_string".
        (* container_types_intf.ml:126  val union_list : t list -> t *)
        Parameter union_list : list t -> M t.
        Extract Inlined Constant union_list => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.union_list".
        (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
        Parameter get_singleton : t -> M (option elt).
        Extract Inlined Constant get_singleton => "Numeric_types.Float32_by_bit_pattern.Pair.Map.Set.get_singleton".
      End Set_.
      (* container_types_intf.ml:136  type +!'a t *)
      Parameter t : Type -> Type.
      Extract Constant t "'a1" => "('a1) Numeric_types.Float32_by_bit_pattern.Pair.Map.t".
      (* container_types_intf.ml:138  val empty : 'a t *)
      Parameter empty : forall {A : Type}, t A.
      Extract Inlined Constant empty => "Numeric_types.Float32_by_bit_pattern.Pair.Map.empty".
      (* container_types_intf.ml:140  val is_empty : 'a t -> bool *)
      Parameter is_empty : forall {A : Type}, t A -> M bool.
      Extract Inlined Constant is_empty => "Numeric_types.Float32_by_bit_pattern.Pair.Map.is_empty".
      (* container_types_intf.ml:142  val mem : key -> 'a t -> bool *)
      Parameter mem : forall {A : Type}, key -> t A -> M bool.
      Extract Inlined Constant mem => "Numeric_types.Float32_by_bit_pattern.Pair.Map.mem".
      (* container_types_intf.ml:144  val add : key -> 'a -> 'a t -> 'a t *)
      Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
      Extract Inlined Constant add => "Numeric_types.Float32_by_bit_pattern.Pair.Map.add".
      (* container_types_intf.ml:146  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t *)
      Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant update => "Numeric_types.Float32_by_bit_pattern.Pair.Map.update".
      (* container_types_intf.ml:148  val singleton : key -> 'a -> 'a t *)
      Parameter singleton : forall {A : Type}, key -> A -> M (t A).
      Extract Inlined Constant singleton => "Numeric_types.Float32_by_bit_pattern.Pair.Map.singleton".
      (* container_types_intf.ml:150  val remove : key -> 'a t -> 'a t *)
      Parameter remove : forall {A : Type}, key -> t A -> M (t A).
      Extract Inlined Constant remove => "Numeric_types.Float32_by_bit_pattern.Pair.Map.remove".
      (* container_types_intf.ml:152  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
      Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
      Extract Inlined Constant merge => "Numeric_types.Float32_by_bit_pattern.Pair.Map.merge".
      (* container_types_intf.ml:157  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union => "Numeric_types.Float32_by_bit_pattern.Pair.Map.union".
      (* container_types_intf.ml:161  val union_sharing : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_sharing => "Numeric_types.Float32_by_bit_pattern.Pair.Map.union_sharing".
      (* container_types_intf.ml:166  val union_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_shared => "Numeric_types.Float32_by_bit_pattern.Pair.Map.union_shared".
      (* container_types_intf.ml:170  val union_total : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total => "Numeric_types.Float32_by_bit_pattern.Pair.Map.union_total".
      (* container_types_intf.ml:176  val union_total_shared : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t *)
      Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
      Extract Inlined Constant union_total_shared => "Numeric_types.Float32_by_bit_pattern.Pair.Map.union_total_shared".
      (* container_types_intf.ml:180  val union_left_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_left_biased => "Numeric_types.Float32_by_bit_pattern.Pair.Map.union_left_biased".
      (* container_types_intf.ml:184  val union_right_biased : 'a t -> 'a t -> 'a t *)
      Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
      Extract Inlined Constant union_right_biased => "Numeric_types.Float32_by_bit_pattern.Pair.Map.union_right_biased".
      (* container_types_intf.ml:186  val update_many : (key -> 'a option -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant update_many => "Numeric_types.Float32_by_bit_pattern.Pair.Map.update_many".
      (* container_types_intf.ml:189  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
      Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
      Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.Pair.Map.compare".
      (* container_types_intf.ml:191  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
      Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
      Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.Pair.Map.equal".
      (* container_types_intf.ml:193  val iter : (key -> 'a -> unit) -> 'a t -> unit *)
      Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
      Extract Inlined Constant iter => "Numeric_types.Float32_by_bit_pattern.Pair.Map.iter".
      (* container_types_intf.ml:195  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
      Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
      Extract Inlined Constant fold => "Numeric_types.Float32_by_bit_pattern.Pair.Map.fold".
      (* container_types_intf.ml:197  val for_all : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant for_all => "Numeric_types.Float32_by_bit_pattern.Pair.Map.for_all".
      (* container_types_intf.ml:199  val exists : (key -> 'a -> bool) -> 'a t -> bool *)
      Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
      Extract Inlined Constant exists_ => "Numeric_types.Float32_by_bit_pattern.Pair.Map.exists".
      (* container_types_intf.ml:201  val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
      Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
      Extract Inlined Constant filter => "Numeric_types.Float32_by_bit_pattern.Pair.Map.filter".
      (* container_types_intf.ml:203  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t *)
      Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
      Extract Inlined Constant filter_map => "Numeric_types.Float32_by_bit_pattern.Pair.Map.filter_map".
      (* container_types_intf.ml:205  val filter_map_sharing : (key -> 'a -> 'a option) -> 'a t -> 'a t *)
      Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
      Extract Inlined Constant filter_map_sharing => "Numeric_types.Float32_by_bit_pattern.Pair.Map.filter_map_sharing".
      (* container_types_intf.ml:207  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
      Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
      Extract Inlined Constant partition => "Numeric_types.Float32_by_bit_pattern.Pair.Map.partition".
      (* container_types_intf.ml:209  val cardinal : 'a t -> int *)
      Parameter cardinal : forall {A : Type}, t A -> M int.
      Extract Inlined Constant cardinal => "Numeric_types.Float32_by_bit_pattern.Pair.Map.cardinal".
      (* container_types_intf.ml:211  val bindings : 'a t -> (key * 'a) list *)
      Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
      Extract Inlined Constant bindings => "Numeric_types.Float32_by_bit_pattern.Pair.Map.bindings".
      (* container_types_intf.ml:213  val min_binding : 'a t -> key * 'a *)
      Parameter min_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant min_binding => "Numeric_types.Float32_by_bit_pattern.Pair.Map.min_binding".
      (* container_types_intf.ml:215  val min_binding_opt : 'a t -> (key * 'a) option *)
      Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant min_binding_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.min_binding_opt".
      (* container_types_intf.ml:217  val max_binding : 'a t -> key * 'a *)
      Parameter max_binding : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant max_binding => "Numeric_types.Float32_by_bit_pattern.Pair.Map.max_binding".
      (* container_types_intf.ml:219  val max_binding_opt : 'a t -> (key * 'a) option *)
      Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant max_binding_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.max_binding_opt".
      (* container_types_intf.ml:221  val choose : 'a t -> key * 'a *)
      Parameter choose : forall {A : Type}, t A -> M (key * A).
      Extract Inlined Constant choose => "Numeric_types.Float32_by_bit_pattern.Pair.Map.choose".
      (* container_types_intf.ml:223  val choose_opt : 'a t -> (key * 'a) option *)
      Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant choose_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.choose_opt".
      (* container_types_intf.ml:225  val split : key -> 'a t -> 'a t * 'a option * 'a t *)
      Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
      Extract Inlined Constant split => "Numeric_types.Float32_by_bit_pattern.Pair.Map.split".
      (* container_types_intf.ml:227  val find : key -> 'a t -> 'a *)
      Parameter find : forall {A : Type}, key -> t A -> M A.
      Extract Inlined Constant find => "Numeric_types.Float32_by_bit_pattern.Pair.Map.find".
      (* container_types_intf.ml:229  val find_opt : key -> 'a t -> 'a option *)
      Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
      Extract Inlined Constant find_opt => "Numeric_types.Float32_by_bit_pattern.Pair.Map.find_opt".
      (* container_types_intf.ml:231  val find_or_null : key -> 'a t -> 'a Or_null.t *)
      Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
      Extract Inlined Constant find_or_null => "Numeric_types.Float32_by_bit_pattern.Pair.Map.find_or_null".
      (* container_types_intf.ml:233  val map : ('a -> 'b) -> 'a t -> 'b t *)
      Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
      Extract Inlined Constant map => "Numeric_types.Float32_by_bit_pattern.Pair.Map.map".
      (* container_types_intf.ml:235  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
      Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
      Extract Inlined Constant mapi => "Numeric_types.Float32_by_bit_pattern.Pair.Map.mapi".
      (* container_types_intf.ml:237  val to_seq : 'a t -> (key * 'a) Seq.t *)
      Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
      Extract Inlined Constant to_seq => "Numeric_types.Float32_by_bit_pattern.Pair.Map.to_seq".
      (* container_types_intf.ml:239  val print_debug : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print_debug => "Numeric_types.Float32_by_bit_pattern.Pair.Map.print_debug".
      (* container_types_intf.ml:242  val of_list : (key * 'a) list -> 'a t *)
      Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
      Extract Inlined Constant of_list => "Numeric_types.Float32_by_bit_pattern.Pair.Map.of_list".
      (* container_types_intf.ml:244  val disjoint_union : ?eq:('a -> 'a -> bool) -> ?print:(Format.formatter -> 'a -> unit) -> 'a t -> 'a t -> 'a t *)
      Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
      Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Numeric_types.Float32_by_bit_pattern.Pair.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
      (* container_types_intf.ml:251  val map_keys : (key -> key) -> 'a t -> 'a t *)
      Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
      Extract Inlined Constant map_keys => "Numeric_types.Float32_by_bit_pattern.Pair.Map.map_keys".
      (* container_types_intf.ml:253  val keys : 'a t -> Set.t *)
      Parameter keys : forall {A : Type}, t A -> M Numeric_types.Float32_by_bit_pattern.Pair.Map.Set_.t.
      Extract Inlined Constant keys => "Numeric_types.Float32_by_bit_pattern.Pair.Map.keys".
      (* container_types_intf.ml:255  val data : 'a t -> 'a list *)
      Parameter data : forall {A : Type}, t A -> M (list A).
      Extract Inlined Constant data => "Numeric_types.Float32_by_bit_pattern.Pair.Map.data".
      (* container_types_intf.ml:257  val of_set : (key -> 'a) -> Set.t -> 'a t *)
      Parameter of_set : forall {A : Type}, (key -> M A) -> Numeric_types.Float32_by_bit_pattern.Pair.Map.Set_.t -> M (t A).
      Extract Inlined Constant of_set => "Numeric_types.Float32_by_bit_pattern.Pair.Map.of_set".
      (* container_types_intf.ml:259  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
      Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
      Extract Inlined Constant print => "Numeric_types.Float32_by_bit_pattern.Pair.Map.print".
      (* container_types_intf.ml:262  val subset_domain : 'a t -> 'b t -> bool *)
      Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
      Extract Inlined Constant subset_domain => "Numeric_types.Float32_by_bit_pattern.Pair.Map.subset_domain".
      (* container_types_intf.ml:264  val diff_domains : 'a t -> 'b t -> 'a t *)
      Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
      Extract Inlined Constant diff_domains => "Numeric_types.Float32_by_bit_pattern.Pair.Map.diff_domains".
      (* container_types_intf.ml:266  val inter : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
      Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
      Extract Inlined Constant inter => "Numeric_types.Float32_by_bit_pattern.Pair.Map.inter".
      (* container_types_intf.ml:276  val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff => "Numeric_types.Float32_by_bit_pattern.Pair.Map.diff".
      (* container_types_intf.ml:280  val diff_sharing : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t *)
      Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
      Extract Inlined Constant diff_sharing => "Numeric_types.Float32_by_bit_pattern.Pair.Map.diff_sharing".
      (* container_types_intf.ml:285  val diff_shared : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t *)
      Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
      Extract Inlined Constant diff_shared => "Numeric_types.Float32_by_bit_pattern.Pair.Map.diff_shared".
      (* container_types_intf.ml:287  val inter_domain_is_non_empty : 'a t -> 'a t -> bool *)
      Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
      Extract Inlined Constant inter_domain_is_non_empty => "Numeric_types.Float32_by_bit_pattern.Pair.Map.inter_domain_is_non_empty".
      (* container_types_intf.ml:289  val get_singleton : 'a t -> (key * 'a) option *)
      Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
      Extract Inlined Constant get_singleton => "Numeric_types.Float32_by_bit_pattern.Pair.Map.get_singleton".
      (* container_types_intf.ml:291  val replace : key -> ('a -> 'a) -> 'a t -> 'a t *)
      Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant replace => "Numeric_types.Float32_by_bit_pattern.Pair.Map.replace".
      (* container_types_intf.ml:293  val map_sharing : ('a -> 'a) -> 'a t -> 'a t *)
      Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
      Extract Inlined Constant map_sharing => "Numeric_types.Float32_by_bit_pattern.Pair.Map.map_sharing".
    End Map.
  End Pair.
  (* numeric_types.mli:171  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
  Parameter cross_product : Numeric_types.Float32_by_bit_pattern.Set_.t -> Numeric_types.Float32_by_bit_pattern.Set_.t -> M Numeric_types.Float32_by_bit_pattern.Pair.Set_.t.
  Extract Inlined Constant cross_product => "Numeric_types.Float32_by_bit_pattern.cross_product".
End Float32_by_bit_pattern.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Numeric_types. End Numeric_types.
