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

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Numeric_types], after its interface
   middle_end/flambda2/numbers/numeric_types.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Int32 Int64 Or_null Stdlib_.

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
  (* numeric_types.mli:50  val of_float : float -> t *)
  Parameter of_float : Stdlib_.float_ -> M t.
  Extract Inlined Constant of_float => "Numeric_types.Int8.of_float".
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
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Int8.Set.add".
  End Set_.
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
  (* numeric_types.mli:74  val of_float : float -> t *)
  Parameter of_float : Stdlib_.float_ -> M t.
  Extract Inlined Constant of_float => "Numeric_types.Int16.of_float".
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
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Int16.Set.add".
  End Set_.
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
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Int32.Set.add".
  End Set_.
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
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Int64.Set.add".
    (* numeric_types.mli:98  include Container_types.S with type t := Int64.t *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Numeric_types.Int64.Set.fold".
  End Set_.
End Int64.
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
  End T.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter equal : Numeric_types.Float_by_bit_pattern.T.t -> Numeric_types.Float_by_bit_pattern.T.t -> M bool.
  Extract Inlined Constant equal => "Numeric_types.Float_by_bit_pattern.equal".
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter compare : Numeric_types.Float_by_bit_pattern.T.t -> Numeric_types.Float_by_bit_pattern.T.t -> M int.
  Extract Inlined Constant compare => "Numeric_types.Float_by_bit_pattern.compare".
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
    (* container_types_intf.ml:46  val add : elt -> t -> t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Float_by_bit_pattern.Set.add".
    (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Numeric_types.Float_by_bit_pattern.Set.map".
    (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Numeric_types.Float_by_bit_pattern.Set.fold".
    (* container_types_intf.ml:98  val cardinal : t -> int *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Float_by_bit_pattern.Set.cardinal".
    (* container_types_intf.ml:118  val of_list : elt list -> t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Numeric_types.Float_by_bit_pattern.Set.of_list".
    (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Numeric_types.Float_by_bit_pattern.Set.get_singleton".
  End Set_.
  (* numeric_types.mli:145  val create : float -> t *)
  Parameter create : Stdlib_.float_ -> M t.
  Extract Inlined Constant create => "Numeric_types.Float_by_bit_pattern.create".
  (* numeric_types.mli:147  val of_bits : bits -> t *)
  Parameter of_bits : bits -> M t.
  Extract Inlined Constant of_bits => "Numeric_types.Float_by_bit_pattern.of_bits".
  (* numeric_types.mli:149  val to_bits : t -> bits *)
  Parameter to_bits : t -> M bits.
  Extract Inlined Constant to_bits => "Numeric_types.Float_by_bit_pattern.to_bits".
  (* numeric_types.mli:157  val one : t *)
  Parameter one : t.
  Extract Inlined Constant one => "Numeric_types.Float_by_bit_pattern.one".
  (* numeric_types.mli:159  val zero : t *)
  Parameter zero : t.
  Extract Inlined Constant zero => "Numeric_types.Float_by_bit_pattern.zero".
  (* numeric_types.mli:161  val minus_one : t *)
  Parameter minus_one : t.
  Extract Inlined Constant minus_one => "Numeric_types.Float_by_bit_pattern.minus_one".
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
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Numeric_types.Float_by_bit_pattern.Pair.t.
      Extract Inlined Constant elt => "Numeric_types.Float_by_bit_pattern.Pair.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Numeric_types.Float_by_bit_pattern.Pair.Set.t".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Float_by_bit_pattern.Pair.Set.fold".
    End Set_.
  End Pair.
  (* numeric_types.mli:171  val cross_product : Set.t -> Set.t -> Pair.Set.t *)
  Parameter cross_product : Numeric_types.Float_by_bit_pattern.Set_.t -> Numeric_types.Float_by_bit_pattern.Set_.t -> M Numeric_types.Float_by_bit_pattern.Pair.Set_.t.
  Extract Inlined Constant cross_product => "Numeric_types.Float_by_bit_pattern.cross_product".
End Float_by_bit_pattern.
Module Float32_by_bit_pattern.
  (* container_types_intf.ml:297  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.t".
  Module T.
    (* container_types_intf.ml:299  module T : Thing with type t = t *)
    Definition t : Type := Numeric_types.Float32_by_bit_pattern.t.
    Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.T.t".
  End T.
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter equal : Numeric_types.Float32_by_bit_pattern.T.t -> Numeric_types.Float32_by_bit_pattern.T.t -> M bool.
  Extract Inlined Constant equal => "Numeric_types.Float32_by_bit_pattern.equal".
  (* container_types_intf.ml:301  include Thing with type t := T.t *)
  Parameter compare : Numeric_types.Float32_by_bit_pattern.T.t -> Numeric_types.Float32_by_bit_pattern.T.t -> M int.
  Extract Inlined Constant compare => "Numeric_types.Float32_by_bit_pattern.compare".
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
    (* container_types_intf.ml:46  val add : elt -> t -> t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Numeric_types.Float32_by_bit_pattern.Set.add".
    (* container_types_intf.ml:84  val map : (elt -> elt) -> t -> t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Numeric_types.Float32_by_bit_pattern.Set.map".
    (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Numeric_types.Float32_by_bit_pattern.Set.fold".
    (* container_types_intf.ml:98  val cardinal : t -> int *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Numeric_types.Float32_by_bit_pattern.Set.cardinal".
    (* container_types_intf.ml:118  val of_list : elt list -> t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Numeric_types.Float32_by_bit_pattern.Set.of_list".
    (* container_types_intf.ml:128  val get_singleton : t -> elt option *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Numeric_types.Float32_by_bit_pattern.Set.get_singleton".
  End Set_.
  (* numeric_types.mli:145  val create : float -> t *)
  Parameter create : Stdlib_.float_ -> M t.
  Extract Inlined Constant create => "Numeric_types.Float32_by_bit_pattern.create".
  (* numeric_types.mli:151  val of_int64 : int64 -> t *)
  Parameter of_int64 : Stdlib_.int64 -> M t.
  Extract Inlined Constant of_int64 => "Numeric_types.Float32_by_bit_pattern.of_int64".
  (* numeric_types.mli:157  val one : t *)
  Parameter one : t.
  Extract Inlined Constant one => "Numeric_types.Float32_by_bit_pattern.one".
  (* numeric_types.mli:159  val zero : t *)
  Parameter zero : t.
  Extract Inlined Constant zero => "Numeric_types.Float32_by_bit_pattern.zero".
  (* numeric_types.mli:161  val minus_one : t *)
  Parameter minus_one : t.
  Extract Inlined Constant minus_one => "Numeric_types.Float32_by_bit_pattern.minus_one".
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
    Module Set_.
      (* container_types_intf.ml:303  module Set : Set with type elt = t *)
      Definition elt : Type := Numeric_types.Float32_by_bit_pattern.Pair.t.
      Extract Inlined Constant elt => "Numeric_types.Float32_by_bit_pattern.Pair.Set.elt".
      (* container_types_intf.ml:38  type t *)
      Parameter t : Type.
      Extract Inlined Constant t => "Numeric_types.Float32_by_bit_pattern.Pair.Set.t".
      (* container_types_intf.ml:86  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Inlined Constant fold => "Numeric_types.Float32_by_bit_pattern.Pair.Set.fold".
    End Set_.
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
