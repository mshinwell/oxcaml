(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                        Nicolas Ojeda Bar, LexiFi                       *)
(*                    Mark Shinwell, Jane Street Europe                   *)
(*                                                                        *)
(*   Copyright 2016 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*   Copyright 2017--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Targetint_32_64], after its interface
   middle_end/flambda2/numbers/targetint_32_64.mli
   (Git blob 5ab59bc3c194fab0f33c2898eb4a9e009166ecc0). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Or_null Seq Stdlib_ Target_system.

(* targetint_32_64.mli:32  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Targetint_32_64.t".
(* targetint_32_64.mli:43  val zero_like : t -> t *)
Parameter zero_like : t -> M t.
Extract Inlined Constant zero_like => "Targetint_32_64.zero_like".
(* targetint_32_64.mli:66  val div : t -> t -> t *)
Parameter div : t -> t -> M t.
Extract Inlined Constant div => "Targetint_32_64.div".
(* targetint_32_64.mli:70  val unsigned_div : t -> t -> t *)
Parameter unsigned_div : t -> t -> M t.
Extract Inlined Constant unsigned_div => "Targetint_32_64.unsigned_div".
(* targetint_32_64.mli:78  val rem : t -> t -> t *)
Parameter rem : t -> t -> M t.
Extract Inlined Constant rem => "Targetint_32_64.rem".
(* targetint_32_64.mli:82  val unsigned_rem : t -> t -> t *)
Parameter unsigned_rem : t -> t -> M t.
Extract Inlined Constant unsigned_rem => "Targetint_32_64.unsigned_rem".
(* targetint_32_64.mli:104  val logand : t -> t -> t *)
Parameter logand : t -> t -> M t.
Extract Inlined Constant logand => "Targetint_32_64.logand".
(* targetint_32_64.mli:107  val logor : t -> t -> t *)
Parameter logor : t -> t -> M t.
Extract Inlined Constant logor => "Targetint_32_64.logor".
(* targetint_32_64.mli:110  val logxor : t -> t -> t *)
Parameter logxor : t -> t -> M t.
Extract Inlined Constant logxor => "Targetint_32_64.logxor".
(* targetint_32_64.mli:113  val lognot : t -> t *)
Parameter lognot : t -> M t.
Extract Inlined Constant lognot => "Targetint_32_64.lognot".
(* targetint_32_64.mli:119  val shift_left : t -> int -> t *)
Parameter shift_left : t -> int -> M t.
Extract Inlined Constant shift_left => "Targetint_32_64.shift_left".
(* targetint_32_64.mli:127  val shift_right : t -> int -> t *)
Parameter shift_right : t -> int -> M t.
Extract Inlined Constant shift_right => "Targetint_32_64.shift_right".
(* targetint_32_64.mli:136  val shift_right_logical : t -> int -> t *)
Parameter shift_right_logical : t -> int -> M t.
Extract Inlined Constant shift_right_logical => "Targetint_32_64.shift_right_logical".
(* targetint_32_64.mli:140  val of_int : Target_system.Machine_width.t -> int -> t *)
Parameter of_int : Target_system.Machine_width.t -> int -> M t.
Extract Inlined Constant of_int => "Targetint_32_64.of_int".
(* targetint_32_64.mli:148  val to_int : t -> int *)
Parameter to_int : t -> M int.
Extract Inlined Constant to_int => "Targetint_32_64.to_int".
(* targetint_32_64.mli:159  val of_float : Target_system.Machine_width.t -> float -> t *)
Parameter of_float : Target_system.Machine_width.t -> Stdlib_.float_ -> M t.
Extract Inlined Constant of_float => "Targetint_32_64.of_float".
(* targetint_32_64.mli:162  val to_float : t -> float *)
Parameter to_float : t -> M Stdlib_.float_.
Extract Inlined Constant to_float => "Targetint_32_64.to_float".
(* targetint_32_64.mli:165  val of_int32 : Target_system.Machine_width.t -> int32 -> t *)
Parameter of_int32 : Target_system.Machine_width.t -> Stdlib_.int32 -> M t.
Extract Inlined Constant of_int32 => "Targetint_32_64.of_int32".
(* targetint_32_64.mli:171  val to_int32 : t -> int32 *)
Parameter to_int32 : t -> M Stdlib_.int32.
Extract Inlined Constant to_int32 => "Targetint_32_64.to_int32".
(* targetint_32_64.mli:175  val of_int64 : Target_system.Machine_width.t -> int64 -> t *)
Parameter of_int64 : Target_system.Machine_width.t -> Stdlib_.int64 -> M t.
Extract Inlined Constant of_int64 => "Targetint_32_64.of_int64".
(* targetint_32_64.mli:178  val to_int64 : t -> int64 *)
Parameter to_int64 : t -> M Stdlib_.int64.
Extract Inlined Constant to_int64 => "Targetint_32_64.to_int64".
Module T.
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Definition t : Type := Targetint_32_64.t.
  Extract Inlined Constant t => "Targetint_32_64.T.t".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Targetint_32_64.T.equal".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter hash : t -> M int.
  Extract Inlined Constant hash => "Targetint_32_64.T.hash".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter compare : t -> t -> M int.
  Extract Inlined Constant compare => "Targetint_32_64.T.compare".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Targetint_32_64.T.print".
End T.
(* targetint_32_64.mli:217  include Container_types.S with type t := t *)
Parameter equal : Targetint_32_64.T.t -> Targetint_32_64.T.t -> M bool.
Extract Inlined Constant equal => "Targetint_32_64.equal".
(* targetint_32_64.mli:217  include Container_types.S with type t := t *)
Parameter hash : Targetint_32_64.T.t -> M int.
Extract Inlined Constant hash => "Targetint_32_64.hash".
(* targetint_32_64.mli:217  include Container_types.S with type t := t *)
Parameter compare : Targetint_32_64.T.t -> Targetint_32_64.T.t -> M int.
Extract Inlined Constant compare => "Targetint_32_64.compare".
(* targetint_32_64.mli:217  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Targetint_32_64.T.t -> M unit.
Extract Inlined Constant print => "Targetint_32_64.print".
Module Set_.
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Definition elt : Type := Targetint_32_64.t.
  Extract Inlined Constant elt => "Targetint_32_64.Set.elt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Targetint_32_64.Set.t".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter empty : t.
  Extract Inlined Constant empty => "Targetint_32_64.Set.empty".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter is_empty : t -> M bool.
  Extract Inlined Constant is_empty => "Targetint_32_64.Set.is_empty".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter mem : elt -> t -> M bool.
  Extract Inlined Constant mem => "Targetint_32_64.Set.mem".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Targetint_32_64.Set.add".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter singleton : elt -> M t.
  Extract Inlined Constant singleton => "Targetint_32_64.Set.singleton".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter remove : elt -> t -> M t.
  Extract Inlined Constant remove => "Targetint_32_64.Set.remove".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union : t -> t -> M t.
  Extract Inlined Constant union => "Targetint_32_64.Set.union".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union_sharing : t -> t -> M t.
  Extract Inlined Constant union_sharing => "Targetint_32_64.Set.union_sharing".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union_shared : t -> t -> M t.
  Extract Inlined Constant union_shared => "Targetint_32_64.Set.union_shared".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter inter : t -> t -> M t.
  Extract Inlined Constant inter => "Targetint_32_64.Set.inter".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter disjoint : t -> t -> M bool.
  Extract Inlined Constant disjoint => "Targetint_32_64.Set.disjoint".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter diff : t -> t -> M t.
  Extract Inlined Constant diff => "Targetint_32_64.Set.diff".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter diff_sharing : t -> t -> M t.
  Extract Inlined Constant diff_sharing => "Targetint_32_64.Set.diff_sharing".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter diff_shared : t -> t -> M t.
  Extract Inlined Constant diff_shared => "Targetint_32_64.Set.diff_shared".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter compare : t -> t -> M int.
  Extract Inlined Constant compare => "Targetint_32_64.Set.compare".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter equal : t -> t -> M bool.
  Extract Inlined Constant equal => "Targetint_32_64.Set.equal".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter subset : t -> t -> M bool.
  Extract Inlined Constant subset => "Targetint_32_64.Set.subset".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter iter : (elt -> M unit) -> t -> M unit.
  Extract Inlined Constant iter => "Targetint_32_64.Set.iter".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter map : (elt -> M elt) -> t -> M t.
  Extract Inlined Constant map => "Targetint_32_64.Set.map".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Targetint_32_64.Set.fold".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter for_all : (elt -> M bool) -> t -> M bool.
  Extract Inlined Constant for_all => "Targetint_32_64.Set.for_all".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter exists_ : (elt -> M bool) -> t -> M bool.
  Extract Inlined Constant exists_ => "Targetint_32_64.Set.exists".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter filter : (elt -> M bool) -> t -> M t.
  Extract Inlined Constant filter => "Targetint_32_64.Set.filter".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
  Extract Inlined Constant filter_map => "Targetint_32_64.Set.filter_map".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter partition : (elt -> M bool) -> t -> M (t * t).
  Extract Inlined Constant partition => "Targetint_32_64.Set.partition".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter cardinal : t -> M int.
  Extract Inlined Constant cardinal => "Targetint_32_64.Set.cardinal".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter elements : t -> M (list elt).
  Extract Inlined Constant elements => "Targetint_32_64.Set.elements".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter min_elt : t -> M elt.
  Extract Inlined Constant min_elt => "Targetint_32_64.Set.min_elt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter min_elt_opt : t -> M (option elt).
  Extract Inlined Constant min_elt_opt => "Targetint_32_64.Set.min_elt_opt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter max_elt : t -> M elt.
  Extract Inlined Constant max_elt => "Targetint_32_64.Set.max_elt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter max_elt_opt : t -> M (option elt).
  Extract Inlined Constant max_elt_opt => "Targetint_32_64.Set.max_elt_opt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter choose : t -> M elt.
  Extract Inlined Constant choose => "Targetint_32_64.Set.choose".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter choose_opt : t -> M (option elt).
  Extract Inlined Constant choose_opt => "Targetint_32_64.Set.choose_opt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter split : elt -> t -> M (tuple3 t bool t).
  Extract Inlined Constant split => "Targetint_32_64.Set.split".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter find : elt -> t -> M elt.
  Extract Inlined Constant find => "Targetint_32_64.Set.find".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter of_list : list elt -> M t.
  Extract Inlined Constant of_list => "Targetint_32_64.Set.of_list".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter to_seq : t -> Seq.t elt.
  Extract Inlined Constant to_seq => "Targetint_32_64.Set.to_seq".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Targetint_32_64.Set.print".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter to_string : t -> M string.
  Extract Inlined Constant to_string => "Targetint_32_64.Set.to_string".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union_list : list t -> M t.
  Extract Inlined Constant union_list => "Targetint_32_64.Set.union_list".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter get_singleton : t -> M (option elt).
  Extract Inlined Constant get_singleton => "Targetint_32_64.Set.get_singleton".
End Set_.
Module Map.
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Definition key : Type := Targetint_32_64.t.
  Extract Inlined Constant key => "Targetint_32_64.Map.key".
  Module Set_.
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Definition elt : Type := Targetint_32_64.t.
    Extract Inlined Constant elt => "Targetint_32_64.Map.Set.elt".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Definition t : Type := Targetint_32_64.Set_.t.
    Extract Inlined Constant t => "Targetint_32_64.Map.Set.t".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter empty : t.
    Extract Inlined Constant empty => "Targetint_32_64.Map.Set.empty".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter is_empty : t -> M bool.
    Extract Inlined Constant is_empty => "Targetint_32_64.Map.Set.is_empty".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter mem : elt -> t -> M bool.
    Extract Inlined Constant mem => "Targetint_32_64.Map.Set.mem".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter add : elt -> t -> M t.
    Extract Inlined Constant add => "Targetint_32_64.Map.Set.add".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter singleton : elt -> M t.
    Extract Inlined Constant singleton => "Targetint_32_64.Map.Set.singleton".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter remove : elt -> t -> M t.
    Extract Inlined Constant remove => "Targetint_32_64.Map.Set.remove".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter union : t -> t -> M t.
    Extract Inlined Constant union => "Targetint_32_64.Map.Set.union".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter union_sharing : t -> t -> M t.
    Extract Inlined Constant union_sharing => "Targetint_32_64.Map.Set.union_sharing".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter union_shared : t -> t -> M t.
    Extract Inlined Constant union_shared => "Targetint_32_64.Map.Set.union_shared".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter inter : t -> t -> M t.
    Extract Inlined Constant inter => "Targetint_32_64.Map.Set.inter".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter disjoint : t -> t -> M bool.
    Extract Inlined Constant disjoint => "Targetint_32_64.Map.Set.disjoint".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter diff : t -> t -> M t.
    Extract Inlined Constant diff => "Targetint_32_64.Map.Set.diff".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter diff_sharing : t -> t -> M t.
    Extract Inlined Constant diff_sharing => "Targetint_32_64.Map.Set.diff_sharing".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter diff_shared : t -> t -> M t.
    Extract Inlined Constant diff_shared => "Targetint_32_64.Map.Set.diff_shared".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter compare : t -> t -> M int.
    Extract Inlined Constant compare => "Targetint_32_64.Map.Set.compare".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter equal : t -> t -> M bool.
    Extract Inlined Constant equal => "Targetint_32_64.Map.Set.equal".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter subset : t -> t -> M bool.
    Extract Inlined Constant subset => "Targetint_32_64.Map.Set.subset".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter iter : (elt -> M unit) -> t -> M unit.
    Extract Inlined Constant iter => "Targetint_32_64.Map.Set.iter".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter map : (elt -> M elt) -> t -> M t.
    Extract Inlined Constant map => "Targetint_32_64.Map.Set.map".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Inlined Constant fold => "Targetint_32_64.Map.Set.fold".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter for_all : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant for_all => "Targetint_32_64.Map.Set.for_all".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter exists_ : (elt -> M bool) -> t -> M bool.
    Extract Inlined Constant exists_ => "Targetint_32_64.Map.Set.exists".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter filter : (elt -> M bool) -> t -> M t.
    Extract Inlined Constant filter => "Targetint_32_64.Map.Set.filter".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
    Extract Inlined Constant filter_map => "Targetint_32_64.Map.Set.filter_map".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter partition : (elt -> M bool) -> t -> M (t * t).
    Extract Inlined Constant partition => "Targetint_32_64.Map.Set.partition".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter cardinal : t -> M int.
    Extract Inlined Constant cardinal => "Targetint_32_64.Map.Set.cardinal".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter elements : t -> M (list elt).
    Extract Inlined Constant elements => "Targetint_32_64.Map.Set.elements".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter min_elt : t -> M elt.
    Extract Inlined Constant min_elt => "Targetint_32_64.Map.Set.min_elt".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter min_elt_opt : t -> M (option elt).
    Extract Inlined Constant min_elt_opt => "Targetint_32_64.Map.Set.min_elt_opt".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter max_elt : t -> M elt.
    Extract Inlined Constant max_elt => "Targetint_32_64.Map.Set.max_elt".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter max_elt_opt : t -> M (option elt).
    Extract Inlined Constant max_elt_opt => "Targetint_32_64.Map.Set.max_elt_opt".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter choose : t -> M elt.
    Extract Inlined Constant choose => "Targetint_32_64.Map.Set.choose".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter choose_opt : t -> M (option elt).
    Extract Inlined Constant choose_opt => "Targetint_32_64.Map.Set.choose_opt".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter split : elt -> t -> M (tuple3 t bool t).
    Extract Inlined Constant split => "Targetint_32_64.Map.Set.split".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter find : elt -> t -> M elt.
    Extract Inlined Constant find => "Targetint_32_64.Map.Set.find".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter of_list : list elt -> M t.
    Extract Inlined Constant of_list => "Targetint_32_64.Map.Set.of_list".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter to_seq : t -> Seq.t elt.
    Extract Inlined Constant to_seq => "Targetint_32_64.Map.Set.to_seq".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Targetint_32_64.Map.Set.print".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter to_string : t -> M string.
    Extract Inlined Constant to_string => "Targetint_32_64.Map.Set.to_string".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter union_list : list t -> M t.
    Extract Inlined Constant union_list => "Targetint_32_64.Map.Set.union_list".
    (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
    Parameter get_singleton : t -> M (option elt).
    Extract Inlined Constant get_singleton => "Targetint_32_64.Map.Set.get_singleton".
  End Set_.
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Targetint_32_64.Map.t".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Targetint_32_64.Map.empty".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter is_empty : forall {A : Type}, t A -> M bool.
  Extract Inlined Constant is_empty => "Targetint_32_64.Map.is_empty".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter mem : forall {A : Type}, key -> t A -> M bool.
  Extract Inlined Constant mem => "Targetint_32_64.Map.mem".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Targetint_32_64.Map.add".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter update : forall {A : Type}, key -> (option A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant update => "Targetint_32_64.Map.update".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Targetint_32_64.Map.singleton".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter remove : forall {A : Type}, key -> t A -> M (t A).
  Extract Inlined Constant remove => "Targetint_32_64.Map.remove".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter merge : forall {A B C : Type}, (key -> option A -> option B -> M (option C)) -> t A -> t B -> M (t C).
  Extract Inlined Constant merge => "Targetint_32_64.Map.merge".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union => "Targetint_32_64.Map.union".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union_sharing : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_sharing => "Targetint_32_64.Map.union_sharing".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_shared => "Targetint_32_64.Map.union_shared".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union_total : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total => "Targetint_32_64.Map.union_total".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union_total_shared : forall {A : Type}, (key -> A -> A -> M A) -> t A -> t A -> M (t A).
  Extract Inlined Constant union_total_shared => "Targetint_32_64.Map.union_total_shared".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union_left_biased : forall {A : Type}, t A -> t A -> M (t A).
  Extract Inlined Constant union_left_biased => "Targetint_32_64.Map.union_left_biased".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter union_right_biased : forall {A : Type}, t A -> t A -> M (t A).
  Extract Inlined Constant union_right_biased => "Targetint_32_64.Map.union_right_biased".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter update_many : forall {A B : Type}, (key -> option A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant update_many => "Targetint_32_64.Map.update_many".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter compare : forall {A : Type}, (A -> A -> M int) -> t A -> t A -> M int.
  Extract Inlined Constant compare => "Targetint_32_64.Map.compare".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter equal : forall {A : Type}, (A -> A -> M bool) -> t A -> t A -> M bool.
  Extract Inlined Constant equal => "Targetint_32_64.Map.equal".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter iter : forall {A : Type}, (key -> A -> M unit) -> t A -> M unit.
  Extract Inlined Constant iter => "Targetint_32_64.Map.iter".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Targetint_32_64.Map.fold".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant for_all => "Targetint_32_64.Map.for_all".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant exists_ => "Targetint_32_64.Map.exists".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter filter : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A).
  Extract Inlined Constant filter => "Targetint_32_64.Map.filter".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
  Extract Inlined Constant filter_map => "Targetint_32_64.Map.filter_map".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter filter_map_sharing : forall {A : Type}, (key -> A -> M (option A)) -> t A -> M (t A).
  Extract Inlined Constant filter_map_sharing => "Targetint_32_64.Map.filter_map_sharing".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter partition : forall {A : Type}, (key -> A -> M bool) -> t A -> M (t A * t A).
  Extract Inlined Constant partition => "Targetint_32_64.Map.partition".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter cardinal : forall {A : Type}, t A -> M int.
  Extract Inlined Constant cardinal => "Targetint_32_64.Map.cardinal".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter bindings : forall {A : Type}, t A -> M (list (key * A)).
  Extract Inlined Constant bindings => "Targetint_32_64.Map.bindings".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter min_binding : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant min_binding => "Targetint_32_64.Map.min_binding".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter min_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant min_binding_opt => "Targetint_32_64.Map.min_binding_opt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter max_binding : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant max_binding => "Targetint_32_64.Map.max_binding".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter max_binding_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant max_binding_opt => "Targetint_32_64.Map.max_binding_opt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter choose : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant choose => "Targetint_32_64.Map.choose".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter choose_opt : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant choose_opt => "Targetint_32_64.Map.choose_opt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter split : forall {A : Type}, key -> t A -> M (tuple3 (t A) (option A) (t A)).
  Extract Inlined Constant split => "Targetint_32_64.Map.split".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Targetint_32_64.Map.find".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter find_opt : forall {A : Type}, key -> t A -> M (option A).
  Extract Inlined Constant find_opt => "Targetint_32_64.Map.find_opt".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter find_or_null : forall {A : Type}, key -> t A -> M (Or_null.t A).
  Extract Inlined Constant find_or_null => "Targetint_32_64.Map.find_or_null".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter map : forall {A B : Type}, (A -> M B) -> t A -> M (t B).
  Extract Inlined Constant map => "Targetint_32_64.Map.map".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter mapi : forall {A B : Type}, (key -> A -> M B) -> t A -> M (t B).
  Extract Inlined Constant mapi => "Targetint_32_64.Map.mapi".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter to_seq : forall {A : Type}, t A -> Seq.t (key * A).
  Extract Inlined Constant to_seq => "Targetint_32_64.Map.to_seq".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter print_debug : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print_debug => "Targetint_32_64.Map.print_debug".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter of_list : forall {A : Type}, list (key * A) -> M (t A).
  Extract Inlined Constant of_list => "Targetint_32_64.Map.of_list".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter disjoint_union : forall {A : Type}, option (A -> A -> M bool) -> option (Format.formatter -> A -> M unit) -> t A -> t A -> M (t A).
  Extract Inlined Constant disjoint_union => "(fun x__1 x__2 x__3 x__4 -> Targetint_32_64.Map.disjoint_union ?eq:x__1 ?print:x__2 x__3 x__4)".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter map_keys : forall {A : Type}, (key -> M key) -> t A -> M (t A).
  Extract Inlined Constant map_keys => "Targetint_32_64.Map.map_keys".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter keys : forall {A : Type}, t A -> M Targetint_32_64.Map.Set_.t.
  Extract Inlined Constant keys => "Targetint_32_64.Map.keys".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter data : forall {A : Type}, t A -> M (list A).
  Extract Inlined Constant data => "Targetint_32_64.Map.data".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter of_set : forall {A : Type}, (key -> M A) -> Targetint_32_64.Map.Set_.t -> M (t A).
  Extract Inlined Constant of_set => "Targetint_32_64.Map.of_set".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Targetint_32_64.Map.print".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
  Extract Inlined Constant subset_domain => "Targetint_32_64.Map.subset_domain".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter diff_domains : forall {A B : Type}, t A -> t B -> M (t A).
  Extract Inlined Constant diff_domains => "Targetint_32_64.Map.diff_domains".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter inter : forall {A B C : Type}, (key -> A -> B -> M C) -> t A -> t B -> M (t C).
  Extract Inlined Constant inter => "Targetint_32_64.Map.inter".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter diff : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant diff => "Targetint_32_64.Map.diff".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter diff_sharing : forall {A B : Type}, (key -> A -> B -> M (option A)) -> t A -> t B -> M (t A).
  Extract Inlined Constant diff_sharing => "Targetint_32_64.Map.diff_sharing".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter diff_shared : forall {A : Type}, (key -> A -> A -> M (option A)) -> t A -> t A -> M (t A).
  Extract Inlined Constant diff_shared => "Targetint_32_64.Map.diff_shared".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter inter_domain_is_non_empty : forall {A : Type}, t A -> t A -> M bool.
  Extract Inlined Constant inter_domain_is_non_empty => "Targetint_32_64.Map.inter_domain_is_non_empty".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant get_singleton => "Targetint_32_64.Map.get_singleton".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter replace : forall {A : Type}, key -> (A -> M A) -> t A -> M (t A).
  Extract Inlined Constant replace => "Targetint_32_64.Map.replace".
  (* targetint_32_64.mli:217  include Container_types.S with type t := t *)
  Parameter map_sharing : forall {A : Type}, (A -> M A) -> t A -> M (t A).
  Extract Inlined Constant map_sharing => "Targetint_32_64.Map.map_sharing".
End Map.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Targetint_32_64. End Targetint_32_64.
