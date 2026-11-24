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
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Stdlib_ Target_system Targetint_32_64.

(* target_ocaml_int.mli:21  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Target_ocaml_int.t".
Module T.
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Definition t : Type := Target_ocaml_int.t.
  Extract Inlined Constant t => "Target_ocaml_int.T.t".
End T.
(* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
Parameter equal : Target_ocaml_int.T.t -> Target_ocaml_int.T.t -> M bool.
Extract Inlined Constant equal => "Target_ocaml_int.equal".
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
  Parameter add : elt -> t -> M t.
  Extract Inlined Constant add => "Target_ocaml_int.Set.add".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter singleton : elt -> M t.
  Extract Inlined Constant singleton => "Target_ocaml_int.Set.singleton".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "Target_ocaml_int.Set.fold".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter filter_map : (elt -> M (option elt)) -> t -> M t.
  Extract Inlined Constant filter_map => "Target_ocaml_int.Set.filter_map".
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
    Definition t : Type := Target_ocaml_int.Set_.t.
    Extract Inlined Constant t => "Target_ocaml_int.Map.Set.t".
  End Set_.
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Target_ocaml_int.Map.t".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Target_ocaml_int.Map.empty".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Target_ocaml_int.Map.add".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter singleton : forall {A : Type}, key -> A -> M (t A).
  Extract Inlined Constant singleton => "Target_ocaml_int.Map.singleton".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter fold : forall {A B : Type}, (key -> A -> B -> M B) -> t A -> B -> M B.
  Extract Inlined Constant fold => "Target_ocaml_int.Map.fold".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter for_all : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant for_all => "Target_ocaml_int.Map.for_all".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter filter_map : forall {A B : Type}, (key -> A -> M (option B)) -> t A -> M (t B).
  Extract Inlined Constant filter_map => "Target_ocaml_int.Map.filter_map".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter cardinal : forall {A : Type}, t A -> M int.
  Extract Inlined Constant cardinal => "Target_ocaml_int.Map.cardinal".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter min_binding : forall {A : Type}, t A -> M (key * A).
  Extract Inlined Constant min_binding => "Target_ocaml_int.Map.min_binding".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter of_set : forall {A : Type}, (key -> M A) -> Target_ocaml_int.Map.Set_.t -> M (t A).
  Extract Inlined Constant of_set => "Target_ocaml_int.Map.of_set".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter subset_domain : forall {A B : Type}, t A -> t B -> M bool.
  Extract Inlined Constant subset_domain => "Target_ocaml_int.Map.subset_domain".
  (* target_ocaml_int.mli:23  include Container_types.S with type t := t *)
  Parameter get_singleton : forall {A : Type}, t A -> M (option (key * A)).
  Extract Inlined Constant get_singleton => "Target_ocaml_int.Map.get_singleton".
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
(* target_ocaml_int.mli:155  val mod_ : t -> t -> t *)
Parameter mod_ : t -> t -> M t.
Extract Inlined Constant mod_ => "Target_ocaml_int.mod_".
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
