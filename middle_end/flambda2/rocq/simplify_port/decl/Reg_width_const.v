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
   Simplify uses of the compiler's module [Reg_width_const], after its interface
   middle_end/flambda2/identifiers/reg_width_const.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_kind Format Int32 Int64 Int_ids Numeric_types Stdlib_ Target_ocaml_int Target_system Targetint_32_64 Vector_types.

(* int_ids.mli:22  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Const.t.
Extract Inlined Constant t => "Reg_width_const.t".
(* module T = Int_ids.Const.T: declared again here under this name. *)
Module T.
  (* int_ids.mli:26  include Container_types.S with type t := t *)
  Definition t : Type := Int_ids.Const.T.t.
  Extract Inlined Constant t => "Reg_width_const.T.t".
End T.
(* int_ids.mli:26  include Container_types.S with type t := t *)
Parameter equal : Reg_width_const.T.t -> Reg_width_const.T.t -> M bool.
Extract Inlined Constant equal => "Reg_width_const.equal".
(* int_ids.mli:26  include Container_types.S with type t := t *)
Parameter hash : Reg_width_const.T.t -> M int.
Extract Inlined Constant hash => "Reg_width_const.hash".
(* int_ids.mli:26  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Reg_width_const.T.t -> M unit.
Extract Inlined Constant print => "Reg_width_const.print".
(* int_ids.mli:38  val untagged_const_int : Target_ocaml_int.t -> t *)
Parameter untagged_const_int : Target_ocaml_int.t -> M t.
Extract Inlined Constant untagged_const_int => "Reg_width_const.untagged_const_int".
(* int_ids.mli:40  val const_zero : Target_system.Machine_width.t -> t *)
Parameter const_zero : Target_system.Machine_width.t -> M t.
Extract Inlined Constant const_zero => "Reg_width_const.const_zero".
(* int_ids.mli:50  val const_poison : Flambda_kind.t -> string -> t *)
Parameter const_poison : Flambda_kind.t -> string -> M t.
Extract Inlined Constant const_poison => "Reg_width_const.const_poison".
(* int_ids.mli:55  val naked_immediate : Target_ocaml_int.t -> t *)
Parameter naked_immediate : Target_ocaml_int.t -> M t.
Extract Inlined Constant naked_immediate => "Reg_width_const.naked_immediate".
(* int_ids.mli:57  val tagged_immediate : Target_ocaml_int.t -> t *)
Parameter tagged_immediate : Target_ocaml_int.t -> M t.
Extract Inlined Constant tagged_immediate => "Reg_width_const.tagged_immediate".
(* int_ids.mli:59  val naked_float32 : Numeric_types.Float32_by_bit_pattern.t -> t *)
Parameter naked_float32 : Numeric_types.Float32_by_bit_pattern.t -> M t.
Extract Inlined Constant naked_float32 => "Reg_width_const.naked_float32".
(* int_ids.mli:61  val naked_float : Numeric_types.Float_by_bit_pattern.t -> t *)
Parameter naked_float : Numeric_types.Float_by_bit_pattern.t -> M t.
Extract Inlined Constant naked_float => "Reg_width_const.naked_float".
(* int_ids.mli:63  val naked_int8 : Numeric_types.Int8.t -> t *)
Parameter naked_int8 : Numeric_types.Int8.t -> M t.
Extract Inlined Constant naked_int8 => "Reg_width_const.naked_int8".
(* int_ids.mli:65  val naked_int16 : Numeric_types.Int16.t -> t *)
Parameter naked_int16 : Numeric_types.Int16.t -> M t.
Extract Inlined Constant naked_int16 => "Reg_width_const.naked_int16".
(* int_ids.mli:67  val naked_int32 : Int32.t -> t *)
Parameter naked_int32 : Int32.t -> M t.
Extract Inlined Constant naked_int32 => "Reg_width_const.naked_int32".
(* int_ids.mli:69  val naked_int64 : Int64.t -> t *)
Parameter naked_int64 : Int64.t -> M t.
Extract Inlined Constant naked_int64 => "Reg_width_const.naked_int64".
(* int_ids.mli:71  val naked_nativeint : Targetint_32_64.t -> t *)
Parameter naked_nativeint : Targetint_32_64.t -> M t.
Extract Inlined Constant naked_nativeint => "Reg_width_const.naked_nativeint".
(* module Descr = Int_ids.Const.Descr: declared again here under this name. *)
Module Descr.
  (* int_ids.mli:82  type t = private | Naked_immediate of Target_ocaml_int.t | Tagged_immediate of Target_ocaml_int.t | Naked_float32 of Numeric_types.Float32_by_bit_pattern.t | Naked_float of Numeric_types.Float_by_bit_pattern.t | Naked_int8 of Numeric_types.Int8.t | Naked_int16 of Numeric_types.Int16.t | Naked_int32 of Int32.t | Naked_int64 of Int64.t | Naked_nativeint of Targetint_32_64.t | Naked_vec128 of Vect... *)
  Definition t : Type := Int_ids.Const.Descr.t.
  Extract Inlined Constant t => "Reg_width_const.Descr.t".
End Descr.
(* int_ids.mli:102  val descr : t -> Descr.t *)
Parameter descr : t -> M Reg_width_const.Descr.t.
Extract Inlined Constant descr => "Reg_width_const.descr".
(* reg_width_const.mli:27  val is_naked_immediate : t -> Target_ocaml_int.t option *)
Parameter is_naked_immediate : t -> M (option Target_ocaml_int.t).
Extract Inlined Constant is_naked_immediate => "Reg_width_const.is_naked_immediate".
(* reg_width_const.mli:29  val is_tagged_immediate : t -> Target_ocaml_int.t option *)
Parameter is_tagged_immediate : t -> M (option Target_ocaml_int.t).
Extract Inlined Constant is_tagged_immediate => "Reg_width_const.is_tagged_immediate".
(* reg_width_const.mli:31  val is_naked_float32 : t -> Numeric_types.Float32_by_bit_pattern.t option *)
Parameter is_naked_float32 : t -> M (option Numeric_types.Float32_by_bit_pattern.t).
Extract Inlined Constant is_naked_float32 => "Reg_width_const.is_naked_float32".
(* reg_width_const.mli:33  val is_naked_float : t -> Numeric_types.Float_by_bit_pattern.t option *)
Parameter is_naked_float : t -> M (option Numeric_types.Float_by_bit_pattern.t).
Extract Inlined Constant is_naked_float => "Reg_width_const.is_naked_float".
(* reg_width_const.mli:35  val is_naked_int8 : t -> Numeric_types.Int8.t option *)
Parameter is_naked_int8 : t -> M (option Numeric_types.Int8.t).
Extract Inlined Constant is_naked_int8 => "Reg_width_const.is_naked_int8".
(* reg_width_const.mli:37  val is_naked_int16 : t -> Numeric_types.Int16.t option *)
Parameter is_naked_int16 : t -> M (option Numeric_types.Int16.t).
Extract Inlined Constant is_naked_int16 => "Reg_width_const.is_naked_int16".
(* reg_width_const.mli:39  val is_naked_int32 : t -> int32 option *)
Parameter is_naked_int32 : t -> M (option Stdlib_.int32).
Extract Inlined Constant is_naked_int32 => "Reg_width_const.is_naked_int32".
(* reg_width_const.mli:41  val is_naked_int64 : t -> int64 option *)
Parameter is_naked_int64 : t -> M (option Stdlib_.int64).
Extract Inlined Constant is_naked_int64 => "Reg_width_const.is_naked_int64".
(* reg_width_const.mli:43  val is_naked_nativeint : t -> Targetint_32_64.t option *)
Parameter is_naked_nativeint : t -> M (option Targetint_32_64.t).
Extract Inlined Constant is_naked_nativeint => "Reg_width_const.is_naked_nativeint".
(* reg_width_const.mli:45  val is_naked_vec128 : t -> Vector_types.Vec128.Bit_pattern.t option *)
Parameter is_naked_vec128 : t -> M (option Vector_types.Vec128.Bit_pattern.t).
Extract Inlined Constant is_naked_vec128 => "Reg_width_const.is_naked_vec128".
(* reg_width_const.mli:47  val is_naked_vec256 : t -> Vector_types.Vec256.Bit_pattern.t option *)
Parameter is_naked_vec256 : t -> M (option Vector_types.Vec256.Bit_pattern.t).
Extract Inlined Constant is_naked_vec256 => "Reg_width_const.is_naked_vec256".
(* reg_width_const.mli:49  val is_naked_vec512 : t -> Vector_types.Vec512.Bit_pattern.t option *)
Parameter is_naked_vec512 : t -> M (option Vector_types.Vec512.Bit_pattern.t).
Extract Inlined Constant is_naked_vec512 => "Reg_width_const.is_naked_vec512".
(* reg_width_const.mli:51  val is_naked_mask : t -> Vector_types.Mask.Bit_pattern.t option *)
Parameter is_naked_mask : t -> M (option Vector_types.Mask.Bit_pattern.t).
Extract Inlined Constant is_naked_mask => "Reg_width_const.is_naked_mask".
(* reg_width_const.mli:53  val is_poison : t -> (Flambda_kind.t * string) option *)
Parameter is_poison : t -> M (option (Flambda_kind.t * string)).
Extract Inlined Constant is_poison => "Reg_width_const.is_poison".
(* reg_width_const.mli:57  val of_int_of_kind : Target_system.Machine_width.t -> Flambda_kind.t -> int -> t *)
Parameter of_int_of_kind : Target_system.Machine_width.t -> Flambda_kind.t -> int -> M t.
Extract Inlined Constant of_int_of_kind => "Reg_width_const.of_int_of_kind".
(* reg_width_const.mli:59  val kind : t -> Flambda_kind.t *)
Parameter kind : t -> M Flambda_kind.t.
Extract Inlined Constant kind => "Reg_width_const.kind".
