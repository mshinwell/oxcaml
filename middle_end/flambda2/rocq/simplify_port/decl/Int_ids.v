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
   Simplify uses of the compiler's module [Int_ids], after its interface
   middle_end/flambda2/identifiers/int_ids.mli
   (Git blob 02934d8c25979ff3dccc8c9e18821e9f37dab407). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_kind Int32 Int64 Numeric_types Or_infinity Target_ocaml_int Targetint_32_64 Vector_types.

Module Const.
  (* int_ids.mli:22  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Const.t".
  Module T.
    (* int_ids.mli:26  include Container_types.S with type t := t *)
    Definition t : Type := Int_ids.Const.t.
    Extract Inlined Constant t => "Int_ids.Const.T.t".
  End T.
  Module Descr.
    (* int_ids.mli:82  type t = private | Naked_immediate of Target_ocaml_int.t | Tagged_immediate of Target_ocaml_int.t | Naked_float32 of Numeric_types.Float32_by_bit_pattern.t | Naked_float of Numeric_types.Float_by_bit_pattern.t | Naked_int8 of Numeric_types.Int8.t | Naked_int16 of Numeric_types.Int16.t | Naked_int32 of Int32.t | Naked_int64 of Int64.t | Naked_nativeint of Targetint_32_64.t | Naked_vec128 of Vect... *)
    Inductive t : Type :=
    | Naked_immediate : Target_ocaml_int.t -> t
    | Tagged_immediate : Target_ocaml_int.t -> t
    | Naked_float32 : Numeric_types.Float32_by_bit_pattern.t -> t
    | Naked_float : Numeric_types.Float_by_bit_pattern.t -> t
    | Naked_int8 : Numeric_types.Int8.t -> t
    | Naked_int16 : Numeric_types.Int16.t -> t
    | Naked_int32 : Int32.t -> t
    | Naked_int64 : Int64.t -> t
    | Naked_nativeint : Targetint_32_64.t -> t
    | Naked_vec128 : Vector_types.Vec128.Bit_pattern.t -> t
    | Naked_vec256 : Vector_types.Vec256.Bit_pattern.t -> t
    | Naked_vec512 : Vector_types.Vec512.Bit_pattern.t -> t
    | Naked_mask : Vector_types.Mask.Bit_pattern.t -> t
    | Null : t
    | Poison : Flambda_kind.t -> string -> t.
    Extract Inductive t => "Int_ids.Const.Descr.t" [ "Int_ids.Const.Descr.Naked_immediate" "Int_ids.Const.Descr.Tagged_immediate" "Int_ids.Const.Descr.Naked_float32" "Int_ids.Const.Descr.Naked_float" "Int_ids.Const.Descr.Naked_int8" "Int_ids.Const.Descr.Naked_int16" "Int_ids.Const.Descr.Naked_int32" "Int_ids.Const.Descr.Naked_int64" "Int_ids.Const.Descr.Naked_nativeint" "Int_ids.Const.Descr.Naked_vec128" "Int_ids.Const.Descr.Naked_vec256" "Int_ids.Const.Descr.Naked_vec512" "Int_ids.Const.Descr.Naked_mask" "Int_ids.Const.Descr.Null" "Int_ids.Const.Descr.Poison" ].
  End Descr.
End Const.
Module Variable_.
  (* int_ids.mli:110  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Variable.t".
  Module T.
    (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
    Definition t : Type := Int_ids.Variable_.t.
    Extract Inlined Constant t => "Int_ids.Variable.T.t".
  End T.
  Module Set_.
    (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
    Definition elt : Type := Int_ids.Variable_.t.
    Extract Inlined Constant elt => "Int_ids.Variable.Set.elt".
    (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Int_ids.Variable.Set.t".
  End Set_.
  Module Map.
    (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
    Definition key : Type := Int_ids.Variable_.t.
    Extract Inlined Constant key => "Int_ids.Variable.Map.key".
    (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Variable.Map.t".
  End Map.
  Module Lmap.
    (* int_ids.mli:116  module Lmap : Lmap.S with type key := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Variable.Lmap.t".
  End Lmap.
End Variable_.
Module Symbol.
  (* int_ids.mli:145  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Symbol.t".
  Module T.
    (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
    Definition t : Type := Int_ids.Symbol.t.
    Extract Inlined Constant t => "Int_ids.Symbol.T.t".
  End T.
  Module Set_.
    (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
    Definition elt : Type := Int_ids.Symbol.t.
    Extract Inlined Constant elt => "Int_ids.Symbol.Set.elt".
    (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Int_ids.Symbol.Set.t".
  End Set_.
  Module Map.
    (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
    Definition key : Type := Int_ids.Symbol.t.
    Extract Inlined Constant key => "Int_ids.Symbol.Map.key".
    Module Set_.
      (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
      Definition t : Type := Int_ids.Symbol.Set_.t.
      Extract Inlined Constant t => "Int_ids.Symbol.Map.Set.t".
    End Set_.
    (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Symbol.Map.t".
  End Map.
End Symbol.
Module Name.
  (* int_ids.mli:176  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Name.t".
  Module T.
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Definition t : Type := Int_ids.Name.t.
    Extract Inlined Constant t => "Int_ids.Name.T.t".
  End T.
  Module Set_.
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Definition elt : Type := Int_ids.Name.t.
    Extract Inlined Constant elt => "Int_ids.Name.Set.elt".
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Int_ids.Name.Set.t".
  End Set_.
  Module Map.
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Definition key : Type := Int_ids.Name.t.
    Extract Inlined Constant key => "Int_ids.Name.Map.key".
    Module Set_.
      (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
      Definition elt : Type := Int_ids.Name.t.
      Extract Inlined Constant elt => "Int_ids.Name.Map.Set.elt".
      (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
      Definition t : Type := Int_ids.Name.Set_.t.
      Extract Inlined Constant t => "Int_ids.Name.Map.Set.t".
    End Set_.
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Name.Map.t".
  End Map.
End Name.
Module Rec_info_expr.
  (* int_ids.mli:192  module Rec_info_expr : Rec_info_expr0.S with type variable = Variable.t *)
  Definition variable : Type := Int_ids.Variable_.t.
  Extract Inlined Constant variable => "Int_ids.Rec_info_expr.variable".
  Module Unrolling_state.
    (* rec_info_expr0.mli:23  type t = private | Not_unrolling ( ** Unrolling has not begun. * ) | Unrolling of { remaining_depth : int } ( ** Unrolling has begun and will continue until [remaining_depth] is zero. A subsequent [unroll_to] expression may increase the remaining depth. * ) | Do_not_unroll ( ** No unrolling may occur. [unroll_to] has no effect. * ) *)
    Inductive t : Type :=
    | Not_unrolling : t
    | Unrolling : int -> t
    | Do_not_unroll : t.
    Extract Inductive t => "Int_ids.Rec_info_expr.Unrolling_state.t" [ "Int_ids.Rec_info_expr.Unrolling_state.Not_unrolling" "(fun x__1 -> (Int_ids.Rec_info_expr.Unrolling_state.Unrolling { remaining_depth = x__1 } : Int_ids.Rec_info_expr.Unrolling_state.t))" "Int_ids.Rec_info_expr.Unrolling_state.Do_not_unroll" ] "(fun f__1 f__2 f__3 x__0 -> match (x__0 : Int_ids.Rec_info_expr.Unrolling_state.t) with Int_ids.Rec_info_expr.Unrolling_state.Not_unrolling -> f__1 () | Int_ids.Rec_info_expr.Unrolling_state.Unrolling { remaining_depth = x__1 } -> f__2 x__1 | Int_ids.Rec_info_expr.Unrolling_state.Do_not_unroll -> f__3 ())".
  End Unrolling_state.
  (* rec_info_expr0.mli:46  type t = private | Const of { depth : int Or_infinity.t; unrolling : Unrolling_state.t } | Var of variable ( ** A variable of kind [Flambda_kind.rec_info]. * ) | Succ of t ( ** The next depth. If we inline an occurrence with depth [d], then in the inlined body, recursive references will have depth [succ d]. * ) | Unroll_to of int * t *)
  Inductive t : Type :=
  | Const : Or_infinity.t int -> Int_ids.Rec_info_expr.Unrolling_state.t -> t
  | Var : variable -> t
  | Succ : t -> t
  | Unroll_to : int -> t -> t.
  Extract Inductive t => "Int_ids.Rec_info_expr.t" [ "(fun (x__1, x__2) -> (Int_ids.Rec_info_expr.Const { depth = x__1; unrolling = x__2 } : Int_ids.Rec_info_expr.t))" "Int_ids.Rec_info_expr.Var" "Int_ids.Rec_info_expr.Succ" "Int_ids.Rec_info_expr.Unroll_to" ] "(fun f__1 f__2 f__3 f__4 x__0 -> match (x__0 : Int_ids.Rec_info_expr.t) with Int_ids.Rec_info_expr.Const { depth = x__1; unrolling = x__2 } -> f__1 x__1 x__2 | Int_ids.Rec_info_expr.Var x__1 -> f__2 x__1 | Int_ids.Rec_info_expr.Succ x__1 -> f__3 x__1 | Int_ids.Rec_info_expr.Unroll_to (x__1, x__2) -> f__4 x__1 x__2)".
End Rec_info_expr.
Module Coercion.
  (* int_ids.mli:197  and type rec_info_expr = Rec_info_expr.t *)
  Definition rec_info_expr : Type := Int_ids.Rec_info_expr.t.
  Extract Inlined Constant rec_info_expr => "Int_ids.Coercion.rec_info_expr".
  (* coercion0.mli:37  type t = private | Id | Change_depth of { from : rec_info_expr; to_ : rec_info_expr } *)
  Inductive t : Type :=
  | Id : t
  | Change_depth : rec_info_expr -> rec_info_expr -> t.
  Extract Inductive t => "Int_ids.Coercion.t" [ "Int_ids.Coercion.Id" "(fun (x__1, x__2) -> (Int_ids.Coercion.Change_depth { from = x__1; to_ = x__2 } : Int_ids.Coercion.t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Int_ids.Coercion.t) with Int_ids.Coercion.Id -> f__1 () | Int_ids.Coercion.Change_depth { from = x__1; to_ = x__2 } -> f__2 x__1 x__2)".
End Coercion.
Module Simple.
  (* int_ids.mli:200  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Simple.t".
  Module T.
    (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
    Definition t : Type := Int_ids.Simple.t.
    Extract Inlined Constant t => "Int_ids.Simple.T.t".
  End T.
  Module Set_.
    (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
    Definition elt : Type := Int_ids.Simple.t.
    Extract Inlined Constant elt => "Int_ids.Simple.Set.elt".
    (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Int_ids.Simple.Set.t".
  End Set_.
  Module Map.
    (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
    Definition key : Type := Int_ids.Simple.t.
    Extract Inlined Constant key => "Int_ids.Simple.Map.key".
    Module Set_.
      (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
      Definition t : Type := Int_ids.Simple.Set_.t.
      Extract Inlined Constant t => "Int_ids.Simple.Map.Set.t".
    End Set_.
    (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Simple.Map.t".
  End Map.
End Simple.
Module Code_id.
  (* int_ids.mli:247  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Code_id.t".
  Module T.
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Definition t : Type := Int_ids.Code_id.t.
    Extract Inlined Constant t => "Int_ids.Code_id.T.t".
  End T.
  Module Set_.
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Definition elt : Type := Int_ids.Code_id.t.
    Extract Inlined Constant elt => "Int_ids.Code_id.Set.elt".
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Int_ids.Code_id.Set.t".
  End Set_.
  Module Map.
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Definition key : Type := Int_ids.Code_id.t.
    Extract Inlined Constant key => "Int_ids.Code_id.Map.key".
    Module Set_.
      (* int_ids.mli:251  include Container_types.S with type t := t *)
      Definition elt : Type := Int_ids.Code_id.t.
      Extract Inlined Constant elt => "Int_ids.Code_id.Map.Set.elt".
      (* int_ids.mli:251  include Container_types.S with type t := t *)
      Definition t : Type := Int_ids.Code_id.Set_.t.
      Extract Inlined Constant t => "Int_ids.Code_id.Map.Set.t".
    End Set_.
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Code_id.Map.t".
  End Map.
End Code_id.
Module Code_id_or_symbol.
  (* int_ids.mli:281  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Code_id_or_symbol.t".
  Module Set_.
    (* int_ids.mli:283  include Container_types.S with type t := t *)
    Definition elt : Type := Int_ids.Code_id_or_symbol.t.
    Extract Inlined Constant elt => "Int_ids.Code_id_or_symbol.Set.elt".
    (* int_ids.mli:283  include Container_types.S with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Int_ids.Code_id_or_symbol.Set.t".
  End Set_.
  Module Map.
    (* int_ids.mli:283  include Container_types.S with type t := t *)
    Definition key : Type := Int_ids.Code_id_or_symbol.t.
    Extract Inlined Constant key => "Int_ids.Code_id_or_symbol.Map.key".
    (* int_ids.mli:283  include Container_types.S with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Code_id_or_symbol.Map.t".
  End Map.
  Module Lmap.
    (* int_ids.mli:285  module Lmap : Lmap.S with type key = t *)
    Definition key : Type := Int_ids.Code_id_or_symbol.t.
    Extract Inlined Constant key => "Int_ids.Code_id_or_symbol.Lmap.key".
    (* lmap.mli:48  type +'a t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Code_id_or_symbol.Lmap.t".
  End Lmap.
End Code_id_or_symbol.

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Int_ids. End Int_ids.
