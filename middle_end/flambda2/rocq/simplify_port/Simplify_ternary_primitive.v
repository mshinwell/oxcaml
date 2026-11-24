(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/simplify_ternary_primitive.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. The functions
   that the interface does not export have their arguments in the order of
   each definition, and an argument that the compiler does not use
   ([~arg2_ty:_]) has here the type of the one call. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Bound_var Debuginfo Or_bottom Simple
  Simplify_common Target_ocaml_int.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda_primitive.t Or_bottom.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 17-62. In the compiler: [array_kind array_set_kind dacc ~original_term dbg
   ~arg1:array ~arg1_ty:array_ty ~arg2:index ~arg2_ty:_ ~arg3:new_value
   ~arg3_ty:_ ~result_var]. *)
Definition simplify_array_set (array_kind : P.Array_kind.t)
    (array_set_kind : P.Array_set_kind.t) (dacc : DA.t)
    (original_term : Named.t) (dbg : Debuginfo.t) (array : Simple.t)
    (array_ty : T.t) (index : Simple.t) (_ : T.t) (new_value : Simple.t)
    (_ : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let& orig_array_kind := array_kind in
  let* array_kind :=
    Simplify_common.specialise_array_kind dacc array_kind array_ty
  in
  match array_kind with
  | Or_bottom.Bottom => SPR.create_invalid dacc
  | Or_bottom.Ok array_kind =>
    (* 28-49 *)
    (match array_kind with
     | P.Array_kind.Immediates | P.Array_kind.Gc_ignorable_values => ret tt
     | P.Array_kind.Values =>
       match array_set_kind with
       | P.Array_set_kind.Values _ => ret tt
       | P.Array_set_kind.Immediates | P.Array_set_kind.Gc_ignorable_values
       (* We don't expect specialisation regressions from Immediates to
          Values. *)
       | P.Array_set_kind.Naked_floats | P.Array_set_kind.Naked_float32s
       | P.Array_set_kind.Naked_ints | P.Array_set_kind.Naked_int8s
       | P.Array_set_kind.Naked_int16s | P.Array_set_kind.Naked_int32s
       | P.Array_set_kind.Naked_int64s | P.Array_set_kind.Naked_nativeints
       | P.Array_set_kind.Naked_vec128s | P.Array_set_kind.Naked_vec256s
       | P.Array_set_kind.Naked_vec512s | P.Array_set_kind.Naked_masks =>
         fatal_errorf8
           "Didn't expect array specialisation to yield array kind %a from array set kind %a (original array kind %a):@ %a"
           P.Array_kind.print array_kind P.Array_set_kind.print
           array_set_kind P.Array_kind.print orig_array_kind Named.print
           original_term
       end
     | P.Array_kind.Naked_floats | P.Array_kind.Naked_float32s
     | P.Array_kind.Naked_ints | P.Array_kind.Naked_int8s
     | P.Array_kind.Naked_int16s | P.Array_kind.Naked_int32s
     | P.Array_kind.Naked_int64s | P.Array_kind.Naked_nativeints
     | P.Array_kind.Naked_vec128s | P.Array_kind.Naked_vec256s
     | P.Array_kind.Naked_vec512s | P.Array_kind.Naked_masks
     | P.Array_kind.Unboxed_product _ =>
       ret tt
     end) ;;
    (* 50-62 *)
    let* named :=
      Named.create_prim
        (P.Ternary (P.Array_set array_kind array_set_kind) array index
           new_value)
        dbg
    in
    let* machine_width :=
      let! tmp1 := DA.denv dacc in
      DE.machine_width tmp1
    in
    let* unit_ty :=
      let! tmp1 := Target_ocaml_int.zero machine_width in
      Flambda2_types.this_tagged_immediate tmp1
    in
    let* dacc := DA.add_variable dacc result_var unit_ty in
    SPR.create named false dacc
  end.

(* 64-67. In the compiler: [_bytes_like_value _string_accessor_width dacc
   ~original_term _dbg ~arg1:_ ~arg1_ty:_ ~arg2:_ ~arg2_ty:_ ~arg3:_
   ~arg3_ty:_ ~result_var]. *)
Definition simplify_bytes_or_bigstring_set
    (_bytes_like_value : P.bytes_like_value)
    (_string_accessor_width : P.string_accessor_width) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unit dacc result_var original_term.

(* 69-72. In the compiler: [~num_dimensions:_ _bigarray_kind _bigarray_layout
   dacc ~original_term _dbg ~arg1:_ ...]. *)
Definition simplify_bigarray_set (_ : P.num_dimensions)
    (_bigarray_kind : P.Bigarray_kind.t)
    (_bigarray_layout : P.Bigarray_layout.t) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unit dacc result_var original_term.

(* 74-79. In the compiler: [(_op : P.int_atomic_op) ~original_prim dacc
   ~original_term _dbg ~arg1:_ ...]. *)
Definition simplify_atomic_int_arith (_op : P.int_atomic_op)
    (original_prim : P.t) (dacc : DA.t) (original_term : Named.t)
    (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 81-85 *)
Definition simplify_atomic_set (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 87-91 *)
Definition simplify_atomic_exchange (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 93-97 *)
Definition simplify_write_offset (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 99-116 *)
Definition simplify_ternary_primitive (dacc : DA.t) (original_prim : P.t)
    (prim : P.ternary_primitive) (arg1 : Simple.t) (arg1_ty : T.t)
    (arg2 : Simple.t) (arg2_ty : T.t) (arg3 : Simple.t) (arg3_ty : T.t)
    (dbg : Debuginfo.t) (result_var : Bound_var.t) : M SPR.t :=
  let* original_term := Named.create_prim original_prim dbg in
  (* 102-114: a function of this file with its first arguments is a value
     (no call is made until [simplifier] has all its arguments). *)
  let& simplifier :=
    match prim with
    | P.Array_set array_kind width => simplify_array_set array_kind width
    | P.Bytes_or_bigstring_set bytes_like_value string_accessor_width =>
      simplify_bytes_or_bigstring_set bytes_like_value string_accessor_width
    | P.Bigarray_set num_dimensions bigarray_kind bigarray_layout =>
      simplify_bigarray_set num_dimensions bigarray_kind bigarray_layout
    | P.Atomic_int_arith _ op => simplify_atomic_int_arith op original_prim
    | P.Atomic_set _ _ _ => simplify_atomic_set original_prim
    | P.Atomic_exchange _ _ _ => simplify_atomic_exchange original_prim
    | P.Write_offset _ _ _ => simplify_write_offset original_prim
    end
  in
  simplifier dacc original_term dbg arg1 arg1_ty arg2 arg2_ty arg3 arg3_ty
    result_var.
