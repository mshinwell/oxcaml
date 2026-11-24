(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Aspen Smith, Jane Street, New York                   *)
(*                                                                        *)
(*   Copyright 2025 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows
   middle_end/flambda2/simplify/simplify_quaternary_primitive.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order) is that of GUIDE.md. The compiler's file has no
   interface: the arguments are in the order of each definition, and an
   argument that the compiler does not use ([~original_prim:_]) has here the
   type of the one call. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Bound_var Debuginfo Simple.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda2_types.proof_of_property
   Flambda_primitive.quaternary_primitive Flambda_primitive.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 17-43 *)
Definition simplify_atomic_compare_and_set_or_exchange_args
    (args_kind : P.Block_access_field_kind.t) (dacc : DA.t)
    (comparison_value_ty new_value_ty : T.t)
    : M P.Block_access_field_kind.t :=
  match args_kind with
  | P.Block_access_field_kind.Immediate =>
    (* No further specialization can be done *)
    ret P.Block_access_field_kind.Immediate
  | P.Block_access_field_kind.Any_value =>
    (* Unlike (for example) a normal write to a block, these primitives can be
       specialized based on the observed types of the arguments. (In the case of
       compare-exchange information can also be propagated based on the result
       type; see below.)

       For example for [Atomic_compare_and_set], observe that if both the second
       and third arguments (value with which to compare, and new value,
       respectively) are immediate, then there is no need to generate a GC
       barrier -- not only because the new value is immediate, but crucially
       also because the old value cannot be a pointer if the operation is to
       perform a write. *)
    (* 36-40 *)
    let& is_immediate :=
      fun (ty : T.t) =>
      let! tmp1 := DA.typing_env dacc in
      let! tmp2 := T.prove_is_not_a_pointer tmp1 ty in
      match tmp2 with
      | T.Proved true => ret true
      | T.Proved false | T.Unknown => ret false
      end
    in
    (* 41-43 *)
    let! tmp1 := is_immediate comparison_value_ty in
    let! tmp2 := and_then tmp1 (is_immediate new_value_ty) in
    if tmp2
    then ret P.Block_access_field_kind.Immediate
    else ret P.Block_access_field_kind.Any_value
  end.

(* 45-68. In the compiler: [offset_units args_kind mode ~original_prim:_ dacc
   ~original_term:_ dbg ~arg1:atomic ~arg1_ty:_ ~arg2:field ~arg2_ty:_
   ~arg3:expected ~arg3_ty:comparison_value_ty ~arg4:desired
   ~arg4_ty:new_value_ty ~result_var]. *)
Definition simplify_atomic_compare_and_set
    (offset_units : P.atomic_offset_units)
    (args_kind : P.Block_access_field_kind.t)
    (mode : Alloc_mode.For_assignments.t) (_ : P.t) (dacc : DA.t)
    (_ : Named.t) (dbg : Debuginfo.t) (atomic : Simple.t) (_ : T.t)
    (field : Simple.t) (_ : T.t) (expected : Simple.t)
    (comparison_value_ty : T.t) (desired : Simple.t) (new_value_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* args_kind :=
    simplify_atomic_compare_and_set_or_exchange_args args_kind dacc
      comparison_value_ty new_value_ty
  in
  let* new_term :=
    Named.create_prim
      (P.Quaternary
         (P.Atomic_compare_and_set offset_units args_kind mode)
         atomic field expected desired)
      dbg
  in
  let* dacc :=
    let! tmp1 := DA.denv dacc in
    let! tmp2 := DE.machine_width tmp1 in
    let! tmp3 := T.any_tagged_bool tmp2 in
    DA.add_variable dacc result_var tmp3
  in
  SPR.create new_term false dacc.

(* 70-96. In the compiler: [offset_units ~atomic_kind ~args_kind ~mode
   ~original_prim:_ dacc ~original_term:_ dbg ~arg1:atomic ~arg1_ty:_
   ~arg2:field ~arg2_ty:_ ~arg3:expected ~arg3_ty:comparison_value_ty
   ~arg4:desired ~arg4_ty:new_value_ty ~result_var]. *)
Definition simplify_atomic_compare_exchange
    (offset_units : P.atomic_offset_units)
    (atomic_kind args_kind : P.Block_access_field_kind.t)
    (mode : Alloc_mode.For_assignments.t) (_ : P.t) (dacc : DA.t)
    (_ : Named.t) (dbg : Debuginfo.t) (atomic : Simple.t) (_ : T.t)
    (field : Simple.t) (_ : T.t) (expected : Simple.t)
    (comparison_value_ty : T.t) (desired : Simple.t) (new_value_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* args_kind :=
    simplify_atomic_compare_and_set_or_exchange_args args_kind dacc
      comparison_value_ty new_value_ty
  in
  let* new_term :=
    Named.create_prim
      (P.Quaternary
         (P.Atomic_compare_exchange offset_units atomic_kind args_kind mode)
         atomic field expected desired)
      dbg
  in
  let& result_var_ty :=
    match atomic_kind with
    | P.Block_access_field_kind.Immediate => T.any_tagged_immediate_or_null
    | P.Block_access_field_kind.Any_value => T.any_value
    end
  in
  let* dacc := DA.add_variable dacc result_var result_var_ty in
  SPR.create new_term false dacc.

(* 98-112 *)
Definition simplify_quaternary_primitive (dacc : DA.t) (original_prim : P.t)
    (prim : P.quaternary_primitive) (arg1 : Simple.t) (arg1_ty : T.t)
    (arg2 : Simple.t) (arg2_ty : T.t) (arg3 : Simple.t) (arg3_ty : T.t)
    (arg4 : Simple.t) (arg4_ty : T.t) (dbg : Debuginfo.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* original_term := Named.create_prim original_prim dbg in
  (* 102-110: a function of this file with its first arguments is a value
     (no call is made until [simplifier] has all its arguments). *)
  let& simplifier :=
    match prim with
    | P.Atomic_compare_and_set offset_units access_kind mode =>
      simplify_atomic_compare_and_set offset_units access_kind mode
        original_prim
    | P.Atomic_compare_exchange offset_units atomic_kind args_kind mode =>
      simplify_atomic_compare_exchange offset_units atomic_kind args_kind
        mode original_prim
    end
  in
  simplifier dacc original_term dbg arg1 arg1_ty arg2 arg2_ty arg3 arg3_ty
    arg4 arg4_ty result_var.
