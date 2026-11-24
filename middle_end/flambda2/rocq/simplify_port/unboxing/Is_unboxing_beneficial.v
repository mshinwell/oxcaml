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

(* This file follows
   middle_end/flambda2/simplify/unboxing/is_unboxing_beneficial.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order, the fuel of the recursive function) is that of GUIDE.md.
   No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Apply_cont_rewrite_id List Reg_width_const
  Simple Tag Unboxing_types Value_slot.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 18-19 *)
From SimplifyPort.abbrev.is_unboxing_beneficial Require Import Port_abbreviations.
(*OCAML
module U = Unboxing_types
module Extra_param_and_args = U.Extra_param_and_args
OCAML*)

(* 21-34 *)
Definition is_unboxing_beneficial_for_epa (epa : Extra_param_and_args.t)
    : M bool :=
  Apply_cont_rewrite_id.Map.exists_
    (fun _ (extra_arg : EPA.Extra_arg.t) =>
      match extra_arg with
      | EPA.Extra_arg.Already_in_scope simple =>
        Simple.pattern_match simple
          (fun _ _ => ret true)
          (fun const =>
            let! tmp1 := Reg_width_const.is_poison const in
            match tmp1 with
            | Some _ => ret false
            | None => ret true
            end)
      | EPA.Extra_arg.New_let_binding _ _
      | EPA.Extra_arg.New_let_binding_with_named_args _ _ => ret false
      end)
    epa.(Unboxing_types.Extra_param_and_args.args).

(* 36-98 *)
(* PORT-GAP(type): [U.field_decision] is abstract in decl/: its
   eliminator [U.match_field_decision] stands for the compiler's record
   pattern [{ epa; decision; kind }], and its maker [U.mk_field_decision] for
   the record that the compiler builds. *)
Fixpoint filter_non_beneficial_decisions (fuel : fuel) (decision : U.decision_)
    {struct fuel} : M U.decision_ :=
  recursive! fuel in
  match decision with
  | U.Do_not_unbox _ => ret decision
  (* 39-54 *)
  | U.Unbox (U.Unique_tag_and_size tag shape fields) =>
    let* '(is_unboxing_beneficial, fields) :=
      List.fold_left_map
        (fun (is_unboxing_beneficial : bool)
             (field_decision : U.field_decision) =>
          U.match_field_decision field_decision (fun epa decision kind =>
            let* is_unboxing_beneficial :=
              or_else is_unboxing_beneficial
                (is_unboxing_beneficial_for_epa epa)
            in
            let* decision := filter_non_beneficial_decisions fuel decision in
            ret (is_unboxing_beneficial,
                 U.mk_field_decision epa decision kind)))
        false fields
    in
    if is_unboxing_beneficial
    then ret (U.Unbox (U.Unique_tag_and_size tag shape fields))
    else ret (U.Do_not_unbox U.Not_beneficial)
  (* 55-68 *)
  | U.Unbox (U.Closure_single_entry function_slot vars_within_closure) =>
    let* is_unboxing_beneficial := mk_ref false in
    let* vars_within_closure :=
      Value_slot.Map.map
        (fun (field_decision : U.field_decision) =>
          U.match_field_decision field_decision (fun epa decision kind =>
            (let! tmp1 := get is_unboxing_beneficial in
             let! tmp2 := or_else tmp1 (is_unboxing_beneficial_for_epa epa) in
             set is_unboxing_beneficial tmp2) ;;
            let* decision := filter_non_beneficial_decisions fuel decision in
            ret (U.mk_field_decision epa decision kind)))
        vars_within_closure
    in
    let! tmp1 := get is_unboxing_beneficial in
    if tmp1
    then
      ret (U.Unbox (U.Closure_single_entry function_slot vars_within_closure))
    else ret (U.Do_not_unbox U.Not_beneficial)
  (* 69-87 *)
  | U.Unbox (U.Variant tag const_ctors fields_by_tag) =>
    let* is_unboxing_beneficial := mk_ref false in
    let* fields_by_tag :=
      Tag.Scannable.Map.map
        (fun '(shape, fields) =>
          let! tmp3 :=
            List.map
              (fun (field_decision : U.field_decision) =>
                U.match_field_decision field_decision
                  (fun epa decision kind =>
                    (let! tmp1 := get is_unboxing_beneficial in
                     let! tmp2 :=
                       or_else tmp1 (is_unboxing_beneficial_for_epa epa)
                     in
                     set is_unboxing_beneficial tmp2) ;;
                    let* decision :=
                      filter_non_beneficial_decisions fuel decision
                    in
                    ret (U.mk_field_decision epa decision kind)))
              fields
          in
          ret (shape, tmp3))
        fields_by_tag
    in
    let! tmp1 := get is_unboxing_beneficial in
    if tmp1
    then ret (U.Unbox (U.Variant tag const_ctors fields_by_tag))
    else ret (U.Do_not_unbox U.Not_beneficial)
  (* 88-90 *)
  | U.Unbox (U.Number K.Naked_number_kind.Naked_immediate _) =>
    (* At worst, this unboxing untags an integer *)
    ret decision
  (* 91-98 *)
  | U.Unbox
      (U.Number
         (K.Naked_number_kind.Naked_float | K.Naked_number_kind.Naked_float32
         | K.Naked_number_kind.Naked_int8 | K.Naked_number_kind.Naked_int16
         | K.Naked_number_kind.Naked_int32 | K.Naked_number_kind.Naked_int64
         | K.Naked_number_kind.Naked_nativeint
         | K.Naked_number_kind.Naked_vec128 | K.Naked_number_kind.Naked_vec256
         | K.Naked_number_kind.Naked_vec512 | K.Naked_number_kind.Naked_mask)
         epa) =>
    let! tmp1 := is_unboxing_beneficial_for_epa epa in
    if tmp1 then ret decision else ret (U.Do_not_unbox U.Not_beneficial)
  end.
