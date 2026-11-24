(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*      Pierre Chambart & Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/simplify_nullary_primitive.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Bound_var Debuginfo Name_mode Simple
  Simplify_primitive_result Target_ocaml_int.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda_primitive.nullary_primitive
   Name_mode.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 17-77 *)
Definition simplify_nullary_primitive (dacc : DA.t) (original_prim : P.t)
    (prim : P.nullary_primitive) (dbg : Debuginfo.t)
    (result_var : Bound_var.t) : M Simplify_primitive_result.t :=
  match prim with
  | P.Invalid _result_kind => Simplify_primitive_result.create_invalid dacc
  | P.Optimised_out result_kind =>
    (* 22-27 *)
    (let! tmp1 := Bound_var.name_mode result_var in
     match tmp1 with
     | Name_mode.Phantom => ret tt
     | Name_mode.Normal | Name_mode.In_types =>
       fatal_errorf0
         "The [Optimised_out] primitive should only be used in bindings of phantom variables"
     end) ;;
    let* named := Named.create_prim original_prim dbg in
    let* ty := T.unknown result_kind in
    let* dacc := DA.add_variable dacc result_var ty in
    Simplify_primitive_result.create named false dacc
  | P.Probe_is_enabled _ _ =>
    (* 32-38 *)
    let* named := Named.create_prim original_prim dbg in
    let* ty :=
      let! tmp1 := DA.denv dacc in
      let! tmp2 := DE.machine_width tmp1 in
      T.any_naked_bool tmp2
    in
    let* dacc := DA.add_variable dacc result_var ty in
    Simplify_primitive_result.create named false dacc
  | P.Enter_inlined_apply dbg inlined_attribute =>
    (* 39-50 *)
    let* dacc :=
      DA.map_denv dacc
        (fun denv =>
          DE.merge_inlined_debuginfo_and_forward_inlined_attribute denv dbg
            inlined_attribute)
    in
    let* machine_width :=
      let! tmp1 := DA.denv dacc in
      DE.machine_width tmp1
    in
    let* named :=
      let! tmp1 := Simple.const_unit machine_width in
      Named.create_simple tmp1
    in
    let* ty :=
      let! tmp1 := Target_ocaml_int.zero machine_width in
      T.this_tagged_immediate tmp1
    in
    let* dacc := DA.add_variable dacc result_var ty in
    Simplify_primitive_result.create named false dacc
  | P.Dls_get =>
    (* 51-55 *)
    let* named := Named.create_prim original_prim dbg in
    let& ty := T.any_value in
    let* dacc := DA.add_variable dacc result_var ty in
    Simplify_primitive_result.create named false dacc
  | P.Tls_get =>
    (* 56-60 *)
    let* named := Named.create_prim original_prim dbg in
    let& ty := T.any_value in
    let* dacc := DA.add_variable dacc result_var ty in
    Simplify_primitive_result.create named false dacc
  | P.Domain_index =>
    (* 61-65 *)
    let* named := Named.create_prim original_prim dbg in
    let& ty := T.any_naked_immediate in
    let* dacc := DA.add_variable dacc result_var ty in
    Simplify_primitive_result.create named false dacc
  | P.Poll =>
    (* 66-71 *)
    let* named := Named.create_prim original_prim dbg in
    let* machine_width :=
      let! tmp1 := DA.denv dacc in
      DE.machine_width tmp1
    in
    let* ty :=
      let! tmp1 := Target_ocaml_int.zero machine_width in
      T.this_tagged_immediate tmp1
    in
    let* dacc := DA.add_variable dacc result_var ty in
    Simplify_primitive_result.create named false dacc
  | P.Cpu_relax =>
    (* 72-77 *)
    let* named := Named.create_prim original_prim dbg in
    let* machine_width :=
      let! tmp1 := DA.denv dacc in
      DE.machine_width tmp1
    in
    let* ty :=
      let! tmp1 := Target_ocaml_int.zero machine_width in
      T.this_tagged_immediate tmp1
    in
    let* dacc := DA.add_variable dacc result_var ty in
    Simplify_primitive_result.create named false dacc
  end.
