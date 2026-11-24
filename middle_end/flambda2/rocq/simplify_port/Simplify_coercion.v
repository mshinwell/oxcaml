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

(* This file follows middle_end/flambda2/simplify/simplify_coercion.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Coercion Int_ids Simplify_rec_info_expr.
(* CONSTRUCTORS-WITHOUT-MODULE: Int_ids.Coercion.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17-25 *)
Definition simplify_coercion (dacc : DA.t) (coercion : Coercion.t)
    : M Coercion.t :=
  match coercion with
  | Int_ids.Coercion.Id => ret coercion
  | Int_ids.Coercion.Change_depth from to_ =>
    let* from' := Simplify_rec_info_expr.simplify_rec_info_expr dacc from in
    let* to_' := Simplify_rec_info_expr.simplify_rec_info_expr dacc to_ in
    let! tmp1 := phys_equal from' from in
    let! tmp2 := and_then tmp1 (phys_equal to_' to_) in
    if tmp2 then ret coercion else Coercion.change_depth from' to_'
  end.
