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
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Variable_.
  (* int_ids.mli:110  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Variable.t".
  Module Map.
    (* int_ids.mli:114  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Variable.Map.t".
  End Map.
End Variable_.
Module Symbol.
  (* int_ids.mli:145  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Symbol.t".
  Module Set_.
    (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Int_ids.Symbol.Set.t".
  End Set_.
  Module Map.
    (* int_ids.mli:149  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Symbol.Map.t".
  End Map.
End Symbol.
Module Name.
  (* int_ids.mli:176  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Name.t".
  Module Set_.
    (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Int_ids.Name.Set.t".
  End Set_.
End Name.
Module Simple.
  (* int_ids.mli:200  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Simple.t".
  Module T.
    (* int_ids.mli:204  include Container_types.S_plus_iterator with type t := t *)
    Definition t : Type := Int_ids.Simple.t.
    Extract Inlined Constant t => "Int_ids.Simple.T.t".
  End T.
End Simple.
Module Code_id.
  (* int_ids.mli:247  type t = private Table_by_int_id.Id.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Int_ids.Code_id.t".
  Module Set_.
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter t : Type.
    Extract Inlined Constant t => "Int_ids.Code_id.Set.t".
  End Set_.
  Module Map.
    (* int_ids.mli:251  include Container_types.S with type t := t *)
    Parameter t : Type -> Type.
    Extract Constant t "'a1" => "('a1) Int_ids.Code_id.Map.t".
  End Map.
End Code_id.
