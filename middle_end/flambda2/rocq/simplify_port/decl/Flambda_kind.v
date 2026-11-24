(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017--2019 OCamlPro SAS                                    *)
(*   Copyright 2017--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Flambda_kind], after its interface
   middle_end/flambda2/kinds/flambda_kind.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* flambda_kind.mli:43  type t = private | Value ( ** OCaml values, either immediates or pointers. * ) | Naked_number of Naked_number_kind.t ( ** The kind of unboxed numbers and untagged immediates. * ) | Region ( ** Values which have been introduced by Flambda and are never accessible at the source language level (for example sets of closures). * ) | Rec_info *)
Parameter t : Type.
Extract Inlined Constant t => "Flambda_kind.t".
Module Scannable_block_shape.
  (* flambda_kind.mli:135  type t = | Value_only | Mixed_record of Mixed_block_shape.t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Flambda_kind.Scannable_block_shape.t".
End Scannable_block_shape.
Module With_subkind.
  (* flambda_kind.mli:212  type full_kind *)
  Parameter full_kind : Type.
  Extract Inlined Constant full_kind => "Flambda_kind.With_subkind.full_kind".
  (* flambda_kind.mli:265  type t = full_kind *)
  Definition t : Type := full_kind.
  Extract Inlined Constant t => "Flambda_kind.With_subkind.t".
  (* flambda_kind.mli:282  val any_value : t *)
  Parameter any_value : t.
  Extract Inlined Constant any_value => "Flambda_kind.With_subkind.any_value".
End With_subkind.
