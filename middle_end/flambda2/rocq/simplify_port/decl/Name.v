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
   Simplify uses of the compiler's module [Name], after its interface
   middle_end/flambda2/identifiers/name.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Int_ids.

(* int_ids.mli:176  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Name.t.
Extract Inlined Constant t => "Name.t".
(* module Set = Int_ids.Name.Set: declared again here under this name. *)
Module Set_.
  (* int_ids.mli:178  include Container_types.S_plus_iterator with type t := t *)
  Definition t : Type := Int_ids.Name.Set_.t.
  Extract Inlined Constant t => "Name.Set.t".
End Set_.
