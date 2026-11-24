(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Code_id], after its interface
   middle_end/flambda2/identifiers/code_id.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Int_ids.

(* int_ids.mli:247  type t = private Table_by_int_id.Id.t *)
Definition t : Type := Int_ids.Code_id.t.
Extract Inlined Constant t => "Code_id.t".
(* module Set = Int_ids.Code_id.Set: declared again here under this name. *)
Module Set_.
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Definition t : Type := Int_ids.Code_id.Set_.t.
  Extract Inlined Constant t => "Code_id.Set.t".
End Set_.
(* module Map = Int_ids.Code_id.Map: declared again here under this name. *)
Module Map.
  (* int_ids.mli:251  include Container_types.S with type t := t *)
  Definition t (A : Type) : Type := Int_ids.Code_id.Map.t A.
  Extract Constant t "'a1" => "('a1) Code_id.Map.t".
End Map.
(* int_ids.mli:267  val name : t -> string *)
Parameter name : t -> M string.
Extract Inlined Constant name => "Code_id.name".
