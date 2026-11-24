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

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Named_rewrite_id], after its interface
   middle_end/flambda2/identifiers/named_rewrite_id.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* named_rewrite_id.mli:17  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Named_rewrite_id.t".
Module Map.
  (* named_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Definition key : Type := Named_rewrite_id.t.
  Extract Inlined Constant key => "Named_rewrite_id.Map.key".
  (* named_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Named_rewrite_id.Map.t".
  (* named_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter empty : forall {A : Type}, t A.
  Extract Inlined Constant empty => "Named_rewrite_id.Map.empty".
  (* named_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter add : forall {A : Type}, key -> A -> t A -> M (t A).
  Extract Inlined Constant add => "Named_rewrite_id.Map.add".
  (* named_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter exists_ : forall {A : Type}, (key -> A -> M bool) -> t A -> M bool.
  Extract Inlined Constant exists_ => "Named_rewrite_id.Map.exists".
  (* named_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter find : forall {A : Type}, key -> t A -> M A.
  Extract Inlined Constant find => "Named_rewrite_id.Map.find".
  (* named_rewrite_id.mli:19  include Container_types.S with type t := t *)
  Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
  Extract Inlined Constant print => "Named_rewrite_id.Map.print".
End Map.
(* named_rewrite_id.mli:21  val create : unit -> t *)
Parameter create : unit -> M t.
Extract Inlined Constant create => "Named_rewrite_id.create".
