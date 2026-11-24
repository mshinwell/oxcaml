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
   Simplify uses of the compiler's module [Continuation], after its interface
   middle_end/flambda2/identifiers/continuation.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* continuation.mli:19  type t = private Table_by_int_id.Id.t *)
Parameter t : Type.
Extract Inlined Constant t => "Continuation.t".
Module T.
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Definition t : Type := Continuation.t.
  Extract Inlined Constant t => "Continuation.T.t".
End T.
(* continuation.mli:23  include Container_types.S with type t := t *)
Parameter equal : Continuation.T.t -> Continuation.T.t -> M bool.
Extract Inlined Constant equal => "Continuation.equal".
(* continuation.mli:23  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Continuation.T.t -> M unit.
Extract Inlined Constant print => "Continuation.print".
Module Set_.
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Continuation.Set.t".
End Set_.
Module Map.
  (* continuation.mli:23  include Container_types.S with type t := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Continuation.Map.t".
End Map.
Module Lmap.
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter t : Type -> Type.
  Extract Constant t "'a1" => "('a1) Continuation.Lmap.t".
  (* continuation.mli:25  module Lmap : Lmap.S with type key := t *)
  Parameter singleton : forall {A : Type}, Continuation.t -> A -> M (t A).
  Extract Inlined Constant singleton => "Continuation.Lmap.singleton".
End Lmap.
Module Sort.
  (* continuation.mli:28  type t = | Normal_or_exn | Return | Define_root_symbol | Toplevel_return *)
  Parameter t : Type.
  Extract Inlined Constant t => "Continuation.Sort.t".
End Sort.
(* continuation.mli:39  val create : ?sort:Sort.t -> ?name:string -> unit -> t *)
Parameter create : option Continuation.Sort.t -> option string -> unit -> M t.
Extract Inlined Constant create => "(fun x__1 x__2 x__3 -> Continuation.create ?sort:x__1 ?name:x__2 x__3)".
