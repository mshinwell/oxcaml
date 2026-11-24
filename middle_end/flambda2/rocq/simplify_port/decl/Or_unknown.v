(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018 OCamlPro SAS                                          *)
(*   Copyright 2018 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Or_unknown], after its interface
   middle_end/flambda2/lattices/or_unknown.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* or_unknown.mli:17  type 'a t = | Known of 'a | Unknown *)
Inductive t (A : Type) : Type :=
| Known : A -> t A
| Unknown : t A.
Arguments Known {A}.
Arguments Unknown {A}.
Extract Inductive t => "Or_unknown.t" [ "Or_unknown.Known" "Or_unknown.Unknown" ].
(* or_unknown.mli:23  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
Extract Inlined Constant print => "Or_unknown.print".
(* or_unknown.mli:31  val map : 'a t -> f:('a -> 'b) -> 'b t *)
Parameter map : forall {A B : Type}, t A -> (A -> M B) -> M (t B).
Extract Inlined Constant map => "Or_unknown.map".
