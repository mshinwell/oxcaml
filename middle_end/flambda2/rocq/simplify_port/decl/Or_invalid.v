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
   Simplify uses of the compiler's module [Or_invalid], after its interface
   middle_end/flambda2/term_basics/or_invalid.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* or_invalid.mli:19  type 'a t = | Ok of 'a | Invalid *)
Inductive t (A : Type) : Type :=
| Ok : A -> t A
| Invalid : t A.
Arguments Ok {A}.
Arguments Invalid {A}.
(* or_invalid.mli:23  val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit *)
Parameter print : forall {A : Type}, (Format.formatter -> A -> M unit) -> Format.formatter -> t A -> M unit.
Extract Inlined Constant print => "Or_invalid.print".
(* or_invalid.mli:25  val map : 'a t -> f:('a -> 'b) -> 'b t *)
Parameter map : forall {A B : Type}, t A -> (A -> M B) -> M (t B).
Extract Inlined Constant map => "Or_invalid.map".
