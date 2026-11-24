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
   Simplify uses of the compiler's module [Inline_attribute], after its interface
   middle_end/flambda2/terms/inline_attribute.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* inline_attribute.mli:19  type t = | Always_inline | Available_inline | Never_inline | Unroll of int | Default_inline *)
Inductive t : Type :=
| Always_inline : t
| Available_inline : t
| Never_inline : t
| Unroll : int -> t
| Default_inline : t.
Extract Inductive t => "Inline_attribute.t" [ "Inline_attribute.Always_inline" "Inline_attribute.Available_inline" "Inline_attribute.Never_inline" "Inline_attribute.Unroll" "Inline_attribute.Default_inline" ].
