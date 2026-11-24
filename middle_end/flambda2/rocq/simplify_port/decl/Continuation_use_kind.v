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
   Simplify uses of the compiler's module [Continuation_use_kind], after its interface
   middle_end/flambda2/term_basics/continuation_use_kind.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* continuation_use_kind.mli:17  type t = | Inlinable | Non_inlinable of { escaping : bool } *)
Inductive t : Type :=
| Inlinable : t
| Non_inlinable : bool -> t.
Extract Inductive t => "Continuation_use_kind.t" [ "Continuation_use_kind.Inlinable" "(fun x__1 -> (Continuation_use_kind.Non_inlinable { escaping = x__1 } : Continuation_use_kind.t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Continuation_use_kind.t) with Continuation_use_kind.Inlinable -> f__1 () | Continuation_use_kind.Non_inlinable { escaping = x__1 } -> f__2 x__1)".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Continuation_use_kind. End Continuation_use_kind.
