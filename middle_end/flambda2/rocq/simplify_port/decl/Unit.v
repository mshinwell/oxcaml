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
   Simplify uses of the compiler's module [Unit], after its interface
   middle_end/flambda2/term_basics/unit.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* unit.mli:17  type t = unit *)
Definition t : Type := unit.
Extract Inlined Constant t => "Unit.t".
Module T.
  (* unit.mli:19  include Container_types.S with type t := t *)
  Definition t : Type := Unit.t.
  Extract Inlined Constant t => "Unit.T.t".
End T.
(* unit.mli:19  include Container_types.S with type t := t *)
Parameter print : Format.formatter -> Unit.T.t -> M unit.
Extract Inlined Constant print => "Unit.print".
