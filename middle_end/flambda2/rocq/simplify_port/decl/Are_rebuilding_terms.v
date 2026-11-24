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
   Simplify uses of the compiler's module [Are_rebuilding_terms], after its interface
   middle_end/flambda2/simplify_shared/are_rebuilding_terms.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format.

(* are_rebuilding_terms.mli:21  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Are_rebuilding_terms.t".
(* are_rebuilding_terms.mli:23  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Are_rebuilding_terms.print".
(* are_rebuilding_terms.mli:27  val are_rebuilding : t *)
Parameter are_rebuilding : t.
Extract Inlined Constant are_rebuilding => "Are_rebuilding_terms.are_rebuilding".
(* are_rebuilding_terms.mli:29  val are_not_rebuilding : t *)
Parameter are_not_rebuilding : t.
Extract Inlined Constant are_not_rebuilding => "Are_rebuilding_terms.are_not_rebuilding".
(* are_rebuilding_terms.mli:31  val do_rebuild_terms : t -> bool *)
Parameter do_rebuild_terms : t -> M bool.
Extract Inlined Constant do_rebuild_terms => "Are_rebuilding_terms.do_rebuild_terms".
(* are_rebuilding_terms.mli:33  val do_not_rebuild_terms : t -> bool *)
Parameter do_not_rebuild_terms : t -> M bool.
Extract Inlined Constant do_not_rebuild_terms => "Are_rebuilding_terms.do_not_rebuild_terms".
