(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Copyright 2023 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)
(** Annotation on function call that represents a probe. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Probe], after its interface
   middle_end/flambda2/terms/probe.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* probe.mli:14  type desc = private { name : string; enabled_at_init : bool } *)
Parameter desc : Type.
Extract Inlined Constant desc => "Probe.desc".
(* probe.mli:19  type t = desc option *)
Definition t : Type := option desc.
Extract Inlined Constant t => "Probe.t".
