(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Stdlib], after its interface
   stdlib/stdlib.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* the type [int32] that OCaml defines before any module *)
Parameter int32 : Type.
Extract Inlined Constant int32 => "int32".
(* the type [int64] that OCaml defines before any module *)
Parameter int64 : Type.
Extract Inlined Constant int64 => "int64".
(* Not_found: in the kit (Port_monad.v). *)
(* NOT DECLARED: <>: an operator, which has no name in Rocq. *)
(* not: in the kit (Port_monad.v). *)
(* NOT DECLARED: &&: an operator, which has no name in Rocq. *)
(* NOT DECLARED: ||: an operator, which has no name in Rocq. *)
