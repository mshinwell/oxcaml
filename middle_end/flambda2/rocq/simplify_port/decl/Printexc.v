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
   Simplify uses of the compiler's module [Printexc], after its interface
   stdlib/printexc.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/printexc.mli  type raw_backtrace *)
Parameter raw_backtrace : Type.
Extract Inlined Constant raw_backtrace => "Printexc.raw_backtrace".
(* stdlib/printexc.mli  val get_raw_backtrace : unit -> Stdlib__Printexc.raw_backtrace *)
Parameter get_raw_backtrace : unit -> M raw_backtrace.
Extract Inlined Constant get_raw_backtrace => "Printexc.get_raw_backtrace".
(* stdlib/printexc.mli  val raise_with_backtrace : exn -> Stdlib__Printexc.raw_backtrace -> 'a *)
Parameter raise_with_backtrace : forall {A : Type}, exn -> raw_backtrace -> M A.
Extract Inlined Constant raise_with_backtrace => "Printexc.raise_with_backtrace".
