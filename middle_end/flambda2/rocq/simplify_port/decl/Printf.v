(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Xavier Leroy and Pierre Weis, projet Cristal, INRIA Rocquencourt     *)
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
   Simplify uses of the compiler's module [Printf], after its interface
   stdlib/printf.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* stdlib/printf.mli  val sprintf : ('a, unit, string) format -> 'a *)
Parameter sprintf0 : string -> M string.
Extract Inlined Constant sprintf0 => "Printf.sprintf".
Parameter sprintf1 : forall {A1 : Type}, string -> A1 -> M string.
Extract Inlined Constant sprintf1 => "Printf.sprintf".
Parameter sprintf2 : forall {A1 A2 : Type}, string -> A1 -> A2 -> M string.
Extract Inlined Constant sprintf2 => "Printf.sprintf".
Parameter sprintf3 : forall {A1 A2 A3 : Type}, string -> A1 -> A2 -> A3 -> M string.
Extract Inlined Constant sprintf3 => "Printf.sprintf".
Parameter sprintf4 : forall {A1 A2 A3 A4 : Type}, string -> A1 -> A2 -> A3 -> A4 -> M string.
Extract Inlined Constant sprintf4 => "Printf.sprintf".
Parameter sprintf5 : forall {A1 A2 A3 A4 A5 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> M string.
Extract Inlined Constant sprintf5 => "Printf.sprintf".
Parameter sprintf6 : forall {A1 A2 A3 A4 A5 A6 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> M string.
Extract Inlined Constant sprintf6 => "Printf.sprintf".
Parameter sprintf7 : forall {A1 A2 A3 A4 A5 A6 A7 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> M string.
Extract Inlined Constant sprintf7 => "Printf.sprintf".
Parameter sprintf8 : forall {A1 A2 A3 A4 A5 A6 A7 A8 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> M string.
Extract Inlined Constant sprintf8 => "Printf.sprintf".
Parameter sprintf9 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> M string.
Extract Inlined Constant sprintf9 => "Printf.sprintf".
Parameter sprintf10 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> M string.
Extract Inlined Constant sprintf10 => "Printf.sprintf".
Parameter sprintf11 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> M string.
Extract Inlined Constant sprintf11 => "Printf.sprintf".
Parameter sprintf12 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> M string.
Extract Inlined Constant sprintf12 => "Printf.sprintf".
Parameter sprintf13 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> M string.
Extract Inlined Constant sprintf13 => "Printf.sprintf".
Parameter sprintf14 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> M string.
Extract Inlined Constant sprintf14 => "Printf.sprintf".
Parameter sprintf15 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> M string.
Extract Inlined Constant sprintf15 => "Printf.sprintf".
Parameter sprintf16 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> M string.
Extract Inlined Constant sprintf16 => "Printf.sprintf".
