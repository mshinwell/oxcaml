(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Pierre Weis, projet Cristal, INRIA Rocquencourt            *)
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
   Simplify uses of the standard library's module [Format]. Its names and
   types are read from the compiled interface of that module in the
   standard library of the OCaml that built the compiler, not from this
   tree's stdlib/ (PROVENANCE.md, last section): the compiled interface
   that the files of the build import by the MD5 digest
   4340cd28f2a5d224f44cf0b31bbfcddb. The header above is that of this
   tree's file of the same name,
   stdlib/format.mli
   (Git blob f88758fae06a35aa59a35e190d88591118ecb09e). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Stdlib_.

(* stdlib/format.mli  type formatter *)
Parameter formatter : Type.
Extract Inlined Constant formatter => "Format.formatter".
(* stdlib/format.mli  val pp_print_space : Stdlib__Format.formatter -> unit -> unit *)
Parameter pp_print_space : formatter -> unit -> M unit.
Extract Inlined Constant pp_print_space => "Format.pp_print_space".
(* stdlib/format.mli  val formatter_of_out_channel : out_channel -> Stdlib__Format.formatter *)
Parameter formatter_of_out_channel : Stdlib_.out_channel -> M formatter.
Extract Inlined Constant formatter_of_out_channel => "Format.formatter_of_out_channel".
(* stdlib/format.mli  val pp_print_list : ?pp_sep:(Stdlib__Format.formatter -> unit -> unit) -> (Stdlib__Format.formatter -> 'a -> unit) -> Stdlib__Format.formatter -> 'a list -> unit *)
Parameter pp_print_list : forall {A : Type}, option (formatter -> unit -> M unit) -> (formatter -> A -> M unit) -> formatter -> list A -> M unit.
Extract Inlined Constant pp_print_list => "(fun x__1 x__2 x__3 x__4 -> Format.pp_print_list ?pp_sep:x__1 x__2 x__3 x__4)".
(* stdlib/format.mli  val pp_print_option : ?none:(Stdlib__Format.formatter -> unit -> unit) -> (Stdlib__Format.formatter -> 'a -> unit) -> Stdlib__Format.formatter -> 'a option -> unit *)
Parameter pp_print_option : forall {A : Type}, option (formatter -> unit -> M unit) -> (formatter -> A -> M unit) -> formatter -> option A -> M unit.
Extract Inlined Constant pp_print_option => "(fun x__1 x__2 x__3 x__4 -> Format.pp_print_option ?none:x__1 x__2 x__3 x__4)".
(* stdlib/format.mli  val fprintf : Stdlib__Format.formatter -> ('a, Stdlib__Format.formatter, unit) format -> 'a *)
Parameter fprintf0 : formatter -> string -> M unit.
Extract Inlined Constant fprintf0 => "Format.fprintf".
Parameter fprintf1 : forall {A1 : Type}, formatter -> string -> A1 -> M unit.
Extract Inlined Constant fprintf1 => "Format.fprintf".
Parameter fprintf2 : forall {A1 A2 : Type}, formatter -> string -> A1 -> A2 -> M unit.
Extract Inlined Constant fprintf2 => "Format.fprintf".
Parameter fprintf3 : forall {A1 A2 A3 : Type}, formatter -> string -> A1 -> A2 -> A3 -> M unit.
Extract Inlined Constant fprintf3 => "Format.fprintf".
Parameter fprintf4 : forall {A1 A2 A3 A4 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> M unit.
Extract Inlined Constant fprintf4 => "Format.fprintf".
Parameter fprintf5 : forall {A1 A2 A3 A4 A5 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> M unit.
Extract Inlined Constant fprintf5 => "Format.fprintf".
Parameter fprintf6 : forall {A1 A2 A3 A4 A5 A6 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> M unit.
Extract Inlined Constant fprintf6 => "Format.fprintf".
Parameter fprintf7 : forall {A1 A2 A3 A4 A5 A6 A7 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> M unit.
Extract Inlined Constant fprintf7 => "Format.fprintf".
Parameter fprintf8 : forall {A1 A2 A3 A4 A5 A6 A7 A8 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> M unit.
Extract Inlined Constant fprintf8 => "Format.fprintf".
Parameter fprintf9 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> M unit.
Extract Inlined Constant fprintf9 => "Format.fprintf".
Parameter fprintf10 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> M unit.
Extract Inlined Constant fprintf10 => "Format.fprintf".
Parameter fprintf11 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> M unit.
Extract Inlined Constant fprintf11 => "Format.fprintf".
Parameter fprintf12 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> M unit.
Extract Inlined Constant fprintf12 => "Format.fprintf".
Parameter fprintf13 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> M unit.
Extract Inlined Constant fprintf13 => "Format.fprintf".
Parameter fprintf14 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> M unit.
Extract Inlined Constant fprintf14 => "Format.fprintf".
Parameter fprintf15 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> M unit.
Extract Inlined Constant fprintf15 => "Format.fprintf".
Parameter fprintf16 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> M unit.
Extract Inlined Constant fprintf16 => "Format.fprintf".
Parameter fprintf24 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> M unit.
Extract Inlined Constant fprintf24 => "Format.fprintf".
Parameter fprintf33 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 : Type}, formatter -> string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> M unit.
Extract Inlined Constant fprintf33 => "Format.fprintf".
(* stdlib/format.mli  val printf : ('a, Stdlib__Format.formatter, unit) format -> 'a *)
Parameter printf0 : string -> M unit.
Extract Inlined Constant printf0 => "Format.printf".
Parameter printf1 : forall {A1 : Type}, string -> A1 -> M unit.
Extract Inlined Constant printf1 => "Format.printf".
Parameter printf2 : forall {A1 A2 : Type}, string -> A1 -> A2 -> M unit.
Extract Inlined Constant printf2 => "Format.printf".
Parameter printf3 : forall {A1 A2 A3 : Type}, string -> A1 -> A2 -> A3 -> M unit.
Extract Inlined Constant printf3 => "Format.printf".
Parameter printf4 : forall {A1 A2 A3 A4 : Type}, string -> A1 -> A2 -> A3 -> A4 -> M unit.
Extract Inlined Constant printf4 => "Format.printf".
Parameter printf5 : forall {A1 A2 A3 A4 A5 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> M unit.
Extract Inlined Constant printf5 => "Format.printf".
Parameter printf6 : forall {A1 A2 A3 A4 A5 A6 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> M unit.
Extract Inlined Constant printf6 => "Format.printf".
Parameter printf7 : forall {A1 A2 A3 A4 A5 A6 A7 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> M unit.
Extract Inlined Constant printf7 => "Format.printf".
Parameter printf8 : forall {A1 A2 A3 A4 A5 A6 A7 A8 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> M unit.
Extract Inlined Constant printf8 => "Format.printf".
Parameter printf9 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> M unit.
Extract Inlined Constant printf9 => "Format.printf".
Parameter printf10 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> M unit.
Extract Inlined Constant printf10 => "Format.printf".
Parameter printf11 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> M unit.
Extract Inlined Constant printf11 => "Format.printf".
Parameter printf12 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> M unit.
Extract Inlined Constant printf12 => "Format.printf".
Parameter printf13 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> M unit.
Extract Inlined Constant printf13 => "Format.printf".
Parameter printf14 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> M unit.
Extract Inlined Constant printf14 => "Format.printf".
Parameter printf15 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> M unit.
Extract Inlined Constant printf15 => "Format.printf".
Parameter printf16 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> M unit.
Extract Inlined Constant printf16 => "Format.printf".
(* stdlib/format.mli  val eprintf : ('a, Stdlib__Format.formatter, unit) format -> 'a *)
Parameter eprintf0 : string -> M unit.
Extract Inlined Constant eprintf0 => "Format.eprintf".
Parameter eprintf1 : forall {A1 : Type}, string -> A1 -> M unit.
Extract Inlined Constant eprintf1 => "Format.eprintf".
Parameter eprintf2 : forall {A1 A2 : Type}, string -> A1 -> A2 -> M unit.
Extract Inlined Constant eprintf2 => "Format.eprintf".
Parameter eprintf3 : forall {A1 A2 A3 : Type}, string -> A1 -> A2 -> A3 -> M unit.
Extract Inlined Constant eprintf3 => "Format.eprintf".
Parameter eprintf4 : forall {A1 A2 A3 A4 : Type}, string -> A1 -> A2 -> A3 -> A4 -> M unit.
Extract Inlined Constant eprintf4 => "Format.eprintf".
Parameter eprintf5 : forall {A1 A2 A3 A4 A5 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> M unit.
Extract Inlined Constant eprintf5 => "Format.eprintf".
Parameter eprintf6 : forall {A1 A2 A3 A4 A5 A6 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> M unit.
Extract Inlined Constant eprintf6 => "Format.eprintf".
Parameter eprintf7 : forall {A1 A2 A3 A4 A5 A6 A7 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> M unit.
Extract Inlined Constant eprintf7 => "Format.eprintf".
Parameter eprintf8 : forall {A1 A2 A3 A4 A5 A6 A7 A8 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> M unit.
Extract Inlined Constant eprintf8 => "Format.eprintf".
Parameter eprintf9 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> M unit.
Extract Inlined Constant eprintf9 => "Format.eprintf".
Parameter eprintf10 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> M unit.
Extract Inlined Constant eprintf10 => "Format.eprintf".
Parameter eprintf11 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> M unit.
Extract Inlined Constant eprintf11 => "Format.eprintf".
Parameter eprintf12 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> M unit.
Extract Inlined Constant eprintf12 => "Format.eprintf".
Parameter eprintf13 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> M unit.
Extract Inlined Constant eprintf13 => "Format.eprintf".
Parameter eprintf14 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> M unit.
Extract Inlined Constant eprintf14 => "Format.eprintf".
Parameter eprintf15 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> M unit.
Extract Inlined Constant eprintf15 => "Format.eprintf".
Parameter eprintf16 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> M unit.
Extract Inlined Constant eprintf16 => "Format.eprintf".
(* stdlib/format.mli  val asprintf : ('a, Stdlib__Format.formatter, unit, string) format4 -> 'a *)
Parameter asprintf0 : string -> M string.
Extract Inlined Constant asprintf0 => "Format.asprintf".
Parameter asprintf1 : forall {A1 : Type}, string -> A1 -> M string.
Extract Inlined Constant asprintf1 => "Format.asprintf".
Parameter asprintf2 : forall {A1 A2 : Type}, string -> A1 -> A2 -> M string.
Extract Inlined Constant asprintf2 => "Format.asprintf".
Parameter asprintf3 : forall {A1 A2 A3 : Type}, string -> A1 -> A2 -> A3 -> M string.
Extract Inlined Constant asprintf3 => "Format.asprintf".
Parameter asprintf4 : forall {A1 A2 A3 A4 : Type}, string -> A1 -> A2 -> A3 -> A4 -> M string.
Extract Inlined Constant asprintf4 => "Format.asprintf".
Parameter asprintf5 : forall {A1 A2 A3 A4 A5 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> M string.
Extract Inlined Constant asprintf5 => "Format.asprintf".
Parameter asprintf6 : forall {A1 A2 A3 A4 A5 A6 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> M string.
Extract Inlined Constant asprintf6 => "Format.asprintf".
Parameter asprintf7 : forall {A1 A2 A3 A4 A5 A6 A7 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> M string.
Extract Inlined Constant asprintf7 => "Format.asprintf".
Parameter asprintf8 : forall {A1 A2 A3 A4 A5 A6 A7 A8 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> M string.
Extract Inlined Constant asprintf8 => "Format.asprintf".
Parameter asprintf9 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> M string.
Extract Inlined Constant asprintf9 => "Format.asprintf".
Parameter asprintf10 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> M string.
Extract Inlined Constant asprintf10 => "Format.asprintf".
Parameter asprintf11 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> M string.
Extract Inlined Constant asprintf11 => "Format.asprintf".
Parameter asprintf12 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> M string.
Extract Inlined Constant asprintf12 => "Format.asprintf".
Parameter asprintf13 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> M string.
Extract Inlined Constant asprintf13 => "Format.asprintf".
Parameter asprintf14 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> M string.
Extract Inlined Constant asprintf14 => "Format.asprintf".
Parameter asprintf15 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> M string.
Extract Inlined Constant asprintf15 => "Format.asprintf".
Parameter asprintf16 : forall {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 : Type}, string -> A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> M string.
Extract Inlined Constant asprintf16 => "Format.asprintf".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Format. End Format.
